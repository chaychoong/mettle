//! The post-solve **evaluator REPL** (mt-062) — `mettle exec --repl` /
//! `--eval <EXPR>`.
//!
//! Implemented from the pinned contract in
//! `docs/reference/alloy6-evaluator.md`, which traced what the reference
//! analyzer's evaluator console actually does. Three facts from it shape
//! everything here:
//!
//! 1. **One grammar slot** (§0 step 8, §5). Input is wrapped as a `run` body
//!    and parsed through the ordinary pred-body grammar
//!    ([`als_syntax::parse_fragment`]). Formulas, comprehensions, `let`,
//!    quantifiers, arithmetic and bare relational expressions all fall out of
//!    that one path — and a declaration or a command typed at the prompt is
//!    rejected as an ordinary parse error, with no bespoke check (E-15/E-16).
//! 2. **Atom and skolem names are globals** (§0 step 6). `A$0` and `$foo_x` are
//!    not special syntax: they resolve because the evaluator registers every
//!    atom/skolem name as a name bound to its value. mettle ports that *shape*
//!    directly against its live, in-process instance — not the reference's
//!    XML-serialize-then-reparse plumbing, which exists only because its
//!    evaluator panel is decoupled from the solver (§5).
//! 3. **Rendering is by sort** (§3): a formula prints `true`/`false`, a
//!    genuinely `int`-typed expression (`#e`, `sum`) prints a bare numeral, and
//!    everything relational prints `{tuple, …}`. `plus[3,4]` is `Int`-*set*-typed
//!    and therefore prints `{7}`, not `7` — a real Alloy typing rule, not a quirk.
//!
//! **Tuple order is mettle's live solve order** (deterministic `TupleSet`
//! order), not the reference GUI console's XML-round-trip order. The two differ
//! for `univ`/`Int`; the sets are equal, and the contract itself recommends not
//! replicating the round-trip. Pinned as LEDGER-012, disclosed in LIMITATIONS.
//!
//! **Overflow in eval position always wraps silently** (§2/§7): `noOverflow` is
//! a no-op there, so evaluation runs with `allow_overflow` on regardless of how
//! the command was solved. That also keeps the forbid-mode polarity guard —
//! which exists to make the *solver's* accept-set exact — out of an ad hoc
//! expression's truth value.
//!
//! Rendering and the input loop live here because this is the CLI crate (STYLE
//! E3); parsing, resolution, lowering and evaluation are one call each into
//! `als-syntax`/`als-types`/`als-core`.

use std::fmt::Write as _;
use std::io::{self, BufRead as _, Write as _};

use als_core::bounds::{AtomId, Bounds, RelBound, Tuple, TupleSet, Universe};
use als_core::ir::{Ir, RelExpr, RelExprId, RelExprKind, RelId, Relation};
use als_core::{
    lower_fragment, BoundsResult, Evaluator, FragmentInput, Instance, LoweredFragment, LoweredGoal,
    ScopedUniverse, SolveOptions, TranslateError,
};
use als_syntax::ast::{Ast, ExprKind};
use als_syntax::{parse_fragment, ArenaId as _, FileId, FragmentError, Span, FRAGMENT_OFFSET};
use als_types::{ModuleGraph, ModuleId, ResolveError, ResolvedSession, SigId, Type};

/// The display path fragment diagnostics are rendered against.
const REPL_PATH: &str = "<repl>";

/// The prompt, exactly as the reference console's (contract §0).
const PROMPT: &str = "> ";

/// What one evaluated fragment produced — the three shapes the reference's
/// evaluator distinguishes (contract §3), before any rendering.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum ReplValue {
    /// A formula's truth value.
    Formula(bool),
    /// A genuinely `int`-typed expression's value, already wrapped to the
    /// command's bitwidth.
    Int(i64),
    /// A relational value over the command's universe.
    Rel(TupleSet),
}

/// Why one fragment did not evaluate. Each variant is a typed error from the
/// phase that raised it (STYLE E1/E4); rendering to text is [`render_error`]'s
/// job alone.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum ReplError {
    /// The input did not parse as one Alloy expression.
    Parse(FragmentError),
    /// The input parsed but did not type-check.
    Resolve(ResolveError),
    /// The input named a string literal the solved command never referenced, so
    /// no atom in this universe denotes it (contract §3, E-49). An
    /// *eval-state* error — about the instance, not the input's syntax or
    /// types — so it carries the reference's own wording.
    UnknownStringLiteral {
        /// The literal's content, without quotes.
        literal: String,
        /// Where it was written, in the fragment's coordinate space.
        span: Span,
    },
    /// The input type-checked but could not be lowered or evaluated.
    Translate(TranslateError),
}

/// One solved command, prepared for evaluation against its instance.
///
/// Owns everything the solve produced that evaluation needs (`Ir`, universe,
/// bounds, instance) and borrows the resolution session and module graph the
/// whole `exec` run holds. Constructing it registers the instance's atom and
/// skolem names as globals — the port of contract §0 step 6.
pub(crate) struct ReplContext<'a> {
    session: &'a ResolvedSession<'a>,
    graph: &'a ModuleGraph,
    /// The module a fragment resolves as — the root, whose names a user typing
    /// at the prompt expects to see.
    module: ModuleId,
    ir: Ir,
    bounds: BoundsResult,
    scoped: ScopedUniverse,
    instance: Instance,
    /// Base bounds + the command's skolem bounds + one exact bound per
    /// registered atom global, i.e. a bound for every relation the evaluator
    /// can now reach.
    eval_bounds: Bounds,
    int_sig: Option<RelId>,
    seq_int_sig: Option<RelId>,
    /// Evaluation options: the command's, but with overflow forced to wrap
    /// (contract §2 — `noOverflow` is a no-op in eval position).
    eval_opts: SolveOptions,
    /// A file id no loaded file owns, so a fragment's spans are distinguishable
    /// from any module's.
    fragment_file: FileId,
    /// Atom/skolem globals as the resolver needs them (name → type).
    global_types: Vec<(String, Type)>,
    /// The same globals as the lowerer needs them (name → lowered value).
    global_values: Vec<(String, RelExprId)>,
}

impl<'a> ReplContext<'a> {
    /// Prepares evaluation against one solved command's instance.
    pub(crate) fn new(
        session: &'a ResolvedSession<'a>,
        graph: &'a ModuleGraph,
        module: ModuleId,
        solved: SolvedCommand,
    ) -> Self {
        let SolvedCommand {
            mut ir,
            bounds,
            scoped,
            goal,
            instance,
            opts,
        } = solved;

        let fragment_file = FileId::from_index(graph.files.len());
        let mut eval_bounds = bounds.bounds.clone();
        for (rel, bound) in &goal.skolem_bounds {
            eval_bounds.bind(*rel, bound.clone());
        }

        let globals = register_globals(
            &mut ir,
            &mut eval_bounds,
            &scoped,
            &goal,
            &instance.universe,
            session.world().builtins.univ,
            Span::new(fragment_file, 0, 0),
        );
        let instance = Instance::from_relations(
            instance.universe.clone(),
            instance
                .iter()
                .map(|(rel, ts)| (rel, ts.clone()))
                .chain(globals.relations),
        );

        ReplContext {
            session,
            graph,
            module,
            ir,
            bounds,
            scoped,
            instance,
            eval_bounds,
            int_sig: goal.int_sig,
            seq_int_sig: goal.seq_int_sig,
            eval_opts: SolveOptions {
                allow_overflow: true,
                ..opts
            },
            fragment_file,
            global_types: globals.types,
            global_values: globals.values,
        }
    }

    /// The universe results render against.
    pub(crate) fn universe(&self) -> &Universe {
        &self.instance.universe
    }
}

/// The solved instance's names, in the two shapes resolution and lowering each
/// need them (contract §0 step 6).
struct Globals {
    /// Name → type, for the resolver's lexical environment.
    types: Vec<(String, Type)>,
    /// Name → already-lowered value, for the lowerer's binder stack.
    values: Vec<(String, RelExprId)>,
    /// The fresh singleton relations minted for atom names, to be added to the
    /// instance so the evaluator can read their values back.
    relations: Vec<(RelId, TupleSet)>,
}

/// Registers every sig atom of the universe, and every skolem the solve minted,
/// as a name bound to its value — the port of contract §0 step 6.
///
/// **Only sig atoms** get a name. The reference registers every atom, but an
/// integer atom is named `-3` and a string atom `"hi"`: neither lexes as an
/// identifier, so neither was ever reachable *as a name* — they are reached as
/// arithmetic and as string literals instead, exactly as in the reference.
///
/// An atom name becomes a fresh, exactly-bound singleton relation, which is all
/// "a name bound to one atom" is; a skolem's relation already exists, is already
/// bounded, and is already decoded, so only the name binding is new.
fn register_globals(
    ir: &mut Ir,
    eval_bounds: &mut Bounds,
    scoped: &ScopedUniverse,
    goal: &LoweredGoal,
    universe: &Universe,
    univ: SigId,
    span: Span,
) -> Globals {
    let mut globals = Globals {
        types: Vec::new(),
        values: Vec::new(),
        relations: Vec::new(),
    };

    for scoped_sig in scoped.scopes.iter() {
        let Some(minted) = scoped_sig.minted else {
            continue;
        };
        for k in 0..minted.count as usize {
            let atom = AtomId::from_index(minted.first.index() + k);
            let name = universe.name(atom).to_owned();
            let mut value = TupleSet::empty(1);
            value.insert(Tuple::new(vec![atom]));
            let rel = ir.relations.alloc(Relation {
                name: name.clone(),
                arity: 1,
                span,
            });
            let expr = ir.rel_exprs.alloc(RelExpr {
                kind: RelExprKind::Relation(rel),
                span,
            });
            eval_bounds.bind(rel, RelBound::new(value.clone(), value.clone()));
            globals.relations.push((rel, value));
            // The minting sig is the atom's static type: a sig mints only atoms
            // its own subtree does not already supply, so an atom's minting sig
            // always contains it (a non-minting subsig may narrow it further,
            // which only ever makes this an over-approximation, never a wrong
            // one).
            globals
                .types
                .push((name.clone(), Type::unary(scoped_sig.sig)));
            globals.values.push((name, expr));
        }
    }

    for (rel, bound) in &goal.skolem_bounds {
        let name = ir.relations[*rel].name.clone();
        let arity = bound.upper().arity();
        let expr = ir.rel_exprs.alloc(RelExpr {
            kind: RelExprKind::Relation(*rel),
            span,
        });
        // Typed as a product of `univ`: a skolem relation does not carry its
        // decl's type, and `univ` intersects everything, so this never rejects a
        // use the reference accepts.
        globals
            .types
            .push((name.clone(), Type::product_of(vec![univ; arity])));
        globals.values.push((name, expr));
    }

    globals
}

/// The artifacts one solved command hands the REPL — everything
/// `compute_universe` → `compute_bounds` → `lower_command` → `solve_goal`
/// produced, kept alive instead of dropped.
pub(crate) struct SolvedCommand {
    pub(crate) ir: Ir,
    pub(crate) bounds: BoundsResult,
    pub(crate) scoped: ScopedUniverse,
    pub(crate) goal: LoweredGoal,
    pub(crate) instance: Instance,
    pub(crate) opts: SolveOptions,
}

/// Evaluates one line of evaluator input against the solved instance: parse
/// (one grammar slot) → resolve (with the instance's names in scope) → lower
/// (into the command's own `Ir`) → evaluate.
///
/// Render-agnostic by design — [`render_value`]/[`render_error`] turn the
/// result into text, and both the interactive loop and `--eval` are thin
/// drivers over this one function.
///
/// # Errors
/// A [`ReplError`] from whichever phase rejected the input.
pub(crate) fn eval_input(ctx: &mut ReplContext<'_>, input: &str) -> Result<ReplValue, ReplError> {
    let fragment = parse_fragment(input, ctx.fragment_file).map_err(ReplError::Parse)?;
    let resolved = ctx
        .session
        .resolve_fragment(ctx.module, &fragment.ast, fragment.expr, &ctx.global_types)
        .map_err(ReplError::Resolve)?;
    // Warnings never change a value (resolution-doc §0/§5.3) and a prompt is
    // not a place to lecture about an unused variable; they are dropped.
    let _ = &resolved.warnings;
    check_string_literals(ctx, &fragment.ast)?;

    // Disjoint field borrows: lowering needs `&mut ir` while reading the
    // world/bounds, so the pieces are named individually rather than through
    // `&self` methods.
    let lowered = lower_fragment(
        ctx.session.world(),
        ctx.graph,
        &ctx.bounds,
        &mut ctx.ir,
        &FragmentInput {
            module: ctx.module,
            ast: &fragment.ast,
            choices: &resolved.choices,
            expr: fragment.expr,
            bitwidth: ctx.scoped.bitwidth,
            globals: &ctx.global_values,
        },
    )
    .map_err(ReplError::Translate)?;

    let mut evaluator = Evaluator::new(
        &ctx.ir,
        &ctx.instance,
        &ctx.scoped,
        &ctx.eval_opts,
        ctx.int_sig,
        ctx.seq_int_sig,
        &ctx.eval_bounds,
    );
    match lowered {
        LoweredFragment::Formula(f) => evaluator.eval_formula(f).map(ReplValue::Formula),
        // The overflow flag is deliberately dropped: in eval position the
        // reference wraps silently and shows no marker, in every overflow shape
        // probed (contract §2/§7, E-31/E-32/E-33).
        LoweredFragment::Int(i) => evaluator
            .eval_int(i)
            .map(|(v, _overflow)| ReplValue::Int(v)),
        LoweredFragment::Rel(r) => evaluator.eval_rel(r).map(ReplValue::Rel),
    }
    .map_err(ReplError::Translate)
}

/// Rejects any string literal in the fragment that this command's universe has
/// no atom for (contract §3, E-49).
///
/// The reference's evaluator hits this the same way: its instance holds exactly
/// the literals the solved command referenced, so a freshly-typed one denotes
/// nothing. Checked here, over the fragment's own arena, rather than left to
/// the lowerer — the lowerer's miss is an internal-invariant failure for every
/// *other* caller, and this is a user error with its own wording.
fn check_string_literals(ctx: &ReplContext<'_>, fragment: &Ast) -> Result<(), ReplError> {
    for (_, expr) in fragment.exprs.iter() {
        let ExprKind::Str(literal) = &expr.kind else {
            continue;
        };
        if !ctx.scoped.string_literals.contains_key(literal) {
            return Err(ReplError::UnknownStringLiteral {
                literal: literal.clone(),
                span: expr.span,
            });
        }
    }
    Ok(())
}

/// Renders a value exactly as the reference's evaluator does (contract §3):
/// `true`/`false`, a bare numeral, or `{a->b, …}` with `{}` for the empty set.
/// Atom names come from the universe, so a string atom carries its own quotes.
pub(crate) fn render_value(value: &ReplValue, universe: &Universe) -> String {
    match value {
        ReplValue::Formula(b) => b.to_string(),
        ReplValue::Int(n) => n.to_string(),
        ReplValue::Rel(tuples) => {
            let mut out = String::from("{");
            for (i, tuple) in tuples.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                for (j, atom) in tuple.atoms().iter().enumerate() {
                    if j > 0 {
                        out.push_str("->");
                    }
                    out.push_str(universe.name(*atom));
                }
            }
            out.push('}');
            out
        }
    }
}

/// Renders an error against the user's own input as a caret-and-label block
/// (STYLE E3/G3), or as a one-liner when no span points into that input.
///
/// The reference's parser error text is deliberately **not** mimicked (its
/// 38-token list is an artifact of its generated parser); mettle's own
/// diagnostics say the same thing better. The two messages that *are* taken
/// verbatim are the ones that state an evaluator rule rather than a syntax
/// fact: the higher-order rejection here, and the no-instance message in
/// [`crate::exec`].
pub(crate) fn render_error(err: &ReplError, input: &str, fragment_file: FileId) -> String {
    let (span, message) = match err {
        ReplError::Parse(FragmentError::Parse(e)) => (Some(e.span()), e.to_string()),
        ReplError::Parse(e @ FragmentError::NotAnExpression) => (None, e.to_string()),
        ReplError::Resolve(e) => (Some(e.span()), e.to_string()),
        ReplError::UnknownStringLiteral { literal, span } => (
            Some(*span),
            format!("String literal \"{literal}\" does not exist in this instance."),
        ),
        ReplError::Translate(TranslateError::HigherOrder { .. }) => (
            None,
            "Higher-order quantification is not allowed in the evaluator.".to_owned(),
        ),
        ReplError::Translate(e) => (Some(e.span()), e.to_string()),
    };
    match span.and_then(|s| fragment_span(s, input, fragment_file)) {
        Some(span) => crate::diagnostics::render(input, REPL_PATH, span, &message),
        None => crate::diagnostics::render_spanless("error", Some(REPL_PATH), &message),
    }
}

/// Translates a span in the wrapped source [`parse_fragment`] parses back into
/// the user's raw input, or `None` when it points somewhere else entirely — an
/// inlined pred body in a real module, say, which has no caret to draw here.
/// The file check is what tells the two apart: the fragment's id belongs to no
/// loaded file.
fn fragment_span(span: Span, input: &str, fragment_file: FileId) -> Option<Span> {
    if span.file != fragment_file {
        return None;
    }
    let len = u32::try_from(input.len()).ok()?;
    let start = span.start.checked_sub(FRAGMENT_OFFSET)?;
    let end = span.end.checked_sub(FRAGMENT_OFFSET)?;
    (end <= len).then(|| Span::new(span.file, start, end))
}

/// Evaluates each `--eval <EXPR>` in order, appending one result line each.
/// Returns whether any of them failed (errors go to stderr, so a piped stdout
/// stays exactly the result lines).
pub(crate) fn eval_each(ctx: &mut ReplContext<'_>, exprs: &[&str], out: &mut String) -> bool {
    let mut failed = false;
    for expr in exprs {
        match eval_input(ctx, expr) {
            Ok(value) => {
                let _ = writeln!(out, "{}", render_value(&value, ctx.universe()));
            }
            Err(err) => {
                eprint!("{}", render_error(&err, expr, ctx.fragment_file));
                failed = true;
            }
        }
    }
    failed
}

/// The interactive loop: prompt, read a line, print one result line, repeat.
///
/// Hand-rolled on purpose — a line reader is the whole requirement, and no
/// readline dependency is justified by it (STYLE P1). Blank input reprompts
/// silently (the reference's console never even calls the evaluator for it);
/// `:q` or EOF exits. History and editing are deliberately absent.
///
/// # Errors
/// An [`io::Error`] only from stdin/stdout themselves.
pub(crate) fn run_loop(ctx: &mut ReplContext<'_>) -> io::Result<()> {
    let stdin = io::stdin();
    let mut line = String::new();
    loop {
        {
            let mut out = io::stdout().lock();
            out.write_all(PROMPT.as_bytes())?;
            out.flush()?;
        }
        line.clear();
        if stdin.lock().read_line(&mut line)? == 0 {
            // EOF: end the line the prompt left open, then leave.
            println!();
            return Ok(());
        }
        let input = line.trim();
        if input.is_empty() {
            continue;
        }
        if input == ":q" {
            return Ok(());
        }
        match eval_input(ctx, input) {
            Ok(value) => println!("{}", render_value(&value, ctx.universe())),
            Err(err) => print!("{}", render_error(&err, input, ctx.fragment_file)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn universe() -> Universe {
        Universe::new(vec![
            "A$0".to_owned(),
            "B$0".to_owned(),
            "-1".to_owned(),
            "\"hi\"".to_owned(),
        ])
    }

    fn atom(i: usize) -> AtomId {
        AtomId::from_index(i)
    }

    #[test]
    fn renders_the_three_shapes() {
        let u = universe();
        assert_eq!(render_value(&ReplValue::Formula(true), &u), "true");
        assert_eq!(render_value(&ReplValue::Formula(false), &u), "false");
        assert_eq!(render_value(&ReplValue::Int(-2), &u), "-2");
        assert_eq!(render_value(&ReplValue::Rel(TupleSet::empty(1)), &u), "{}");
    }

    #[test]
    fn renders_tuples_with_arrows_and_atom_names() {
        let u = universe();
        let mut unary = TupleSet::empty(1);
        unary.insert(Tuple::new(vec![atom(0)]));
        unary.insert(Tuple::new(vec![atom(3)]));
        assert_eq!(
            render_value(&ReplValue::Rel(unary), &u),
            "{A$0, \"hi\"}",
            "string atoms carry their own quotes (contract §3)"
        );

        let mut binary = TupleSet::empty(2);
        binary.insert(Tuple::new(vec![atom(1), atom(0)]));
        binary.insert(Tuple::new(vec![atom(1), atom(2)]));
        assert_eq!(
            render_value(&ReplValue::Rel(binary), &u),
            "{B$0->A$0, B$0->-1}"
        );
    }

    #[test]
    fn fragment_spans_map_back_onto_the_users_input() {
        let file = FileId::from_index(7);
        let input = "some A";
        // `run {\n` is 6 bytes, so the input's first byte is at 6.
        let mapped = fragment_span(Span::new(file, 6, 10), input, file).expect("in range");
        assert_eq!((mapped.start, mapped.end), (0, 4));
        // A span before the input (inside the wrapper) has no caret here.
        assert_eq!(fragment_span(Span::new(file, 0, 4), input, file), None);
        // Nor does one past its end (the wrapper's closing brace).
        assert_eq!(fragment_span(Span::new(file, 13, 14), input, file), None);
        // Nor does a span in a real module — an inlined pred body's, say.
        let other = FileId::from_index(0);
        assert_eq!(fragment_span(Span::new(other, 6, 10), input, file), None);
    }
}
