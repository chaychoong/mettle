//! The two [`ServeSession`] implementations behind `mettle serve` (mt-072):
//! the solved command, and every question the four protocol verbs can ask of
//! it.
//!
//! Split from [`super`] because the two responsibilities are genuinely
//! separate — that module is the *subcommand* (arguments, pipeline, listener,
//! console output), this one is the *session* (what is true of the solved
//! instance, and what advancing means). Everything about the wire is in
//! `als_sterling`; nothing here knows a socket exists.
//!
//! The lifetime discipline and the under-pinned protocol corners this file
//! settles (temporal eval posture, stale `datumId`) are documented in
//! [`super`]'s module docs, which is where a reader arrives first.

use std::fmt::Write as _;

use als_core::ir::Ir;
use als_core::{
    BoundsResult, Instance, InstanceEnumerator, LoweredGoal, ScopedUniverse, SolveOptions,
    TemporalTrace, TraceAdvance, TraceEnumerator, TraceStep, TranslateError,
};
use als_instance::{write_instance_xml, XmlRequest, XmlSolution};
use als_sterling::{
    Button, ClickRefused, ProviderMeta, ServeSession, SessionDatum, CLICK_NEW_FORK, CLICK_NEW_INIT,
    CLICK_NEXT, CLICK_NEXT_CONFIG, CLICK_NEXT_TRACE, TEMPORAL_CLICKS,
};
use als_syntax::ast::CmdKind;
use als_types::{ModuleGraph, ResolvedSession, ResolvedWorld};

use super::SolveInputs;
use crate::exec;
use crate::repl::{self, ReplContext, SolvedCommand, SolvedTrace};

/// A static command's solved artifacts, pinned for the enumerator's lifetime.
pub(super) struct StaticArtifacts {
    pub(super) ir: Ir,
    pub(super) scoped: ScopedUniverse,
    pub(super) bounds: BoundsResult,
    pub(super) goal: LoweredGoal,
    pub(super) opts: SolveOptions,
}

/// A temporal command's solved artifacts, pinned for the trace enumerator's
/// lifetime (mt-076 — the enumerator borrows `scoped`/`bounds` for as long as
/// it lives, exactly as the static enumerator borrows [`StaticArtifacts`]).
pub(super) struct TemporalArtifacts {
    pub(super) ir: Ir,
    pub(super) scoped: ScopedUniverse,
    pub(super) bounds: BoundsResult,
    pub(super) opts: SolveOptions,
}

/// What the client is currently looking at: one datum's identity, its XML, and
/// an evaluator pointed at exactly that instance.
struct Shown<'a> {
    id: String,
    xml: String,
    evaluator: ReplContext<'a>,
}

/// A static command's session: the instance on screen, and an enumerator
/// holding the solver state that produces the next one.
pub(super) struct StaticSession<'a> {
    generator: String,
    artifacts: &'a StaticArtifacts,
    context: ViewContext<'a>,
    enumerator: InstanceEnumerator<'a>,
    shown: Shown<'a>,
    /// How many datum ids have been minted. Monotone rather than "the index of
    /// the instance on screen": an advance that finds an instance but fails to
    /// render it still burns an id, and two different instances must never
    /// share one.
    minted: usize,
    /// Set once the enumerator has reported the space empty. The `Next` button
    /// disappears at that point rather than inviting a click that cannot work.
    exhausted: bool,
}

/// A temporal command's session: the trace on screen, and the enumerator that
/// answers the reference GUI's four exploration buttons (mt-076).
pub(super) struct TemporalSession<'a> {
    generator: String,
    artifacts: &'a TemporalArtifacts,
    context: ViewContext<'a>,
    enumerator: TraceEnumerator<'a>,
    shown: Shown<'a>,
    /// How many datum ids have been minted (see [`StaticSession::minted`]).
    minted: usize,
    /// Set once **path** enumeration has run out. Only "Next Trace" retires:
    /// the other three verbs ask different questions of the same length and can
    /// still answer (a fork is a fresh restricted search, and a new
    /// configuration restarts the sweep).
    paths_exhausted: bool,
    /// Set once the enumerator reports its effort budget spent. Every button
    /// goes at that point — nothing further is reachable, and the space was
    /// never shown empty, so "no more" would be a lie.
    budget_spent: bool,
}

/// The borrowed inputs both views need to render an instance.
#[derive(Clone, Copy)]
struct ViewContext<'a> {
    session: &'a ResolvedSession<'a>,
    graph: &'a ModuleGraph,
    world: &'a ResolvedWorld,
    command: usize,
    filename: &'a str,
}

impl<'a> ViewContext<'a> {
    pub(super) fn new(
        session: &'a ResolvedSession<'a>,
        graph: &'a ModuleGraph,
        inputs: &SolveInputs<'a>,
    ) -> Self {
        ViewContext {
            session,
            graph,
            world: inputs.world,
            command: inputs.idx,
            filename: inputs.filename,
        }
    }

    /// Renders a static instance and builds the evaluator for it.
    ///
    /// Both consumers get their own clone of the solved `Ir`: each appends to
    /// it (macro bodies, lowered fragments) and neither should see the other's
    /// nodes — nor should the pristine arena the enumerator is reading grow
    /// underneath it.
    fn show_instance(
        &self,
        artifacts: &StaticArtifacts,
        id: String,
        instance: Instance,
    ) -> Result<Shown<'a>, TranslateError> {
        let mut ir = artifacts.ir.clone();
        let xml = write_instance_xml(
            &mut ir,
            &XmlRequest {
                world: self.world,
                graph: self.graph,
                scoped: &artifacts.scoped,
                bounds: &artifacts.bounds,
                command: self.command,
                filename: self.filename,
                opts: artifacts.opts,
                solution: XmlSolution::Static {
                    instance: &instance,
                    goal: &artifacts.goal,
                },
            },
        )?;
        let evaluator = ReplContext::new(
            self.session,
            self.graph,
            self.graph.root,
            SolvedCommand {
                ir: artifacts.ir.clone(),
                bounds: artifacts.bounds.clone(),
                scoped: artifacts.scoped.clone(),
                goal: artifacts.goal.clone(),
                instance,
                opts: artifacts.opts,
                trace: None,
            },
        );
        Ok(Shown { id, xml, evaluator })
    }

    /// The temporal twin: the whole lasso as one document, and an evaluator
    /// sitting at state 0 of it.
    ///
    /// `ir` is the **enumerator's** arena, not the session's: a trace
    /// references the per-state copies and skolems its own trace length
    /// allocated, and none of those exist in the pre-solve arena
    /// [`TemporalArtifacts`] holds (see [`TraceEnumerator::ir`]).
    fn show_trace(
        &self,
        artifacts: &TemporalArtifacts,
        ir: &Ir,
        id: String,
        trace: &TemporalTrace,
    ) -> Result<Shown<'a>, TranslateError> {
        let mut ir = ir.clone();
        let xml = write_instance_xml(
            &mut ir,
            &XmlRequest {
                world: self.world,
                graph: self.graph,
                scoped: &artifacts.scoped,
                bounds: &artifacts.bounds,
                command: self.command,
                filename: self.filename,
                opts: artifacts.opts,
                solution: XmlSolution::Trace { trace },
            },
        )?;
        // The XML writer appended to its own copy; the evaluator gets a fresh
        // one from the same base so neither sees the other's nodes.
        // Cloned rather than moved out of the trace: the trace itself stays
        // alive as the thing the XML above describes.
        let eval_artifacts = (*trace.artifacts).clone();
        let evaluator = ReplContext::new(
            self.session,
            self.graph,
            self.graph.root,
            SolvedCommand {
                ir,
                bounds: artifacts.bounds.clone(),
                scoped: artifacts.scoped.clone(),
                goal: eval_artifacts.goal,
                instance: eval_artifacts.instance,
                opts: artifacts.opts,
                trace: Some(SolvedTrace {
                    unrolled: eval_artifacts.unrolled,
                    loop_state: trace.loop_state,
                    state: 0,
                }),
            },
        );
        Ok(Shown { id, xml, evaluator })
    }
}

/// The datum id for the `n`th instance of a session. Changing on every advance
/// is the contract the client's stale-datum check relies on.
fn datum_id(index: usize) -> String {
    format!("mettle:{index}")
}

impl<'a> StaticSession<'a> {
    pub(super) fn new(
        session: &'a ResolvedSession<'a>,
        graph: &'a ModuleGraph,
        inputs: &SolveInputs<'a>,
        artifacts: &'a StaticArtifacts,
        enumerator: InstanceEnumerator<'a>,
        instance: Instance,
    ) -> Result<Self, TranslateError> {
        let context = ViewContext::new(session, graph, inputs);
        // Printed from the raw solved instance, before the evaluator's atom
        // globals are registered into a copy of it — `exec`'s rendering of this
        // command and `serve`'s must be the same text.
        print_solved(inputs, &artifacts.ir, &Solved::Instance(&instance));
        let shown = context.show_instance(artifacts, datum_id(0), instance)?;
        Ok(StaticSession {
            generator: inputs.header.to_owned(),
            artifacts,
            context,
            enumerator,
            shown,
            minted: 0,
            exhausted: false,
        })
    }
}

/// What was solved, for the one-time console summary.
enum Solved<'a> {
    Instance(&'a Instance),
    Trace(&'a TemporalTrace),
}

/// Prints the verdict block `exec` would print for this command, so that
/// `serve` and `exec` agree about what was found before the browser is even
/// opened.
///
/// `expect` is deliberately not checked here: an `expect` mismatch is a verdict
/// gauge's business, and `serve` is an exploration tool with no exit code to
/// fail.
fn print_solved(inputs: &SolveInputs<'_>, ir: &Ir, solved: &Solved<'_>) {
    let label = match inputs.cmd.kind {
        CmdKind::Run => "SAT",
        CmdKind::Check => "COUNTEREXAMPLE",
    };
    let mut out = String::new();
    let _ = writeln!(out, "{}", inputs.header);
    let _ = writeln!(out, "{label}");
    match solved {
        Solved::Instance(instance) => out.push_str(&exec::render_instance(ir, instance)),
        Solved::Trace(trace) => out.push_str(&exec::render_trace(ir, trace)),
    }
    out.push('\n');
    // A failure to write the summary must not take the server down; the URL
    // line below is what actually matters, and it reports its own failure.
    let _ = crate::write_stdout(out);
}

impl ServeSession for StaticSession<'_> {
    fn meta(&self) -> ProviderMeta {
        provider_meta(&self.generator)
    }

    fn datum(&self) -> SessionDatum {
        SessionDatum {
            id: self.shown.id.clone(),
            generator_name: self.generator.clone(),
            xml: self.shown.xml.clone(),
            buttons: if self.exhausted {
                Vec::new()
            } else {
                vec![Button {
                    text: "Next".to_owned(),
                    on_click: CLICK_NEXT.to_owned(),
                    mouseover: Some("(Get the next instance)".to_owned()),
                }]
            },
        }
    }

    fn eval(&mut self, datum_id: &str, expression: &str) -> String {
        match stale(datum_id, &self.shown.id) {
            Some(message) => message,
            None => repl::eval_line(&mut self.shown.evaluator, expression),
        }
    }

    /// `state` is ignored: a static command's instance is a single state, so
    /// there is no position for a client to be looking at.
    fn click(&mut self, on_click: &str, _state: Option<usize>) -> Result<(), ClickRefused> {
        if TEMPORAL_CLICKS.contains(&on_click) {
            return Err(temporal_defer(on_click));
        }
        if on_click != CLICK_NEXT {
            return Err(ClickRefused::unknown(on_click));
        }
        if self.exhausted {
            return Err(exhausted());
        }
        let Some(instance) = self.enumerator.next() else {
            self.exhausted = true;
            // An enumerator that ran out of *budget* rather than out of
            // instances is a different sentence: the count it stopped at is a
            // lower bound, and saying "that was the last one" would be false.
            return Err(if self.enumerator.exhausted() {
                ClickRefused {
                    code: "enumeration-budget",
                    message: "the enumeration budget ran out, so there may be further \
                              instances this session cannot reach."
                        .to_owned(),
                }
            } else {
                exhausted()
            });
        };
        self.minted += 1;
        let shown = self
            .context
            .show_instance(self.artifacts, datum_id(self.minted), instance)
            .map_err(|e| ClickRefused {
                code: "export-failed",
                // The instance is already consumed from the enumerator, and
                // saying so is what keeps the sequence honest.
                message: format!(
                    "the next instance was found but could not be rendered as XML ({e}); \
                     it has been skipped."
                ),
            })?;
        self.shown = shown;
        Ok(())
    }
}

impl<'a> TemporalSession<'a> {
    pub(super) fn new(
        session: &'a ResolvedSession<'a>,
        graph: &'a ModuleGraph,
        inputs: &SolveInputs<'a>,
        artifacts: &'a TemporalArtifacts,
        enumerator: TraceEnumerator<'a>,
        trace: &TemporalTrace,
    ) -> Result<Self, TranslateError> {
        let context = ViewContext::new(session, graph, inputs);
        print_solved(inputs, enumerator.ir(), &Solved::Trace(trace));
        let shown = context.show_trace(artifacts, enumerator.ir(), datum_id(0), trace)?;
        Ok(TemporalSession {
            generator: inputs.header.to_owned(),
            artifacts,
            context,
            enumerator,
            shown,
            minted: 0,
            paths_exhausted: false,
            budget_spent: false,
        })
    }

    /// The state "New Fork" forks *after* — the reference GUI's `current`
    /// field, which sends `fork(current + 1)`.
    ///
    /// Two sources, in this order (ADR-0016 Decision 2 amendment (d), mt-075):
    ///
    /// 1. **The client's own displayed state**, when the `click` payload
    ///    carries one. mettle's frontend steps through a lasso client-side —
    ///    the whole trace arrives in one datum — so its stepper is the only
    ///    thing that knows where the user is looking, and the pinned payload
    ///    (verb string only) could not say.
    /// 2. **The evaluator pane's state**, otherwise. That is not a fallback so
    ///    much as the reference's own arrangement — `VizGUI` and `OurConsole`
    ///    share one `current` index (alloy6-temporal.md §(h)), so "where the
    ///    evaluator is pointed" *is* "what the user is looking at" in Alloy
    ///    too — and it is what a client that does not send the field (an
    ///    external Sterling) keeps getting, moved with `:state N`.
    ///
    /// # Errors
    /// A [`ClickRefused`] if the client names a state this trace does not
    /// have: an index outside the displayed lasso is a client bug, and forking
    /// at a guessed state would answer a question nobody asked.
    fn fork_state(&self, requested: Option<usize>) -> Result<usize, ClickRefused> {
        let Some(state) = requested else {
            return Ok(self.evaluator_state());
        };
        let k = self.trace_length();
        if state >= k {
            return Err(ClickRefused {
                code: "state-out-of-range",
                message: format!(
                    "state {state} is outside the trace on screen, which has {k} states."
                ),
            });
        }
        Ok(state)
    }

    /// Where the evaluator pane is pointed — the `None` half of
    /// [`fork_state`](Self::fork_state), and what the button set reads.
    fn evaluator_state(&self) -> usize {
        self.shown.evaluator.trace_state().unwrap_or(0)
    }

    /// The number of states in the trace on screen.
    fn trace_length(&self) -> usize {
        self.enumerator
            .current()
            .map_or(0, als_core::TemporalTrace::k)
    }

    /// Runs one enumerator step and, if it produced a trace, puts it on screen.
    fn take(&mut self, step: TraceStep, verb: &str) -> Result<(), ClickRefused> {
        let advance = self.enumerator.advance(step).map_err(|e| ClickRefused {
            code: "export-failed",
            message: format!("`{verb}` could not be answered: {e}."),
        })?;
        let trace = match advance {
            TraceAdvance::Trace(trace) => trace,
            TraceAdvance::Exhausted => {
                if matches!(step, TraceStep::NextPath) {
                    self.paths_exhausted = true;
                }
                return Err(exhausted_verb(verb, step));
            }
            // The reference re-displays the byte-identical original here, which
            // is indistinguishable from doing nothing; saying so is more use
            // than silently redrawing the same picture.
            TraceAdvance::SameConfig => {
                return Err(ClickRefused {
                    code: "no-more-instances",
                    message: "this model has no static (non-`var`) relations left free, so \
                              there is only one configuration to show."
                        .to_owned(),
                })
            }
            TraceAdvance::BudgetExhausted => {
                self.budget_spent = true;
                return Err(ClickRefused {
                    code: "enumeration-budget",
                    message: "the enumeration budget ran out, so there may be further traces \
                              this session cannot reach."
                        .to_owned(),
                });
            }
            TraceAdvance::PrimaryVarCap { k, primaries } => {
                return Err(ClickRefused {
                    code: "enumeration-budget",
                    message: format!(
                        "trace length {k} needs {primaries} primary variables, past this \
                         session's cap; the search stopped short of it."
                    ),
                })
            }
        };
        self.minted += 1;
        let shown = self
            .context
            .show_trace(
                self.artifacts,
                self.enumerator.ir(),
                datum_id(self.minted),
                &trace,
            )
            .map_err(|e| ClickRefused {
                code: "export-failed",
                message: format!(
                    "the next trace was found but could not be rendered as XML ({e}); \
                     it has been skipped."
                ),
            })?;
        self.shown = shown;
        Ok(())
    }
}

impl ServeSession for TemporalSession<'_> {
    fn meta(&self) -> ProviderMeta {
        provider_meta(&self.generator)
    }

    fn datum(&self) -> SessionDatum {
        SessionDatum {
            id: self.shown.id.clone(),
            generator_name: self.generator.clone(),
            xml: self.shown.xml.clone(),
            buttons: self.buttons(),
        }
    }

    fn eval(&mut self, datum_id: &str, expression: &str) -> String {
        match stale(datum_id, &self.shown.id) {
            Some(message) => message,
            // `:state N` moves where this evaluates, exactly as at the REPL
            // prompt — and, for a client that sends no state of its own, also
            // moves what "New Fork" forks after (see `fork_state`).
            None => repl::eval_line(&mut self.shown.evaluator, expression),
        }
    }

    fn click(&mut self, on_click: &str, state: Option<usize>) -> Result<(), ClickRefused> {
        if self.budget_spent {
            return Err(ClickRefused {
                code: "enumeration-budget",
                message: "the enumeration budget for this session is spent; no further trace \
                          is reachable."
                    .to_owned(),
            });
        }
        match on_click {
            // The reference's "New" and "New Trace" are the *same* operator —
            // `fork(-3)` and `fork(-2)` produce byte-identical sequences (probe
            // P-076-3) — so mettle answers both, rather than pretending to a
            // distinction the jar does not have.
            CLICK_NEXT | CLICK_NEXT_TRACE => {
                if self.paths_exhausted {
                    return Err(exhausted_verb(on_click, TraceStep::NextPath));
                }
                self.take(TraceStep::NextPath, on_click)
            }
            CLICK_NEXT_CONFIG => self.take(TraceStep::NextConfig, on_click),
            CLICK_NEW_INIT => self.take(TraceStep::Fork { hold: 0 }, on_click),
            CLICK_NEW_FORK => {
                let hold = self.fork_state(state)? + 1;
                self.take(TraceStep::Fork { hold }, on_click)
            }
            _ => Err(ClickRefused::unknown(on_click)),
        }
    }
}

impl TemporalSession<'_> {
    /// The buttons this session offers, following mt-072's rule: a button is
    /// present only while it can still do something.
    ///
    /// "New Fork" is additionally hidden at the last state, where
    /// `current + 1 == k` and the answer is always exhaustion (probe P-076-6) —
    /// the same "absent, never wrong" discipline, one state finer. The state
    /// read here is the *evaluator's*, the only one the server knows: a client
    /// that steps through the trace itself (mt-075's frontend) owns the same
    /// rule against its own displayed state, and says so where it applies it.
    fn buttons(&self) -> Vec<Button> {
        if self.budget_spent {
            return Vec::new();
        }
        let k = self.trace_length();
        let mut buttons = Vec::new();
        if !self.paths_exhausted {
            buttons.push(button(
                "New Trace",
                CLICK_NEXT_TRACE,
                "(Show a new trace, same configuration)",
            ));
        }
        buttons.push(button(
            "New Config",
            CLICK_NEXT_CONFIG,
            "(Show a new configuration)",
        ));
        buttons.push(button(
            "New Init",
            CLICK_NEW_INIT,
            "(Show a new initial state)",
        ));
        if self.evaluator_state() + 1 < k {
            buttons.push(button(
                "New Fork",
                CLICK_NEW_FORK,
                "(Fork the trace after the state you are on)",
            ));
        }
        buttons
    }
}

fn button(text: &str, on_click: &str, mouseover: &str) -> Button {
    Button {
        text: text.to_owned(),
        on_click: on_click.to_owned(),
        mouseover: Some(mouseover.to_owned()),
    }
}

/// The "nothing further down this road" refusal, worded per verb so a client
/// can tell "this trace has no other configuration" from "this command has no
/// other trace at all".
fn exhausted_verb(verb: &str, step: TraceStep) -> ClickRefused {
    let what = match step {
        TraceStep::NextPath => {
            "there are no further traces of this configuration within the command's scopes"
        }
        TraceStep::NextConfig => "this command has no other configuration within its scopes",
        TraceStep::Fork { hold: 0 } => "this command has no other initial state",
        TraceStep::Fork { .. } => "this trace cannot fork after the state you are on",
    };
    ClickRefused {
        code: "no-more-instances",
        message: format!("`{verb}`: {what}."),
    }
}

fn provider_meta(generator: &str) -> ProviderMeta {
    ProviderMeta {
        name: "mettle".to_owned(),
        evaluator: true,
        // The two views mt-075 built, both real as of its graph slice.
        // `script` (a D3 scripting pane) and `edit` are upstream affordances
        // mettle does not offer, and claiming them would show a client an
        // empty tab.
        views: vec!["graph".to_owned(), "table".to_owned()],
        generators: vec![generator.to_owned()],
    }
}

/// The refusal a **static** session gives a temporal verb: the verb is real and
/// implemented (mt-076), it simply has no meaning for this command.
fn temporal_defer(on_click: &str) -> ClickRefused {
    ClickRefused {
        code: "unknown-click",
        message: format!(
            "`{on_click}` explores a lasso trace (New Trace / New Config / \
             New Init / New Fork), and this command is not temporal — it has \
             instances, not traces. Use `next`."
        ),
    }
}

fn exhausted() -> ClickRefused {
    ClickRefused {
        code: "no-more-instances",
        message: "there are no further instances of this command within its scopes.".to_owned(),
    }
}

/// The stale-`datumId` guard: `None` to answer, `Some(message)` to refuse.
///
/// An empty id is what a client sends before it has any datum, and is read as
/// "the current one".
fn stale(requested: &str, current: &str) -> Option<String> {
    if requested.is_empty() || requested == current {
        return None;
    }
    Some(format!(
        "This evaluator is pointed at `{current}`, not `{requested}` — that instance has been \
         superseded. Re-request the current instance and ask again."
    ))
}
