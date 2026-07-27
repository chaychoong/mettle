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
    TemporalTrace, TranslateError,
};
use als_instance::{write_instance_xml, XmlRequest, XmlSolution};
use als_sterling::{
    Button, ClickRefused, ProviderMeta, ServeSession, SessionDatum, CLICK_NEXT, TEMPORAL_CLICKS,
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

/// A temporal command's solved artifacts. No enumerator borrows these (trace
/// enumeration is mt-076), so the session simply owns them.
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

/// A temporal command's session: one lasso, no enumeration yet (mt-076).
pub(super) struct TemporalSession<'a> {
    generator: String,
    shown: Shown<'a>,
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
    fn show_trace(
        &self,
        artifacts: &TemporalArtifacts,
        id: String,
        trace: &TemporalTrace,
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
                solution: XmlSolution::Trace { trace },
            },
        )?;
        // Cloned rather than moved out of the trace: the trace itself stays
        // alive as the thing the XML above describes.
        let eval_artifacts = (*trace.artifacts).clone();
        let evaluator = ReplContext::new(
            self.session,
            self.graph,
            self.graph.root,
            SolvedCommand {
                ir: artifacts.ir.clone(),
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

    fn click(&mut self, on_click: &str) -> Result<(), ClickRefused> {
        if TEMPORAL_CLICKS.contains(&on_click) {
            return Err(temporal_defer(on_click, "this command is not temporal"));
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
        artifacts: &TemporalArtifacts,
        trace: &TemporalTrace,
    ) -> Result<Self, TranslateError> {
        let context = ViewContext::new(session, graph, inputs);
        print_solved(inputs, &artifacts.ir, &Solved::Trace(trace));
        let shown = context.show_trace(artifacts, datum_id(0), trace)?;
        Ok(TemporalSession {
            generator: inputs.header.to_owned(),
            shown,
        })
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
            // No buttons at all until mt-076: a "Next Trace" that produced the
            // same trace, or a wrong one, is worse than no button (ADR-0016
            // Decision 2).
            buttons: Vec::new(),
        }
    }

    fn eval(&mut self, datum_id: &str, expression: &str) -> String {
        match stale(datum_id, &self.shown.id) {
            Some(message) => message,
            // `:state N` moves where this evaluates, exactly as at the REPL
            // prompt — the protocol carries no state of its own.
            None => repl::eval_line(&mut self.shown.evaluator, expression),
        }
    }

    fn click(&mut self, on_click: &str) -> Result<(), ClickRefused> {
        if TEMPORAL_CLICKS.contains(&on_click) {
            return Err(temporal_defer(
                on_click,
                "trace enumeration is not implemented",
            ));
        }
        if on_click == CLICK_NEXT {
            return Err(temporal_defer(
                on_click,
                "`next` enumerates instances of a static command, and this command is temporal",
            ));
        }
        Err(ClickRefused::unknown(on_click))
    }
}

fn provider_meta(generator: &str) -> ProviderMeta {
    ProviderMeta {
        name: "mettle".to_owned(),
        evaluator: true,
        // The two views mt-075 builds. `script` (a D3 scripting pane) and
        // `edit` are upstream affordances mettle does not offer, and claiming
        // them would show a client an empty tab.
        views: vec!["graph".to_owned(), "table".to_owned()],
        generators: vec![generator.to_owned()],
    }
}

/// The refusal for a verb that is real but not implemented yet, always naming
/// the bead that retires it.
fn temporal_defer(on_click: &str, because: &str) -> ClickRefused {
    ClickRefused {
        code: "not-yet-supported",
        message: format!(
            "`{on_click}` is not available yet: {because}. Temporal trace \
             enumeration (New Trace / New Config / New Init / New Fork) arrives \
             in mt-076; until then this session shows the one solved trace."
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
