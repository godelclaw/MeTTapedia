import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchGraph

/-!
# Emitted entries over the shared search algebra

All four emitted entry bodies use the same selected search descriptor.
Their execution theorem takes the existing five-operation realization;
search state and receipt encodings remain opaque to the emitter.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner (Search Machine)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Eval WireKit
open CompleteExecution (patternValue)
open CompleteExecution.SearchRunner (Realization)

private abbrev a (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name

@[simp] private theorem backend_closed (spec : Spec) (profile : SearchProfile spec) (caller : Subst) :
    applySubst caller (backendAtom spec profile) = backendAtom spec profile := by
  cases profile <;> simp [backendAtom, CompleteExecution.classSearchBackend, applySubst]

section Realized

variable {Run Receipt : Type} {search : Search Pattern Run Receipt} {spec : Spec}
    (profile : SearchProfile spec) (realization : Realization search)
    (backendEq : realization.backend = backendAtom spec profile)
    (planEq : realization.plan = planAtom spec) (standardEq : realization.standard = standardAtom spec)

include backendEq planEq standardEq

private theorem realized_begin_call (caller : Subst) (state : Effects.State) (source start : Pattern)
    (ready : realization.SourceReady start)
    (prepared : PureReturns runtime [] state
      (a "gslt:runner:standard" [realization.standard, patternValue source]) state (patternValue start))
    (captured : applySubst caller (v "source") = patternValue source) :
    PureReturns runtime caller state
      (a "gslt:runner:begin" [backendAtom spec profile, planAtom spec, standardAtom spec, v "source"])
      state (encoded (realization.machineTerm (Machine.begin search start))) := by
  apply PureData.raw_capture_returns runtime [] caller state state "gslt:runner:begin"
    [backendAtom spec profile, planAtom spec, standardAtom spec, patternValue source]
    [backendAtom spec profile, planAtom spec, standardAtom spec, v "source"] _ (by decide +kernel)
    (runtime_raw "gslt:runner:begin" 4 (by decide +kernel)) (by decide)
  · simp [captured, planAtom, standardAtom]
  · simpa only [backendEq, planEq, standardEq] using
      CompleteExecution.SearchRunner.begin_returns realization state source start ready prepared

/-- The common emitted begin entry works for every certified realization. -/
theorem begin_entry_of_realization {name : String} (fresh : namesFresh spec name profile = true)
    (state : Effects.State) (source start : Pattern) (ready : realization.SourceReady start)
    (prepared : PureReturns runtime [] state
      (a "gslt:runner:standard" [realization.standard, patternValue source]) state (patternValue start)) :
    PureReturns (emittedRuntime spec name profile) [] state
      (a (beginHead name) [patternValue source]) state
      (encoded (realization.machineTerm (Machine.begin search start))) := by
  obtain ⟨special, io, known⟩ := entry_facts fresh (head := beginHead name) (by simp [entries])
  let callee : Subst := [("source", patternValue source)]
  apply PureData.raw_authored_call_return (emittedRuntime spec name profile) [] callee state state (beginHead name)
    [patternValue source] (beginBody spec profile) _ special io known
  · simp [emittedRuntime, SpaceSemantics.Program.append, program, beginEquation]
  · simpa using entry_raw (spec := spec) (name := name) (profile := profile)
      (beginHead name) 1 known (by simp [program])
  · rw [closed_arguments]
    exact PureData.named_equation_clause (emittedRuntime spec name profile) (beginHead name)
      (beginEquation spec name profile) ["source"] [patternValue source]
      (entry_row fresh (beginEquation spec name profile) (by simp [program])) rfl (by decide) rfl
  · exact transport fresh (fresh_parts fresh).2.2.2.2.2.1
      (realized_begin_call profile realization backendEq planEq standardEq callee state source start ready prepared
        (by simp [callee, applySubst, Subst.lookup]))

private theorem realized_run_body (state : Effects.State) (source start : Pattern)
    (ready : realization.SourceReady start)
    (prepared : PureReturns runtime [] state
      (a "gslt:runner:standard" [realization.standard, patternValue source]) state (patternValue start))
    (ticks quantum : Nat) :
    PureReturns runtime [("quantum", number quantum), ("ticks", number ticks), ("source", patternValue source)]
      state (runBody spec profile) state
      (encoded (CompleteExecution.SearchWire.traceTerm
        (Machine.advance search ticks quantum (Machine.begin search start)))) := by
  let begun := Machine.begin search start
  let paged := Machine.advance search ticks quantum begun
  let caller : Subst := [("quantum", number quantum), ("ticks", number ticks), ("source", patternValue source)]
  let withMachine := ("machine", encoded (realization.machineTerm begun)) :: caller
  let withPaged := ("paged", encoded (realization.machineTerm paged)) :: withMachine
  have searchReady : CompleteExecution.SearchRunner.Ready realization begun := realization.run_ready start ready 0
  unfold runBody
  apply let_returns runtime caller withMachine state state state (v "machine") _ _
    (encoded (realization.machineTerm begun)) _
    (realized_begin_call profile realization backendEq planEq standardEq caller state source start ready prepared
      (by simp [caller, applySubst, Subst.lookup]))
  · simp [withMachine, caller, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
  · apply let_returns runtime withMachine withPaged state state state (v "paged") _ _
      (encoded (realization.machineTerm paged))
    · apply PureData.raw_capture_returns runtime [] withMachine state state "gslt:runner:advance"
        [backendAtom spec profile, planAtom spec, standardAtom spec, number ticks, number quantum,
          encoded (realization.machineTerm begun)]
        [backendAtom spec profile, planAtom spec, standardAtom spec, v "ticks", v "quantum", v "machine"] _
        (by decide +kernel) (runtime_raw "gslt:runner:advance" 6 (by decide +kernel)) (by decide)
      · simp [withMachine, caller, planAtom, standardAtom, applySubst, Subst.lookup]
      · simpa only [backendEq, planEq, standardEq] using
          CompleteExecution.SearchRunner.advance_returns realization state quantum ticks begun searchReady
    · simp [withPaged, withMachine, caller, SpaceSemantics.matchBinding, SpaceSemantics.matchValue,
        matchAtom, Subst.lookup]
    · apply PureData.raw_capture_returns runtime [] withPaged state state "gslt:runner:trace"
        [encoded (realization.machineTerm paged)] [v "paged"] _ (by decide +kernel)
        (runtime_raw "gslt:runner:trace" 1 (by decide +kernel)) (by decide)
      · simp [withPaged, withMachine, caller, applySubst, Subst.lookup]
      · exact CompleteExecution.SearchRunner.trace_returns realization state paged

/-- The common emitted run entry retains the selected realization. -/
theorem run_entry_of_realization {name : String} (fresh : namesFresh spec name profile = true)
    (state : Effects.State) (source start : Pattern) (ready : realization.SourceReady start)
    (prepared : PureReturns runtime [] state
      (a "gslt:runner:standard" [realization.standard, patternValue source]) state (patternValue start))
    (ticks quantum : Nat) :
    PureReturns (emittedRuntime spec name profile) [] state
      (a (runHead name) [patternValue source, number ticks, number quantum]) state
      (encoded (CompleteExecution.SearchWire.traceTerm
        (Machine.advance search ticks quantum (Machine.begin search start)))) := by
  obtain ⟨special, io, known⟩ := entry_facts fresh (head := runHead name) (by simp [entries])
  apply PureData.raw_authored_call_return (emittedRuntime spec name profile) []
    [("quantum", number quantum), ("ticks", number ticks), ("source", patternValue source)]
    state state (runHead name) [patternValue source, number ticks, number quantum] (runBody spec profile) _
    special io known
  · simp [emittedRuntime, SpaceSemantics.Program.append, program, runEquation]
  · simpa using entry_raw (spec := spec) (name := name) (profile := profile)
      (runHead name) 3 known (by simp [program])
  · rw [closed_arguments]
    exact PureData.named_equation_clause (emittedRuntime spec name profile) (runHead name)
      (runEquation spec name profile) ["source", "ticks", "quantum"]
      [patternValue source, number ticks, number quantum]
      (entry_row fresh (runEquation spec name profile) (by simp [program])) rfl (by decide) rfl
  · exact transport fresh (fresh_parts fresh).2.2.2.2.2.2.1
      (realized_run_body profile realization backendEq planEq standardEq state source start ready prepared ticks quantum)

omit backendEq planEq standardEq in
private theorem realized_rounds_ready (work : Nat) (explorer)
    (ready : CompleteExecution.SearchExplore.Ready realization explorer) :
    CompleteExecution.SearchExplore.Ready realization
      (Complete.Settled.roundsUntilSettled search work explorer) := by
  induction work generalizing explorer with
  | zero => exact ready
  | succ work ih =>
    simp only [Complete.Settled.roundsUntilSettled]
    split
    · exact ready
    · exact ih _ (CompleteExecution.SearchExplore.step_ready realization explorer ready)

omit backendEq planEq standardEq in
private theorem realized_begin_explorer_ready (start : Pattern) (ready : realization.SourceReady start) :
    CompleteExecution.SearchExplore.Ready realization (Complete.Explore.begin search start) := by
  intro node member
  simp only [Complete.Explore.begin, List.mem_singleton] at member
  subst member
  exact realization.run_ready start ready 0

omit backendEq planEq standardEq in
private abbrev realizedFinal (start : Pattern) (work : Nat) :=
  Complete.Settled.roundsUntilSettled search work (Complete.Explore.begin search start)

private theorem realized_exploration_body (state : Effects.State) (source start : Pattern)
    (ready : realization.SourceReady start)
    (prepared : PureReturns runtime [] state
      (a "gslt:runner:standard" [realization.standard, patternValue source]) state (patternValue start))
    (work : Nat) (read answer : Atom)
    (readBack : PureReturns runtime
      [("explored", encoded (CompleteExecution.SearchExplore.explorerTerm realization (realizedFinal (search := search) start work))),
       ("explorer", encoded (CompleteExecution.SearchExplore.explorerTerm realization (Complete.Explore.begin search start))),
       ("work", number work), ("source", patternValue source)] state read state answer) :
    PureReturns runtime [("work", number work), ("source", patternValue source)] state
      (a "let" [v "explorer", a "gslt:explore:begin"
        [backendAtom spec profile, planAtom spec, standardAtom spec, v "source"],
        a "let" [v "explored", a "gslt:explore:rounds"
          [backendAtom spec profile, planAtom spec, standardAtom spec, v "work", v "explorer"], read]])
      state answer := by
  let caller : Subst := [("work", number work), ("source", patternValue source)]
  let startExplorer := Complete.Explore.begin search start
  let withExplorer := ("explorer", encoded (CompleteExecution.SearchExplore.explorerTerm realization startExplorer)) :: caller
  let final := realizedFinal (search := search) start work
  let withExplored := ("explored", encoded (CompleteExecution.SearchExplore.explorerTerm realization final)) :: withExplorer
  apply let_returns runtime caller withExplorer state state state (v "explorer") _ _
    (encoded (CompleteExecution.SearchExplore.explorerTerm realization startExplorer))
  · apply PureData.raw_capture_returns runtime [] caller state state "gslt:explore:begin"
      [backendAtom spec profile, planAtom spec, standardAtom spec, patternValue source]
      [backendAtom spec profile, planAtom spec, standardAtom spec, v "source"] _ (by decide +kernel)
      (runtime_raw "gslt:explore:begin" 4 (by decide +kernel)) (by decide)
    · simp [caller, planAtom, standardAtom, applySubst, Subst.lookup]
    · simpa only [backendEq, planEq, standardEq] using
        CompleteExecution.SearchExplore.begin_returns realization state source start ready prepared
  · simp [withExplorer, caller, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
  · apply let_returns runtime withExplorer withExplored state state state (v "explored") _ _
      (encoded (CompleteExecution.SearchExplore.explorerTerm realization final))
    · apply PureData.raw_capture_returns runtime [] withExplorer state state "gslt:explore:rounds"
        [backendAtom spec profile, planAtom spec, standardAtom spec, number work,
          encoded (CompleteExecution.SearchExplore.explorerTerm realization startExplorer)]
        [backendAtom spec profile, planAtom spec, standardAtom spec, v "work", v "explorer"] _
        (by decide +kernel) (runtime_raw "gslt:explore:rounds" 5 (by decide +kernel)) (by decide)
      · simp [withExplorer, caller, planAtom, standardAtom, applySubst, Subst.lookup]
      · simpa only [backendEq, planEq, standardEq] using
          CompleteExecution.SearchExplore.rounds_returns realization state work startExplorer
            (realized_begin_explorer_ready realization start ready)
    · simp [withExplored, withExplorer, caller, SpaceSemantics.matchBinding, SpaceSemantics.matchValue,
        matchAtom, Subst.lookup]
    · exact readBack

private theorem realized_explore_body (state : Effects.State) (source start : Pattern)
    (ready : realization.SourceReady start)
    (prepared : PureReturns runtime [] state
      (a "gslt:runner:standard" [realization.standard, patternValue source]) state (patternValue start))
    (work : Nat) :
    PureReturns runtime [("work", number work), ("source", patternValue source)] state
      (exploreBody spec profile) state
      (CompleteExecution.patternsValue ((realizedFinal (search := search) start work).nodes.map (·.state))) := by
  apply realized_exploration_body profile realization backendEq planEq standardEq state source start ready prepared work
  apply PureData.raw_capture_returns runtime [] _ state state "gslt:explore:states"
    [encoded (CompleteExecution.SearchExplore.explorerTerm realization (realizedFinal (search := search) start work))]
    [v "explored"] _ (by decide +kernel) (runtime_raw "gslt:explore:states" 1 (by decide +kernel)) (by decide)
  · simp [applySubst, Subst.lookup]
  · exact CompleteExecution.SearchExplore.states_returns realization state _

/-- The common emitted explorer computes the shared search, stopping only
when its existing settled predicate permits it. -/
theorem explore_entry_of_realization {name : String} (fresh : namesFresh spec name profile = true)
    (state : Effects.State) (source start : Pattern) (ready : realization.SourceReady start)
    (prepared : PureReturns runtime [] state
      (a "gslt:runner:standard" [realization.standard, patternValue source]) state (patternValue start))
    (work : Nat) :
    PureReturns (emittedRuntime spec name profile) [] state
      (a (exploreHead name) [patternValue source, number work]) state
      (CompleteExecution.patternsValue ((realizedFinal (search := search) start work).nodes.map (·.state))) := by
  obtain ⟨special, io, known⟩ := entry_facts fresh (head := exploreHead name) (by simp [entries])
  apply PureData.raw_authored_call_return (emittedRuntime spec name profile) []
    [("work", number work), ("source", patternValue source)] state state (exploreHead name)
    [patternValue source, number work] (exploreBody spec profile) _ special io known
  · simp [emittedRuntime, SpaceSemantics.Program.append, program, exploreEquation]
  · simpa using entry_raw (spec := spec) (name := name) (profile := profile)
      (exploreHead name) 2 known (by simp [program])
  · rw [closed_arguments]
    exact PureData.named_equation_clause (emittedRuntime spec name profile) (exploreHead name)
      (exploreEquation spec name profile) ["source", "work"] [patternValue source, number work]
      (entry_row fresh (exploreEquation spec name profile) (by simp [program])) rfl (by decide) rfl
  · exact transport fresh (fresh_parts fresh).2.2.2.2.2.2.2.1
      (realized_explore_body profile realization backendEq planEq standardEq state source start ready prepared work)

private theorem realized_edges_body (state : Effects.State) (source start : Pattern)
    (ready : realization.SourceReady start)
    (prepared : PureReturns runtime [] state
      (a "gslt:runner:standard" [realization.standard, patternValue source]) state (patternValue start))
    (work : Nat) :
    PureReturns runtime [("work", number work), ("source", patternValue source)] state
      (edgesBody spec profile) state
      (encoded (encodeList (CompleteExecution.SearchWire.edgeTerm realization.receiptTerm)
        (Complete.Graph.edges search (realizedFinal (search := search) start work)))) := by
  apply realized_exploration_body profile realization backendEq planEq standardEq state source start ready prepared work
  apply PureData.raw_capture_returns runtime [] _ state state "gslt:explore:edges"
    [backendAtom spec profile, standardAtom spec,
      encoded (CompleteExecution.SearchExplore.explorerTerm realization (realizedFinal (search := search) start work))]
    [backendAtom spec profile, standardAtom spec, v "explored"] _ (by decide +kernel)
    (runtime_raw "gslt:explore:edges" 3 (by decide +kernel)) (by decide)
  · simp [standardAtom, applySubst, Subst.lookup]
  · simpa only [backendEq, standardEq] using CompleteExecution.SearchGraph.edges_returns realization state
      (realizedFinal (search := search) start work)
      (realized_rounds_ready realization work _ (realized_begin_explorer_ready realization start ready))

/-- The common emitted graph preserves the full receipt list on every
node; sharing equal target states does not deduplicate their incoming edges. -/
theorem edges_entry_of_realization {name : String} (fresh : namesFresh spec name profile = true)
    (state : Effects.State) (source start : Pattern) (ready : realization.SourceReady start)
    (prepared : PureReturns runtime [] state
      (a "gslt:runner:standard" [realization.standard, patternValue source]) state (patternValue start))
    (work : Nat) :
    PureReturns (emittedRuntime spec name profile) [] state
      (a (edgesHead name) [patternValue source, number work]) state
      (encoded (encodeList (CompleteExecution.SearchWire.edgeTerm realization.receiptTerm)
        (Complete.Graph.edges search (realizedFinal (search := search) start work)))) := by
  obtain ⟨special, io, known⟩ := entry_facts fresh (head := edgesHead name) (by simp [entries])
  apply PureData.raw_authored_call_return (emittedRuntime spec name profile) []
    [("work", number work), ("source", patternValue source)] state state (edgesHead name)
    [patternValue source, number work] (edgesBody spec profile) _ special io known
  · simp [emittedRuntime, SpaceSemantics.Program.append, program, edgesEquation]
  · simpa using entry_raw (spec := spec) (name := name) (profile := profile)
      (edgesHead name) 2 known (by simp [program])
  · rw [closed_arguments]
    exact PureData.named_equation_clause (emittedRuntime spec name profile) (edgesHead name)
      (edgesEquation spec name profile) ["source", "work"] [patternValue source, number work]
      (entry_row fresh (edgesEquation spec name profile) (by simp [program])) rfl (by decide) rfl
  · exact transport fresh (fresh_parts fresh).2.2.2.2.2.2.2.2
      (realized_edges_body profile realization backendEq planEq standardEq state source start ready prepared work)

end Realized

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
