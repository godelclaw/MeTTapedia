import Mettapedia.Languages.MeTTa.HE.RecursiveDataExecution
import Mettapedia.Languages.MeTTa.HE.ExecutableBoundary
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
import Mettapedia.Languages.MeTTa.HE.QueryBindingProjection
import Mettapedia.Languages.MeTTa.HE.FirstSuccessPreparedArguments
import Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution

/-!
# Independent selected invocation and completed-worker stability

The actual checked worker preserves completed observations under extra depth.
Independent source meaning is constructed below for admitted function and
binding-changing unification invocations, retaining the actual readout table,
caller and occurrence. These are local source/worker connections; neither
arbitrary host effects nor all ordinary recursive calls are certified here.

The final typed-invocation section constructs singleton-arrow applicability and
coverage before composing the existing argument, minimal body and typed-return
admissions. The published raw-domain function annotation is a concrete instance;
polymorphic first-binding coverage and arbitrary host/world behavior remain
separate obligations.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveMachine RecursiveExecution

theorem completed_observation_stable
    (space : Space) (dispatch : GroundedDispatch) (task : Task)
    (budget : Nat) (events : ResultSet) (final : Configuration) (result : ResultPair)
    (completed : (Checked.machine dispatch).run budget
      (Configuration.initial space task) = (events, .finished final))
    (observed : result ∈ events) (extra : Nat) :
    result ∈ (task.replenish extra).denote space dispatch := by
  have original := (finished_results space dispatch task budget events final
    (Checked.finished_refines dispatch budget _ _ _ completed)).1
  rw [completed_depth_stable space dispatch task budget extra events final completed,
    ← original]
  exact observed

/-- A completed atom run earns actual eventual support, independently of any
historical declarative relation. -/
theorem completed_atom_stably_reaches (space : Space) (dispatch : GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (fuel budget : Nat) (live : List Atom)
    (events : ResultSet) (final : Configuration) (result : ResultPair)
    (completed : (Checked.machine dispatch).run budget
      (Configuration.initial space (.atom value expected bindings fuel live)) =
        (events, .finished final))
    (observed : result ∈ events) :
    EvalAtomStablyReaches space dispatch value expected bindings result live := by
  refine ⟨fuel, ?_⟩
  intro larger enough
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  exact completed_observation_stable space dispatch _ budget events final result completed observed extra

end Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness

namespace Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.Invocation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveMachine
open Spec.Match.ModelTheory Spec.Type.Presentation
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- A fixed selected frame determines the whole immediate-function reply.
Reflection keeps its exact frame datum, rather than a model-equivalent record. -/
theorem immediate_function_selected_iff
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (caller : Option Atom) (typing : Spec.Eval.EvalTypeService)
    (bindings : Bindings) (table : TypeSubst)
    (certificate : BindingTheory.ReadoutCertificate bindings table)
    (payload : Atom) (result : Spec.Eval.FrameResult) :
    Spec.Eval.Minimal.CoreStepRel space dispatch live (typing := typing) (caller := caller)
      (.expression [.symbol "function", .expression [.symbol "return", payload]])
      (.selected bindings table certificate) result ↔
      result = (table.apply payload, .selected bindings table certificate) := by
  rw [← Spec.Eval.Minimal.invocationResult_function_exact,
    Spec.Eval.Minimal.immediate_function_completion_exact]
  change (∃ value, value = table.apply payload ∧
    result = (value, Spec.Eval.BindingFrame.selected bindings table certificate)) ↔ _
  simp

/-- An immediate return still performs the actual selected-frame read. The
same table is shared by all variable occurrences in the returned syntax. -/
theorem immediate_function_source
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (caller : Option Atom) (typing : Spec.Eval.EvalTypeService)
    (bindings : Bindings) (payload : Atom)
    (loopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (shape : AssignmentsNonVariable bindings)
    (coherent : CanonicalClassCoherent bindings loopFree shape) :
    let table := QueryBindingProjection.nativeReadoutPresentation bindings
    let frame := Spec.Eval.BindingFrame.selected bindings table
      (QueryBindingProjection.nativeReadoutPresentation_certificate loopFree shape coherent
        (fun _ => Iff.rfl))
    Spec.Eval.Minimal.CoreStepRel space dispatch live (typing := typing) (caller := caller)
      (.expression [.symbol "function", .expression [.symbol "return", payload]]) frame
      (table.apply payload, frame) := by
  dsimp only
  exact (immediate_function_selected_iff space dispatch live caller typing bindings _ _ payload _).mpr rfl

/-- The finite worker evaluates that source read at its actual saved depth.
Read coverage is the executable resolver predicate, not a desired-result
premise; arbitrary alias-bearing principal caller records are admitted. -/
theorem immediate_function_native
    (space : Space) (dispatch : GroundedDispatch) (live : List Atom)
    (caller : Option Atom) (bindings : Bindings) (payload : Atom) (fuel : Nat)
    (loopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (shape : AssignmentsNonVariable bindings)
    (coherent : CanonicalClassCoherent bindings loopFree shape)
    (covered : bindings.applyFullCovered
      (.expression [.symbol "return", payload]) (fuel + 1) = true) :
    minimalStep space dispatch
      (.expression [.symbol "function", .expression [.symbol "return", payload]])
      bindings (fuel + 3) live caller =
      [((QueryBindingProjection.nativeReadoutPresentation bindings).apply payload, bindings)] := by
  have read := QueryBindingProjection.nativeReadoutPresentation_apply loopFree shape coherent
    (.expression [.symbol "return", payload]) (fuel + 1) covered
  simp only [TypeSubst.apply, List.map_cons, List.map_nil] at read
  simp [minimalStep, functionBody, minimalRun, minimalInstruction, ← read, functionTerminal]

set_option maxHeartbeats 1200000 in
/-- Exact guarded execution retains the caller record, one selected readout,
and publication occurrence. No service or source-termination callback is used. -/
theorem immediate_function_checked
    (space : Space) (dispatch : GroundedDispatch) (live : List Atom)
    (caller : Option Atom) (bindings : Bindings) (payload : Atom) (fuel : Nat)
    (loopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (shape : AssignmentsNonVariable bindings)
    (coherent : CanonicalClassCoherent bindings loopFree shape)
    (covered : bindings.applyFullCovered
      (.expression [.symbol "return", payload]) (fuel + 1) = true) :
    let result := ((QueryBindingProjection.nativeReadoutPresentation bindings).apply payload, bindings)
    let start := Configuration.initial space (.primitive
      (.expression [.symbol "function", .expression [.symbol "return", payload]])
      bindings (fuel + 3) live caller)
    (Checked.machine dispatch).run 12 start =
      ([result], .finished ⟨space, .returning [], [], [result]⟩) := by
  have read := QueryBindingProjection.nativeReadoutPresentation_apply loopFree shape coherent
    (.expression [.symbol "return", payload]) (fuel + 1) covered
  simp only [TypeSubst.apply, List.map_cons, List.map_nil] at read
  simp [Configuration.initial, Machine.run, Checked.machine, Checked.guardMachine, Checked.blocked,
    Checked.taskReady, Checked.frameReady, Transition.relabel, RecursiveMachine.machine,
    enter, resume, next, minimalCoreSupported, minimalInstruction, ← read, covered, functionTerminal]

/-- Every completed scheduler run reflects the same selected result and
the same final receiver. Extra scheduler budget cannot choose another frame
or publish another occurrence. -/
theorem immediate_function_checked_reflects
    (space : Space) (dispatch : GroundedDispatch) (live : List Atom)
    (caller : Option Atom) (bindings : Bindings) (payload : Atom) (fuel budget : Nat)
    (loopFree : Spec.Match.Merge.SemanticLoopFree bindings)
    (shape : AssignmentsNonVariable bindings)
    (coherent : CanonicalClassCoherent bindings loopFree shape)
    (covered : bindings.applyFullCovered
      (.expression [.symbol "return", payload]) (fuel + 1) = true)
    (events : ResultSet) (final : Configuration)
    (completed : (Checked.machine dispatch).run budget (Configuration.initial space
      (.primitive (.expression [.symbol "function", .expression [.symbol "return", payload]])
        bindings (fuel + 3) live caller)) = (events, .finished final)) :
    let result := ((QueryBindingProjection.nativeReadoutPresentation bindings).apply payload, bindings)
    events = [result] ∧ final = ⟨space, .returning [], [], [result]⟩ := by
  have known := immediate_function_checked space dispatch live caller bindings payload fuel
    loopFree shape coherent covered
  have left := (Checked.machine dispatch).run_add 12 budget
    (Configuration.initial space (.primitive
      (.expression [.symbol "function", .expression [.symbol "return", payload]])
      bindings (fuel + 3) live caller))
  have right := (Checked.machine dispatch).run_add budget 12
    (Configuration.initial space (.primitive
      (.expression [.symbol "function", .expression [.symbol "return", payload]])
      bindings (fuel + 3) live caller))
  rw [known] at left
  rw [completed, Nat.add_comm budget 12, left] at right
  have same := Prod.mk.inj right
  exact ⟨same.1.symm, (Outcome.finished.inj same.2).symm⟩

end Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.Invocation

namespace Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.Invocation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Steps Spec.Match.Merge Spec.Match.ModelTheory
open Spec.Type.Presentation Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open LeaTTaBridge LeaTTaTypeConformance

/-- A real match/merge occurrence earns its next finite readout table. The
independent merge may use different rows; full solution theory and support
are proved, and all pending syntax shares the actual native table. Matching
and the common input model are explicit leaf admissions, not evaluation
correspondence assumptions. -/
theorem unify_success_source_of_actual_merge
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (caller : Option Atom) (typing : Spec.Eval.EvalTypeService)
    (target pattern yes no : Atom) (incoming matched output : Bindings)
    (inputTable : TypeSubst) (inputCertificate : BindingTheory.ReadoutCertificate incoming inputTable)
    (fuel : Nat)
    (physicalMatch : matched ∈ matchAtoms target pattern fuel)
    (sourceMatch : MatchRel equalityGroundedSemantic target pattern matched)
    (physicalMerge : output ∈ mergeBindings matched incoming fuel)
    (covered : unifyMatchesCovered target pattern incoming fuel = true)
    (unique : AssignmentsNodup matched) (noEqualities : matched.equalities = [])
    (matchedShape : AssignmentsNonVariable matched) (incomingShape : AssignmentsNonVariable incoming)
    (valuation : String → Metta.Atom)
    (matchedModel : HEBindingSatisfied valuation matched)
    (incomingModel : HEBindingSatisfied valuation incoming) :
    ∃ independent,
      (∀ observer, TypeBindingSatisfied observer output ↔ TypeBindingSatisfied observer independent) ∧
      (∀ name, name ∈ specBindingVars output ↔ name ∈ specBindingVars independent) ∧
      ∃ certificate : BindingTheory.ReadoutCertificate independent
          (QueryBindingProjection.nativeReadoutPresentation output),
        let frame := BindingFrame.selected independent
          (QueryBindingProjection.nativeReadoutPresentation output) certificate
        Minimal.CoreStepRel space dispatch live (typing := typing) (caller := caller)
          (.expression [.symbol "unify", target, pattern, yes, no])
          (.selected incoming inputTable inputCertificate) (output.applyFull yes (output.resolutionFuel yes), frame) ∧
        (output.applyFull yes (output.resolutionFuel yes), output) ∈
          minimalStep space GroundedDispatch.none
            (.expression [.symbol "unify", target, pattern, yes, no]) incoming (fuel + 1) live caller ∧
        (∃ events final,
          (RecursiveMachine.Checked.machine GroundedDispatch.none).run (events.length + 2)
            (RecursiveTasks.Configuration.initial space (.primitive
              (.expression [.symbol "unify", target, pattern, yes, no]) incoming (fuel + 1) live caller)) =
            (events, .finished final) ∧
          (output.applyFull yes (output.resolutionFuel yes), output) ∈ events) ∧
        ∀ atom depth, output.applyFullCovered atom depth = true →
          frame.Materialization atom (output.applyFull atom depth) := by
  have nativeLoop := QueryBindingProjection.mergeBindings_semanticLoopFree_of_common_model
    physicalMerge matchedShape incomingShape matchedModel incomingModel
  have nativeShape := QueryBindingProjection.mergeBindings_assignmentsNonVariable_model
    physicalMerge matchedShape incomingShape
  have nativeCoherent := QueryBindingProjection.mergeBindings_canonicalClassCoherent_of_common_model
    physicalMerge unique noEqualities matchedShape incomingShape matchedModel incomingModel
  have matchedNonvar : HEAssignmentsNonVariable matched := by
    intro key name present
    have impossible := matchedShape key (.var name) present
    simp [isVariableB] at impossible
  have incomingNonvar : HEAssignmentsNonVariable incoming := by
    intro key name present
    have impossible := incomingShape key (.var name) present
    simp [isVariableB] at impossible
  obtain ⟨independent, sourceMerge, _independentModel, _independentNonvar⟩ :=
    Spec.Match.Completeness.exists_specMerge_of_solution matchedModel matchedNonvar
      incomingModel incomingNonvar
  have sameTheory : ∀ observer, TypeBindingSatisfied observer output ↔
      TypeBindingSatisfied observer independent := by
    intro observer
    simp only [specTypeBindingSatisfied_iff_heBindingSatisfied_translated]
    exact (mergeBindings_solution_iff physicalMerge _).trans
      (Spec.Match.SolutionTheory.mergeRel_solution_iff sourceMerge _).symm
  have sameSupport : ∀ name, name ∈ specBindingVars output ↔ name ∈ specBindingVars independent := by
    intro name
    rw [FreshPrivateMerge.merge_support_iff physicalMerge,
      QueryBindingProjection.SourceSupport.merge_support sourceMerge]
  let certificate := QueryBindingProjection.nativeReadoutPresentation_certificate
    nativeLoop nativeShape nativeCoherent sameTheory
  have nativeMember : (output.applyFull yes (output.resolutionFuel yes), output) ∈
      minimalStep space GroundedDispatch.none
        (.expression [.symbol "unify", target, pattern, yes, no]) incoming (fuel + 1) live caller := by
    have noLoop : output.hasLoop = false :=
      (hasLoop_eq_false_iff_semanticLoopFree output).mpr nativeLoop
    have produced : (output.applyFull yes (output.resolutionFuel yes), output) ∈
        unifySuccessResults target pattern yes incoming fuel := by
      apply List.mem_flatMap.mpr
      refine ⟨matched, physicalMatch, List.mem_filterMap.mpr ?_⟩
      exact ⟨output, by simpa only [BindingTheory.aliasConstraints_eq_self incomingShape]
        using physicalMerge, by simp [noLoop]⟩
    have nonempty := List.ne_nil_of_mem produced
    simpa only [minimalStep, List.isEmpty_iff, nonempty, if_false] using produced
  refine ⟨independent, sameTheory, sameSupport, certificate, ?_, nativeMember, ?_, ?_⟩
  · apply Minimal.CoreStepRel.unifySuccess
    · exact ⟨matched, sourceMatch, sourceMerge.logicalMerge certificate.satisfiable⟩
    · exact .selected _ _
    · change output.applyFull yes (output.resolutionFuel yes) =
        (QueryBindingProjection.nativeReadoutPresentation output).apply yes
      exact (QueryBindingProjection.nativeReadoutPresentation_apply nativeLoop nativeShape
        nativeCoherent yes (output.resolutionFuel yes)
        (output.applyFullCovered_resolutionFuel yes)).symm
  · exact ⟨_, _, RecursiveExecution.checked_unify_results space GroundedDispatch.none
      target pattern yes no incoming fuel live caller covered, nativeMember⟩
  · intro atom depth covered
    exact (QueryBindingProjection.nativeReadoutPresentation_apply nativeLoop nativeShape
      nativeCoherent atom depth covered).symm

end Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.Invocation


namespace Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.Invocation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks FirstSuccessPreparedArguments FirstSuccessSourceExecution
open Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The existing retained worker executes an immediate function under the
constructed normal presentation. The saved stack and publication prefix are
arbitrary; the read occurs in the reached body frame. -/
theorem normalized_immediate_function_realizes
    (space : Space) (table : TypeSubst) (normal : table.Normal)
    (payload : Atom) (fuel : Nat) (live : List Atom) (caller : Option Atom)
    (enough : LeaTTaBridge.atomDepth (.expression [.symbol "return", payload]) + 2 ≤ fuel + 1)
    (covered : (presentedBindings table).applyFullCovered
      (.expression [.symbol "return", payload]) (fuel + 1) = true) :
    Covered.Realizes space
      (.primitive (.expression [.symbol "function", .expression [.symbol "return", payload]])
        (presentedBindings table) (fuel + 3) live caller)
      [(table.apply payload, presentedBindings table)] := by
  intro stack emitted
  let bindings := presentedBindings table
  let body := Atom.expression [.symbol "return", payload]
  let function := Atom.expression [.symbol "function", body]
  let bodyLive := function :: live
  let bodyCaller := some function
  let terminal := Atom.expression [.symbol "return", table.apply payload]
  have bodyData : minimalInstruction body = false := rfl
  have terminalData : minimalInstruction terminal = false := rfl
  have read : bindings.applyFull body (fuel + 1) = terminal := by
    simpa only [body, terminal, TypeSubst.apply, List.map_cons, List.map_nil] using
      applyFull_presented normal (fuel + 1) body enough
  have first := Covered.enter_request space
    (.primitive function bindings (fuel + 3) live caller) stack emitted
    (by simp [FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady,
      function, body, minimalCoreSupported])
  have second := Covered.enter_request space
    (.functionBody body bindings (fuel + 2) bodyLive bodyCaller)
    (.functionTerminal caller :: stack) emitted
  have third := Covered.enter_request space
    (.minimal body bindings (fuel + 1) bodyLive bodyCaller)
    (.bodyResults (fuel + 1) bodyLive bodyCaller :: .functionTerminal caller :: stack) emitted
  have fourth := Covered.consume_continuation space
    (.bodyResults (fuel + 1) bodyLive bodyCaller) [(body, bindings)]
    (.functionTerminal caller :: stack) emitted
  have fifth := Covered.enter_request space
    (.bodyResults (fuel + 1) [(body, bindings)] bodyLive bodyCaller)
    (.functionTerminal caller :: stack) emitted
    (by simpa only [FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady,
      bindings, body] using covered)
  have emptyRest : Covered.Realizes space
      (.bodyResults (fuel + 1) [] bodyLive bodyCaller) [] := by
    intro saved prior
    simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, List.nil_append] using
      Covered.enter_request space (.bodyResults (fuel + 1) [] bodyLive bodyCaller) saved prior
  have rest := Covered.append_results space (.bodyResults (fuel + 1) [] bodyLive bodyCaller)
    [(terminal, bindings)] [] emptyRest (.functionTerminal caller :: stack) emitted
  have finish := Covered.consume_continuation space (.functionTerminal caller)
    [(terminal, bindings)] stack emitted
  have materialized : Covered.SilentPath
      ⟨space, .work (.bodyResults (fuel + 1) [(body, bindings)] bodyLive bodyCaller),
        .functionTerminal caller :: stack, emitted⟩
      ⟨space, .returning [(terminal, bindings)],
        .append (.bodyResults (fuel + 1) [] bodyLive bodyCaller) ::
          .functionTerminal caller :: stack, emitted⟩ := by
    simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, read,
      terminalData, Bool.false_eq_true, if_false, List.cons_append, List.nil_append] using fifth
  apply first.trans
  simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, RecursiveMachine.resume,
    bodyData, Bool.false_eq_true, if_false,
    function, body, bodyLive, bodyCaller, terminal,
    List.cons_append, List.nil_append, List.append_nil, List.map_cons, List.map_nil,
    functionTerminal] using
    second.trans (third.trans (fourth.trans (materialized.trans (rest.trans finish))))

/-- A computed finite depth covers the actual binding resolver and the
normal-presentation theorem. This is a sufficient resource bound for the
constructed request, not a limit on the language. -/
def normalizedFunctionDepth (table : TypeSubst) (payload : Atom) : Nat :=
  (presentedBindings table).resolutionFuel (.expression [.symbol "return", payload]) +
    LeaTTaBridge.atomDepth (.expression [.symbol "return", payload]) + 4

theorem normalized_immediate_function_constructed
    (space : Space) (table : TypeSubst) (normal : table.Normal)
    (payload : Atom) (live : List Atom) (caller : Option Atom) :
    Covered.Realizes space
      (.primitive (.expression [.symbol "function", .expression [.symbol "return", payload]])
        (presentedBindings table) (normalizedFunctionDepth table payload) live caller)
      [(table.apply payload, presentedBindings table)] := by
  let body := Atom.expression [.symbol "return", payload]
  let fuel := (presentedBindings table).resolutionFuel body + LeaTTaBridge.atomDepth body + 1
  have enough : LeaTTaBridge.atomDepth body + 2 ≤ fuel + 1 := by dsimp [fuel]; omega
  have covered : (presentedBindings table).applyFullCovered body (fuel + 1) = true := by
    apply Bindings.queryRank_covers
    simp only [Bindings.queryRank, fuel, Bindings.resolutionFuel]
    omega
  have path := normalized_immediate_function_realizes space table normal payload fuel live caller
    enough covered
  simpa only [normalizedFunctionDepth, fuel, body, Nat.add_assoc] using path

end Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.Invocation


namespace Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.Invocation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open MetavariableFrameStore.Shared MetavariableFrameStore.Snapshot
open RecursiveTasks FirstSuccessPreparedArguments FirstSuccessSourceExecution
open Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open Spec.Type.Presentation.BindingTheory.CurrentStore
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Loading the independently earned normal presentation into the existing
worker preserves every older continuation and prior publication. The source
frame may keep its original equation record; the worker uses the explicitly
constructed normalized representation. -/
theorem normalized_immediate_function_source_and_path
    (space : Space) (bindings : Bindings) (table : TypeSubst)
    (certificate : ReadoutCertificate bindings table)
    (payload : Atom) (live : List Atom) (caller : Option Atom) :
    Spec.Eval.Minimal.CoreStepRel space noHost live (caller := caller)
      (.expression [.symbol "function", .expression [.symbol "return", payload]])
      (.selected bindings table certificate)
      (table.apply payload, .selected bindings table certificate) ∧
    Covered.Realizes space
      (.primitive (.expression [.symbol "function", .expression [.symbol "return", payload]])
        (presentedBindings table) (normalizedFunctionDepth table payload) live caller)
      [(table.apply payload, presentedBindings table)] := by
  refine ⟨?_, normalized_immediate_function_constructed space table certificate.normal payload live caller⟩
  exact (immediate_function_selected_iff space noHost live caller Spec.Eval.publishedTypeService
    bindings table certificate payload _).mpr rfl

/-- Exact continuation handoff: the function's administrative path produces no
events, and every later budget runs the original saved stack from its reached
result. No behavior of that arbitrary older stack is assumed. -/
theorem normalized_immediate_function_handoff
    (space : Space) (table : TypeSubst) (normal : table.Normal)
    (payload : Atom) (live : List Atom) (caller : Option Atom)
    (stack : List Frame) (earned : ResultSet) :
    ∃ budget, ∀ later,
      (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run (budget + later)
        ⟨space, .work (.primitive
          (.expression [.symbol "function", .expression [.symbol "return", payload]])
          (presentedBindings table) (normalizedFunctionDepth table payload) live caller), stack, earned⟩ =
      (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run later
        ⟨space, .returning [(table.apply payload, presentedBindings table)], stack, earned⟩ :=
  (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).silent_run
    (normalized_immediate_function_constructed space table normal payload live caller stack earned)

/-- The existing completion and pause laws consume the constructed path. The
complete reply is appended once to the already earned prefix. -/
theorem normalized_immediate_function_completed
    (space : Space) (table : TypeSubst) (normal : table.Normal)
    (payload : Atom) (live : List Atom) (caller : Option Atom) (earned : ResultSet) :
    ∃ budget, ∀ later,
      (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run (budget + later)
        ⟨space, .work (.primitive
          (.expression [.symbol "function", .expression [.symbol "return", payload]])
          (presentedBindings table) (normalizedFunctionDepth table payload) live caller), [], earned⟩ =
      ([(table.apply payload, presentedBindings table)],
        .finished ⟨space, .returning [], [], earned ++ [(table.apply payload, presentedBindings table)]⟩) :=
  Covered.realizes_completed
    (normalized_immediate_function_constructed space table normal payload live caller) earned

/-- Every completed run has the constructed reply and the same accumulated
history, even when its scheduler budget differs from the sufficient bound. -/
theorem normalized_immediate_function_completed_unique
    (space : Space) (table : TypeSubst) (normal : table.Normal)
    (payload : Atom) (live : List Atom) (caller : Option Atom) (earned actual : ResultSet)
    (budget : Nat) (finished : Configuration)
    (ran : (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run budget
      ⟨space, .work (.primitive
        (.expression [.symbol "function", .expression [.symbol "return", payload]])
        (presentedBindings table) (normalizedFunctionDepth table payload) live caller), [], earned⟩ =
        (actual, .finished finished)) :
    actual = [(table.apply payload, presentedBindings table)] ∧
      finished = ⟨space, .returning [], [],
        earned ++ [(table.apply payload, presentedBindings table)]⟩ := by
  obtain ⟨bound, complete⟩ :=
    normalized_immediate_function_completed space table normal payload live caller earned
  have stable := (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run_stable
    budget bound _ (by
      intro residual impossible
      rw [ran] at impossible
      cases impossible)
  have same := complete budget
  rw [Nat.add_comm bound budget, stable, ran] at same
  have endpoints := Prod.mk.inj same
  exact ⟨endpoints.1, Outcome.finished.inj endpoints.2⟩

theorem normalized_immediate_function_resumed
    (space : Space) (table : TypeSubst) (normal : table.Normal)
    (payload : Atom) (live : List Atom) (caller : Option Atom) (earned before : ResultSet)
    (first : Nat) (saved : Configuration)
    (paused : (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run first
      ⟨space, .work (.primitive
        (.expression [.symbol "function", .expression [.symbol "return", payload]])
        (presentedBindings table) (normalizedFunctionDepth table payload) live caller), [], earned⟩ =
        (before, .exhausted saved)) :
    ∃ budget after,
      (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run budget saved =
        (after, .finished ⟨space, .returning [], [],
          earned ++ [(table.apply payload, presentedBindings table)]⟩) ∧
      before ++ after = [(table.apply payload, presentedBindings table)] :=
  Covered.completes_saved
    (normalized_immediate_function_constructed space table normal payload live caller)
    earned first before saved paused

/-- A real scoped open-slot write constructs both the renewed source frame and
an immediate return in the existing retained worker. The worker state is the
explicit normalized store view. This does not identify a raw backend record
with that view or assert that the write operation is itself an HE `unify`. -/
theorem currentStore_open_write_immediate_function
    {globals : List String} {image next : ImageOf ContextualOperand}
    {raw : RowOf ContextualOperand} {payload : ContextualOperand} {atom : Atom}
    {operands : List ContextualOperand} {snapshot : List CurrentStore.Row} {qualified : List Atom}
    (written : image.write? raw.reference (some payload) = some next)
    (qualifiedPayload : qualify? image payload = some atom)
    (payloadScope : operandScope globals image payload = true)
    (prepared : prepareScoped? globals image operands = some (snapshot, qualified))
    (beforeChecked : Bindings.hasLoop ⟨assignments snapshot, []⟩ = false)
    (afterChecked : Bindings.hasLoop
      ⟨assignments (snapshot.map (RowOf.afterWrite next.writeClock raw.reference (some atom))), []⟩ = false)
    (read : readRow? image raw.reference = some raw) (unbound : raw.observed.value = none)
    (space : Space) (live : List Atom) (caller : Option Atom) :
    let updated := snapshot.map (RowOf.afterWrite next.writeClock raw.reference (some atom))
    let earlier := normalize (assignments snapshot)
    let later := normalize (assignments updated)
    ∃ certificate : ReadoutCertificate ⟨assignments updated, []⟩ later,
      prepareScoped? globals next operands = some (updated, qualified) ∧
      Spec.Eval.BindingFrame.Update .renew
        (.selected ⟨assignments snapshot, []⟩ earlier
          (prepareScoped?_certified_of_noLoop prepared beforeChecked))
        (.selected ⟨assignments updated, []⟩ later certificate) ∧
      (∀ pending : List Atom,
        List.Forall₂
          (Spec.Eval.BindingFrame.selected ⟨assignments updated, []⟩ later certificate).Materialization
          (pending.map earlier.apply) (pending.map later.apply)) ∧
      ∀ pending : Atom,
        Spec.Eval.Minimal.CoreStepRel space noHost live (caller := caller)
          (.expression [.symbol "function", .expression [.symbol "return", earlier.apply pending]])
          (.selected ⟨assignments updated, []⟩ later certificate)
          (later.apply pending, .selected ⟨assignments updated, []⟩ later certificate) ∧
        Covered.Realizes space
          (.primitive (.expression [.symbol "function", .expression [.symbol "return", earlier.apply pending]])
            (presentedBindings later) (normalizedFunctionDepth later (earlier.apply pending)) live caller)
          [(later.apply pending, presentedBindings later)] := by
  dsimp only
  obtain ⟨certificate, nextPrepared, renewed, allPending⟩ :=
    Spec.Eval.BindingFrame.selected_open_write_renewal_of_noLoop written qualifiedPayload
      payloadScope prepared beforeChecked afterChecked read unbound
  refine ⟨certificate, nextPrepared, renewed, allPending, ?_⟩
  intro pending
  have absorbs := (prepareScoped?_certified_of_noLoop prepared beforeChecked).absorbs
    certificate (fun valuation model =>
      (open_write_models (prepare?_components (prepareScoped?_success prepared)).1
        read unbound next.writeClock atom valuation).mp model |>.1) pending
  have both := normalized_immediate_function_source_and_path space _ _ certificate
    ((normalize (assignments snapshot)).apply pending) live caller
  simpa only [absorbs] using both

end Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.Invocation


namespace Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.Invocation.StoreControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open RecursiveTasks FirstSuccessPreparedArguments FirstSuccessSourceExecution
open Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open Spec.Type.Presentation.BindingTheory.CurrentStore
open CurrentStore.WriteControls CurrentStore.WriteSourceControls
open Mettapedia.GSLT.Distinction.ProductiveBlocks

def repeated : Atom := .expression [.symbol "pair", .var (referenceName callerX),
  .var (referenceName callerX)]
def priorTable : TypeSubst := normalize (assignments beforeRows)
def currentTable : TypeSubst := normalize (assignments afterRows)
def answer : Atom := .expression [.symbol "pair", .symbol "A", .symbol "A"]
def retainedCaller : Atom := .expression [.symbol "saved-caller", .var "outer"]
def retainedLive : List Atom := [.expression [.symbol "older", .var "outer"]]
def priorEvents : ResultSet := [(.symbol "already-published", Bindings.empty)]

attribute [local simp] CurrentStore.normalize normalizeFrom TypeSubst.bind TypeSubst.apply
  TypeSubst.lookup TypeSubst.applyAssignment TypeSubst.erase referenceName
  Controls.callerX Controls.childX Controls.caller Controls.child Shared.Token.ref

theorem prior_read_keeps_one_open_alias : priorTable.apply repeated =
    .expression [.symbol "pair", .var (referenceName childX), .var (referenceName childX)] := by
  simp [priorTable, repeated, before_assignments]

theorem updated_read_reuses_the_written_value : currentTable.apply repeated = answer := by
  simp [currentTable, repeated, answer, after_assignments]

theorem stale_read_is_not_the_new_result : priorTable.apply repeated ≠ answer := by
  rw [prior_read_keeps_one_open_alias]
  simp [answer]

def request : Task := .primitive
  (.expression [.symbol "function", .expression [.symbol "return", priorTable.apply repeated]])
  (presentedBindings currentTable) (normalizedFunctionDepth currentTable (priorTable.apply repeated))
  retainedLive (some retainedCaller)

/-- This uses the actual cross-frame open-slot write, rather than merely
supplying a table certificate to the generic worker theorem. -/
theorem actual_write_source_and_path (space : Space) :
    Spec.Eval.Minimal.CoreStepRel space noHost retainedLive (caller := some retainedCaller)
      (.expression [.symbol "function", .expression [.symbol "return", priorTable.apply repeated]])
      afterFrame (answer, afterFrame) ∧
    Covered.Realizes space request [(answer, presentedBindings currentTable)] := by
  obtain ⟨certificate, _prepared, _renewed, _pending, invocation⟩ :=
    currentStore_open_write_immediate_function
      (raw := openRow) (atom := .symbol "A") (snapshot := beforeRows) (qualified := qualified)
      actual_write payload_qualified payload_scoped before_prepared actual_before_loop_check
      actual_after_loop_check target_open.1 target_open.2 space retainedLive (some retainedCaller)
  have result := invocation repeated
  change Spec.Eval.Minimal.CoreStepRel space noHost retainedLive (caller := some retainedCaller)
      (.expression [.symbol "function", .expression [.symbol "return", priorTable.apply repeated]])
      afterFrame (currentTable.apply repeated, afterFrame) ∧
    Covered.Realizes space request [(currentTable.apply repeated, presentedBindings currentTable)] at result
  simpa only [updated_read_reuses_the_written_value] using result

theorem actual_write_completed (space : Space) :
    ∃ budget, ∀ later,
      (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run (budget + later)
        ⟨space, .work request, [], priorEvents⟩ =
      ([(answer, presentedBindings currentTable)],
        .finished ⟨space, .returning [], [], priorEvents ++ [(answer, presentedBindings currentTable)]⟩) :=
  Covered.realizes_completed (actual_write_source_and_path space).2 priorEvents

/-- The pending outer frame and the old publication remain untouched by the
whole function path. Their subsequent behavior is left to the actual machine. -/
theorem saved_stack_handoff (space : Space) (outer : Frame) (older : List Frame) :
    ∃ budget, ∀ later,
      (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run (budget + later)
        ⟨space, .work request, outer :: older, priorEvents⟩ =
      (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run later
        ⟨space, .returning [(answer, presentedBindings currentTable)], outer :: older, priorEvents⟩ :=
  (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).silent_run
    ((actual_write_source_and_path space).2 (outer :: older) priorEvents)

theorem saved_prefix_resumes_once (space : Space) (first : Nat)
    (before : ResultSet) (saved : Configuration)
    (paused : (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run first
      ⟨space, .work request, [], priorEvents⟩ = (before, .exhausted saved)) :
    ∃ budget after,
      (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run budget saved =
        (after, .finished ⟨space, .returning [], [],
          priorEvents ++ [(answer, presentedBindings currentTable)]⟩) ∧
      before ++ after = [(answer, presentedBindings currentTable)] :=
  Covered.completes_saved (actual_write_source_and_path space).2 priorEvents first before saved paused

/-- The source stores the directed alias and its new assignment. The loaded
worker representation has normalized them; the two records are not asserted
to have identical raw rows. -/
theorem normalized_worker_record_is_not_the_snapshot_record :
    presentedBindings currentTable ≠ (⟨assignments afterRows, []⟩ : Bindings) := by
  intro same
  have rows := congrArg Bindings.assignments same
  simp [presentedBindings, currentTable, after_assignments] at rows

def symbolicTable : TypeSubst := normalize (assignments symbolicRows)

theorem open_symbolic_return_keeps_calls_and_correlation : symbolicTable.apply repeated =
    .expression [.symbol "pair", symbolicValue, symbolicValue] := by
  simp [symbolicTable, repeated, symbolic_assignments, symbolicValue, freeName]
  decide +kernel

/-- An unevaluated call containing a shared residual is returned as syntax by
the function protocol. There is no dispatch or equation execution in this path. -/
theorem open_symbolic_function_path (space : Space) :
    Covered.Realizes space
      (.primitive (.expression [.symbol "function", .expression [.symbol "return", repeated]])
        (presentedBindings symbolicTable) (normalizedFunctionDepth symbolicTable repeated)
        retainedLive (some retainedCaller))
      [(.expression [.symbol "pair", symbolicValue, symbolicValue], presentedBindings symbolicTable)] := by
  have path := normalized_immediate_function_constructed space symbolicTable symbolic_certificate.normal
    repeated retainedLive (some retainedCaller)
  simpa only [open_symbolic_return_keeps_calls_and_correlation] using path

theorem no_depth_suspends_the_whole_saved_request (space : Space) (stack : List Frame) :
    let saved : Configuration := ⟨space,
      .work (.primitive (.expression [.symbol "function", .expression [.symbol "return", repeated]])
        (presentedBindings currentTable) 0 retainedLive (some retainedCaller)), stack, priorEvents⟩
    (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run 1 saved =
      ([], .suspended .evaluationDepth saved) := by
  rfl

theorem no_depth_is_not_empty_completion (space : Space) (stack : List Frame) (final : Configuration) :
    (FirstSuccessRecursiveExecution.Checked.machine GroundedDispatch.none).run 1
      ⟨space,
        .work (.primitive (.expression [.symbol "function", .expression [.symbol "return", repeated]])
          (presentedBindings currentTable) 0 retainedLive (some retainedCaller)), stack, priorEvents⟩ ≠
      ([], .finished final) := by
  rw [no_depth_suspends_the_whole_saved_request]
  intro impossible
  cases impossible

end Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.Invocation.StoreControls



set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.TypedInvocation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Type.Presentation Spec.Eval
open FirstSuccessSourceApplicability FirstSuccessSourceScan FirstSuccessSourceExecution
open RecursiveTasks
attribute [local simp] Atom.atomType Atom.symbolType Atom.expressionType Atom.groundedType
  Atom.variableType Atom.undefinedType

/-- A declared singleton arrow is selected from the actual callback and the
independent ordered scan. This fact does not classify the operator's call lane. -/
theorem single_arrow_selected
    (space : Space) (name : String) (arguments domains : List Atom)
    (expected returned : Atom) (incoming : Bindings) (fuel : Nat)
    (types : getAtomTypes space (.symbol name) = [arrow domains returned])
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (positive : 0 < admittedPathCount space arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (fits : ClosedTypeFits expected returned)
    (enough : sizeOf expected + sizeOf returned + 2 ≤ fuel) :
    FirstSuccessRecursiveStrategy.select space (.expression (.symbol name :: arguments))
        expected incoming (fuel + 1) (getAtomTypes space (.symbol name)) =
      .selected (selectedPolicy domains returned) [incoming] ∧
    FunctionCandidateScanRel PublishedCandidateApplicabilityRel space
      (.expression (.symbol name :: arguments)) expected incoming
      (getAtomTypes space (.symbol name)) (.success (selectedPolicy domains returned) incoming) := by
  obtain ⟨policy, selectedDomains, selectedReturn, native, source⟩ :=
    checked_prefix_selected (RejectedPrefix.nil (space := space) (fuel := fuel)
      (operator := .symbol name) (expected := expected) (arguments := arguments))
      returned domains incoming [] checked positive expectedClosed returnedClosed fits enough
  have same : policy = selectedPolicy domains returned := by
    cases policy with
    | mk functionType argumentTypes returnType isFunction =>
      dsimp at selectedDomains selectedReturn
      subst argumentTypes; subst returnType
      change functionType = arrow domains returned at isFunction
      subst functionType
      rfl
  subst policy
  simpa only [types, List.nil_append, selectedPolicy] using And.intro native source

/-- Every applicability read is covered by the actual domain evidence and
return syntax bound; the selected suffix is never queried. -/
theorem single_arrow_ready
    (space : Space) (name : String) (arguments domains : List Atom)
    (expected returned : Atom) (incoming : Bindings) (fuel : Nat)
    (types : getAtomTypes space (.symbol name) = [arrow domains returned])
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (positive : 0 < admittedPathCount space arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (fits : ClosedTypeFits expected returned)
    (enough : sizeOf expected + sizeOf returned + 2 ≤ fuel) :
    FirstSuccessRecursiveStrategy.selectionReady space (.expression (.symbol name :: arguments))
      expected incoming (fuel + 1) (getAtomTypes space (.symbol name)) = true := by
  obtain ⟨policy, parsed, _, _, _⟩ := FirstSuccessRecursiveStrategy.readPolicy_complete
    (show FunctionTypeRel (arrow domains returned) domains returned from rfl)
  rw [types]
  exact FirstSuccessRecursiveStrategy.selectionReady_selected parsed
    (checked_applicability_covered space (.symbol name) expected returned arguments domains incoming fuel
      checked expectedClosed returnedClosed enough)
    (checked_applicability_success space (.symbol name) expected returned arguments domains incoming fuel
      checked positive expectedClosed returnedClosed fits enough) []

theorem single_arrow_head_covered
    (space : Space) (name : String) (domains : List Atom) (returned : Atom)
    (incoming : Bindings) (fuel : Nat)
    (types : getAtomTypes space (.symbol name) = [arrow domains returned])
    (closed : TypeSubst.typeVars (arrow domains returned) = [])
    (enough : sizeOf (arrow domains returned) + sizeOf (arrow domains returned) + 2 ≤ fuel) :
    typeCastCovered (.symbol name) (arrow domains returned) space incoming fuel = true := by
  unfold typeCastCovered TypeCheckDepth.castQuery
  simp only [rawTypeLookup]
  rw [types]
  apply closed_castLoop_covered _ _ _ _ _ [] closed
  · intro actual member
    obtain rfl := List.mem_singleton.mp member
    exact closed
  · intro actual member
    obtain rfl := List.mem_singleton.mp member
    exact enough

/-- The function-head and argument continuations do not depend on whether
later invocation selects an embedded primitive or an authored equation. -/
theorem single_arrow_function_realizes
    (space : Space) (name : String) (arguments domains : List Atom) (returned : Atom)
    (incoming : Bindings) (fuel : Nat) (rows : ArgumentResults) (live : List Atom)
    (types : getAtomTypes space (.symbol name) = [arrow domains returned])
    (closed : TypeSubst.typeVars (arrow domains returned) = [])
    (enough : sizeOf (arrow domains returned) + sizeOf (arrow domains returned) + 2 < fuel)
    (notEmpty : name ≠ "Empty")
    (argumentsRun : Covered.Realizes space
      (.args arguments domains incoming fuel (.symbol name :: live)) (argumentReplies rows)) :
    Covered.Realizes space
      (.func (.expression (.symbol name :: arguments)) (arrow domains returned)
        incoming (fuel + 1) live) (applications name rows) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    intro stack emitted
    have casts := Covered.symbol_cast_realizes space name (arrow domains returned) incoming fuel
      [] [] (arrow domains returned) notEmpty (by simpa using types)
      closed closed (by simp) (by simp)
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by omega)
      (arrow domains returned :: arguments ++ live)
      (single_arrow_head_covered space name domains returned incoming fuel types closed (by omega))
      (.heads (arrow domains returned) arguments (fuel + 1) live :: stack) emitted
    have transfer := Covered.consume_continuation space
      (.heads (arrow domains returned) arguments (fuel + 1) live)
      [(.symbol name, incoming)] stack emitted
    have finish := Covered.function_head_retained space name domains returned incoming (fuel + 1)
      live rows arguments notEmpty argumentsRun stack emitted
    have beginning := Covered.enter_request space
      (.func (.expression (.symbol name :: arguments)) (arrow domains returned)
        incoming (fuel + 1 + 1) live) stack emitted
    exact beginning.trans (by
      simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
        List.cons_append, List.nil_append] using casts.trans (transfer.trans (by
          simpa only [RecursiveMachine.resume, List.nil_append] using finish)))

/-- The selected arrow contributes one binding occurrence. The actual function
and call continuations retain every downstream result and changed binding. -/
theorem single_arrow_application_realizes
    (space : Space) (name : String) (arguments domains : List Atom)
    (expected returned : Atom) (incoming : Bindings) (fuel : Nat)
    (rows : ArgumentResults) (results : ResultSet) (live : List Atom)
    (types : getAtomTypes space (.symbol name) = [arrow domains returned])
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (positive : 0 < admittedPathCount space arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (fits : ClosedTypeFits expected returned)
    (returnBudget : sizeOf expected + sizeOf returned + 2 ≤ fuel)
    (headClosed : TypeSubst.typeVars (arrow domains returned) = [])
    (headBudget : sizeOf (arrow domains returned) + sizeOf (arrow domains returned) + 2 < fuel)
    (notRaw : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (notEmpty : name ≠ "Empty") (notError : name ≠ "Error")
    (argumentsRun : Covered.Realizes space
      (.args arguments domains incoming fuel (.symbol name ::
        (if returned = Atom.expressionType then Atom.undefinedType else returned) :: live))
      (argumentReplies rows))
    (callsRun : Covered.Realizes space
      (.calls (if returned = Atom.expressionType then Atom.undefinedType else returned)
        (fuel + 1) (applications name rows) live) results) :
    Covered.Realizes space (.atom (.expression (.symbol name :: arguments)) expected
      incoming (fuel + 3) live) (successPriority results) := by
  intro stack emitted
  let callType := if returned = Atom.expressionType then Atom.undefinedType else returned
  let rest := Task.bindingAlternatives (.expression (.symbol name :: arguments))
    (arrow domains returned) callType (fuel + 1) [] live
  have atom := Covered.enter_request space
    (.atom (.expression (.symbol name :: arguments)) expected incoming (fuel + 3) live) stack emitted
  have expression := Covered.enter_request space
    (.expression (.expression (.symbol name :: arguments)) expected incoming (fuel + 2) live)
    (.filter :: stack) emitted
  have selection := Covered.enter_request space
    (.functions (.expression (.symbol name :: arguments)) expected incoming (fuel + 1)
      (getAtomTypes space (.symbol name)) live) (.filter :: stack) emitted
    (single_arrow_ready space name arguments domains expected returned incoming fuel
      types checked positive expectedClosed returnedClosed fits returnBudget)
  have alternatives := Covered.enter_request space
    (.bindingAlternatives (.expression (.symbol name :: arguments)) (arrow domains returned)
      callType (fuel + 1) [incoming] live) (.filter :: stack) emitted
  have function := single_arrow_function_realizes space name arguments domains returned incoming fuel
    rows (callType :: live) types headClosed headBudget notEmpty argumentsRun
    (.calls callType (fuel + 1) live :: .append rest :: .filter :: stack) emitted
  have transfer := Covered.consume_continuation space (.calls callType (fuel + 1) live)
    (applications name rows) (.append rest :: .filter :: stack) emitted
  have remaining : Covered.Realizes space rest [] := by
    intro older prior
    simpa [rest, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter] using
      Covered.enter_request space rest older prior
  have finish := Covered.append_results space rest results [] remaining (.filter :: stack) emitted
  have filtered := Covered.consume_continuation space .filter results stack emitted
  have joined := (callsRun (.append rest :: .filter :: stack) emitted).trans (finish.trans (by
    simpa only [List.append_nil, RecursiveMachine.resume, List.nil_append] using filtered))
  have afterFunction := transfer.trans (by
    simpa only [RecursiveMachine.resume, List.nil_append] using joined)
  have afterAlternatives := alternatives.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      List.cons_append, List.nil_append, rest] using function.trans afterFunction)
  have selected := (single_arrow_selected space name arguments domains expected returned incoming fuel
    types checked positive expectedClosed returnedClosed fits returnBudget).1
  have afterSelection := selection.trans (by
    simpa [FirstSuccessRecursiveStrategy.enter, selected, selectedPolicy, callType] using afterAlternatives)
  have afterExpression := expression.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, rawTypeLookup, List.nil_append] using
      afterSelection)
  change expected ≠ .symbol "Atom" at notRaw
  change expected ≠ .symbol "Expression" at notExpression
  exact atom.trans (by
    simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, isEmptyOrError,
      isEmptyAtom, Atom.empty, Atom.unit, isErrorAtom, getMetaType, notRaw,
      notExpression, notError, Nat.add_assoc] using afterExpression)

/-- Independent source composition at the same declared arrow, without an
artificial exclusion of minimal instruction heads. -/
theorem single_arrow_application_source
    (space : Space) (name : String) (arguments domains : List Atom)
    (expected returned : Atom) (incoming reached : BindingFrame) (fuel : Nat)
    (values live : List Atom) (result : FrameResult) (scope : List String)
    (types : getAtomTypes space (.symbol name) = [arrow domains returned])
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (positive : 0 < admittedPathCount space arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (fits : ClosedTypeFits expected returned)
    (returnBudget : sizeOf expected + sizeOf returned + 2 ≤ fuel)
    (headClosed : TypeSubst.typeVars (arrow domains returned) = [])
    (headBudget : sizeOf (arrow domains returned) + sizeOf (arrow domains returned) + 2 < fuel)
    (notRaw : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (notEmpty : name ≠ "Empty") (notError : name ≠ "Error")
    (argumentsSource : InterpretArgsRel space noHost
      (.symbol name :: (if returned = Atom.expressionType then Atom.undefinedType else returned) :: live)
      (protectedScope := scope) arguments domains incoming (argumentPacket values, reached))
    (callSource : CallRel space noHost live (protectedScope := scope) (.expression (.symbol name :: values))
      (if returned = Atom.expressionType then Atom.undefinedType else returned) reached result) :
    EvalAtomRawRel space noHost live (protectedScope := scope)
      (.expression (.symbol name :: arguments)) expected incoming result := by
  have interpreted : InterpretExpressionRel space noHost live (protectedScope := scope)
      (.expression (.symbol name :: arguments)) expected incoming result := by
    apply InterpretExpressionRel.functionPath _ _ (.symbol name) arguments
      (getAtomTypes space (.symbol name)) (getAtomTypes space (.symbol name))
      (selectedPolicy domains returned)
      (if returned = Atom.expressionType then Atom.undefinedType else returned)
      incoming incoming (.expression (.symbol name :: values), reached) result rfl
      (FirstSuccessSourceReplies.source_types space (.symbol name)) rfl
      (single_arrow_selected space name arguments domains expected returned incoming.bindings fuel
        types checked positive expectedClosed returnedClosed fits returnBudget).2 (.same .renew _) rfl
    · have head : EvalAtomRawRel space noHost
          (arrow domains returned :: arguments ++
            (if returned = Atom.expressionType then Atom.undefinedType else returned) :: live)
          (protectedScope := scope ++ expectedApplicationScope (.expression (.symbol name :: arguments)) expected)
          (.symbol name) (arrow domains returned) incoming (.symbol name, incoming) :=
        symbol_cast_spec space name (arrow domains returned) incoming (fuel - 1)
          [] [] (arrow domains returned) notEmpty (by simp [arrow]) (by simp [arrow])
          (by simpa using types) headClosed headClosed (by simp) (by simp)
          (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by omega) _ _
      simpa only [selectedPolicy, argumentValues_packet] using
        (InterpretFunctionRel.success (.expression (.symbol name :: arguments)) (arrow domains returned)
          expected (.symbol name) returned arguments domains incoming (.symbol name, incoming)
          (argumentPacket values, reached) rfl rfl head
          (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, notEmpty]) argumentsSource ⟨values, rfl⟩)
    · exact callSource
  have notPass : ¬(expected = Atom.atomType ∨ expected = Atom.expressionType ∨
      Atom.expressionType = Atom.variableType) := by
    rintro (raw | intrinsic | impossible)
    · exact notRaw raw
    · exact notExpression intrinsic
    · simp at impossible
  by_cases error : IsErrorRel result.1
  · exact .interpretError _ _ Atom.expressionType incoming result
      (clean_application name arguments notError).1 (.expression (.symbol name :: arguments))
      notPass ⟨.symbol name, arguments, rfl⟩ interpreted error
  · exact .interpretSuccess _ _ Atom.expressionType incoming result
      (clean_application name arguments notError).1 (.expression (.symbol name :: arguments))
      notPass ⟨.symbol name, arguments, rfl⟩ interpreted error


/-- The actual typed prefix composes existing local argument and invocation
admissions. Neither child is replaced by a whole-run adequacy premise. -/
theorem single_arrow_derivation
    (space : Space) (name : String) (arguments domains : List Atom)
    (expected returned : Atom) (incoming : Bindings) (fuel : Nat)
    (rows : ArgumentResults) (outputs : ResultPair → ResultSet) (live : List Atom)
    (types : getAtomTypes space (.symbol name) = [arrow domains returned])
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (positive : 0 < admittedPathCount space arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (fits : ClosedTypeFits expected returned)
    (returnBudget : sizeOf expected + sizeOf returned + 2 ≤ fuel)
    (headClosed : TypeSubst.typeVars (arrow domains returned) = [])
    (headBudget : sizeOf (arrow domains returned) + sizeOf (arrow domains returned) + 2 < fuel)
    (notRaw : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (notEmpty : name ≠ "Empty") (notError : name ≠ "Error")
    (argumentsDerived : ArgsDerivation space .semantic
      (.symbol name :: (if returned = Atom.expressionType then Atom.undefinedType else returned) :: live)
      arguments domains incoming fuel rows)
    (argumentsCovered : argumentsDerived.Covered)
    (calls : ∀ request ∈ applications name rows,
      CallDerivation space .semantic live request.1
        (if returned = Atom.expressionType then Atom.undefinedType else returned)
        request.2 (fuel + 1) (outputs request))
    (callsCovered : ∀ request member, (calls request member).Covered) :
    ∃ derived : AtomDerivation space .semantic live (.expression (.symbol name :: arguments))
      expected incoming (fuel + 3) (successPriority ((applications name rows).flatMap outputs)),
      derived.Covered := by
  let typing := ApplicationTyping.single_arrow space name arguments domains expected returned fuel
    types checked positive expectedClosed returnedClosed fits returnBudget headClosed headBudget
    notRaw notExpression notEmpty notError
  let derived := AtomDerivation.application live name arguments expected incoming fuel typing
    rows outputs argumentsDerived calls
  refine ⟨derived, ?_⟩
  exact AtomDerivation.Covered.application (typing := typing)
    (args := argumentsDerived) (calls := calls)
    (single_arrow_ready space name arguments domains expected returned incoming fuel types checked
      positive expectedClosed returnedClosed fits returnBudget)
    (single_arrow_head_covered space name domains returned incoming (fuel - 1) types headClosed (by omega))
    argumentsCovered callsCovered

/-- The constructed recursive application supplies both its actual checked path
and its independent source result at every related chosen input frame. -/
theorem single_arrow_admitted
    (space : Space) (name : String) (arguments domains : List Atom)
    (expected returned : Atom) (incoming : Bindings) (fuel : Nat)
    (rows : ArgumentResults) (outputs : ResultPair → ResultSet) (live : List Atom)
    (types : getAtomTypes space (.symbol name) = [arrow domains returned])
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (positive : 0 < admittedPathCount space arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (fits : ClosedTypeFits expected returned)
    (returnBudget : sizeOf expected + sizeOf returned + 2 ≤ fuel)
    (headClosed : TypeSubst.typeVars (arrow domains returned) = [])
    (headBudget : sizeOf (arrow domains returned) + sizeOf (arrow domains returned) + 2 < fuel)
    (notRaw : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (notEmpty : name ≠ "Empty") (notError : name ≠ "Error")
    (argumentsDerived : ArgsDerivation space .semantic
      (.symbol name :: (if returned = Atom.expressionType then Atom.undefinedType else returned) :: live)
      arguments domains incoming fuel rows)
    (argumentsCovered : argumentsDerived.Covered)
    (calls : ∀ request ∈ applications name rows,
      CallDerivation space .semantic live request.1
        (if returned = Atom.expressionType then Atom.undefinedType else returned)
        request.2 (fuel + 1) (outputs request))
    (callsCovered : ∀ request member, (calls request member).Covered) :
    let results := successPriority ((applications name rows).flatMap outputs)
    Covered.Realizes space (.atom (.expression (.symbol name :: arguments)) expected
      incoming (fuel + 3) live) results ∧
    ∀ result ∈ results, ∀ scope input,
      SourceBindingComparison.semantic.FrameRelated incoming input →
      ∃ output, EvalAtomRawRel space noHost live (protectedScope := scope)
        (.expression (.symbol name :: arguments)) expected input (result.1, output) ∧
        SourceBindingComparison.semantic.FrameRelated result.2 output := by
  obtain ⟨derived, coverage⟩ := single_arrow_derivation space name arguments domains expected returned
    incoming fuel rows outputs live types checked positive expectedClosed returnedClosed fits returnBudget
    headClosed headBudget notRaw notExpression notEmpty notError argumentsDerived argumentsCovered calls callsCovered
  exact ⟨derived.covered_realizes coverage, fun result member scope input related =>
    derived.sound result member scope input related⟩

/-- Raw argument demand retains the complete body syntax before invocation,
including embedded calls, errors and repeated free variables. -/
theorem raw_single_argument
    (space : Space) (live : List Atom) (value : Atom) (incoming : Bindings) (fuel : Nat) :
    ∃ derived : ArgsDerivation space .semantic live [value] [Atom.atomType] incoming
      (fuel + 2) [([value], incoming)], derived.Covered := by
  have leaf : FirstSuccessLeafEvaluation.LeafRel value Atom.atomType :=
    Or.inr ⟨getMetaType value,
      (Spec.Type.Conformance.metaTypeRel_iff_getMetaType value _).mpr rfl, Or.inl rfl⟩
  let head : AtomDerivation space .semantic live value Atom.atomType incoming (fuel + 1)
      [(value, incoming)] := .leaf live value Atom.atomType incoming fuel leaf
  let tails : ResultPair → ArgumentResults := fun selected => [([], selected.2)]
  have tail : ∀ selected ∈ [(value, incoming)],
      ArgsDerivation space .semantic (selected.1 :: live) [] [] selected.2 (fuel + 1) (tails selected) :=
    fun selected _ => .nil _ _ fuel
  have safe : ∀ selected ∈ [(value, incoming)], selected.1 = value ∨ isEmptyOrError selected.1 = false := by
    intro selected present
    obtain rfl := List.mem_singleton.mp present
    exact Or.inl rfl
  have derived := ArgsDerivation.cons (space := space) (comparison := .semantic)
    live value Atom.atomType [] [] incoming (fuel + 1) [(value, incoming)] tails head safe tail
  have covered : derived.Covered := .cons (safe := safe) (.leaf (leaf := leaf)) (fun selected _ => .nil)
  simpa only [tails, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    List.append_nil] using Exists.intro derived covered

/-- A genuine function body supplies the raw minimal child. The ordinary
receiver evaluates each completed result at the declared demand and keeps
its reached frame; terminal rows remain physical occurrences. -/
theorem function_call_of_body
    (space : Space) (live parts : List Atom) (expected : Atom) (incoming : Bindings)
    (fuel : Nat) (terminals : ResultSet) (outputs : ResultPair → ResultSet)
    (body : FunctionBodyDerivation space .semantic
      (.expression [.symbol "function", .expression parts] :: expected :: live)
      (some (.expression [.symbol "function", .expression parts]))
      (.expression parts) incoming fuel terminals)
    (returns : ∀ result ∈ terminals.map (fun result => (HE.functionTerminal none result.1, result.2)),
      ReturnDerivation space .semantic live (.expression [.symbol "function", .expression parts])
        expected result.1 result.2 (fuel + 2) (outputs result)) :
    CallDerivation space .semantic live (.expression [.symbol "function", .expression parts])
      expected incoming (fuel + 3)
      ((terminals.map (fun result => (HE.functionTerminal none result.1, result.2))).flatMap outputs) := by
  apply CallDerivation.embedded live "function" [.expression parts] expected incoming (fuel + 2)
    (terminals.map (fun result => (HE.functionTerminal none result.1, result.2))) outputs rfl (by decide) rfl
  · exact .instruction _ _ _ _ (fuel + 1) _ rfl
      (by simp [Minimal.IsChain]) (.function _ _ parts incoming fuel terminals body)
  · exact returns

theorem function_call_of_body_covered
    (space : Space) (live parts : List Atom) (expected : Atom) (incoming : Bindings)
    (fuel : Nat) (terminals : ResultSet) (outputs : ResultPair → ResultSet)
    (body : FunctionBodyDerivation space .semantic
      (.expression [.symbol "function", .expression parts] :: expected :: live)
      (some (.expression [.symbol "function", .expression parts]))
      (.expression parts) incoming fuel terminals)
    (returns : ∀ result ∈ terminals.map (fun result => (HE.functionTerminal none result.1, result.2)),
      ReturnDerivation space .semantic live (.expression [.symbol "function", .expression parts])
        expected result.1 result.2 (fuel + 2) (outputs result))
    (covered : ∀ result member, (returns result member).Covered) :
    (function_call_of_body space live parts expected incoming fuel terminals outputs body returns).Covered := by
  exact CallDerivation.Covered.embedded
    (semantic := rfl) (clean := by decide) (instruction := rfl)
    (child := MinimalDerivation.instruction _ _ _ _ (fuel + 1) _ rfl
      (by simp [Minimal.IsChain]) (PrimitiveDerivation.function _ _ parts incoming fuel terminals body))
    (returns := returns) covered

end Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.TypedInvocation



set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.TypedInvocation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Type Spec.Type.Presentation
open FirstSuccessSourceApplicability FirstSuccessSourceScan FirstSuccessSourceExecution
open RecursiveTasks

/-- The published raw-domain function type composes with an admitted minimal
body and its actual typed receiver. The body may renew bindings and produce
multiple physical terminal occurrences; the same output map is used by the
retained worker and the independent source derivation. -/
theorem full_function_derivation_of_body
    (space : Space) (live parts : List Atom) (expected : Atom) (incoming : Bindings)
    (fuel : Nat) (terminals : ResultSet) (outputs : ResultPair → ResultSet)
    (types : getAtomTypes space (.symbol "function") = [arrow [Atom.atomType] Atom.atomType])
    (expectedClosed : TypeSubst.typeVars expected = [])
    (notRaw : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (returnBudget : sizeOf expected + sizeOf Atom.atomType + 2 ≤ fuel + 2)
    (headBudget : sizeOf (arrow [Atom.atomType] Atom.atomType) +
      sizeOf (arrow [Atom.atomType] Atom.atomType) + 2 < fuel + 2)
    (body : FunctionBodyDerivation space .semantic
      (.expression [.symbol "function", .expression parts] :: Atom.atomType :: live)
      (some (.expression [.symbol "function", .expression parts]))
      (.expression parts) incoming fuel terminals)
    (returns : ∀ result ∈ terminals.map (fun result => (HE.functionTerminal none result.1, result.2)),
      ReturnDerivation space .semantic live (.expression [.symbol "function", .expression parts])
        Atom.atomType result.1 result.2 (fuel + 2) (outputs result))
    (covered : ∀ result member, (returns result member).Covered) :
    let results := successPriority
      ((terminals.map (fun result => (HE.functionTerminal none result.1, result.2))).flatMap outputs)
    ∃ derived : AtomDerivation space .semantic live
      (.expression [.symbol "function", .expression parts]) expected incoming (fuel + 5) results,
      derived.Covered := by
  obtain ⟨args, argsCovered⟩ := raw_single_argument space (.symbol "function" :: Atom.atomType :: live)
    (.expression parts) incoming fuel
  have call := function_call_of_body space live parts Atom.atomType incoming fuel terminals outputs body returns
  have callCovered := function_call_of_body_covered space live parts Atom.atomType incoming fuel
    terminals outputs body returns covered
  have argumentChecks : List.Forall₂
      (fun argument domain => ArgumentDomainEvidence space argument domain (fuel + 2))
      [.expression parts] [Atom.atomType] := .cons (.wildcard (Or.inl rfl)) .nil
  have positive : 0 < admittedPathCount space [.expression parts] [Atom.atomType] := by
    simpa [admittedPathCount, acceptedTypes, ClosedTypeFits] using
      List.length_pos_iff.mpr (FirstSuccessSourceReplies.getAtomTypes_nonempty space (.expression parts))
  have joined := single_arrow_derivation space "function" [.expression parts] [Atom.atomType]
    expected Atom.atomType incoming (fuel + 2) [([.expression parts], incoming)]
    (fun _ => (terminals.map (fun result => (HE.functionTerminal none result.1, result.2))).flatMap outputs)
    live types argumentChecks positive expectedClosed rfl
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) returnBudget rfl headBudget
    notRaw notExpression (by decide) (by decide) args argsCovered
    (by
      intro request member
      have same : request = (.expression [.symbol "function", .expression parts], incoming) := by
        simpa only [applications, List.map_cons, List.map_nil, List.mem_singleton] using member
      subst request
      simpa only [show (Atom.atomType = Atom.expressionType) = False from propext (by decide),
        if_false, Nat.add_assoc] using call)
    (by
      intro request member
      have same : request = (.expression [.symbol "function", .expression parts], incoming) := by
        simpa only [applications, List.map_cons, List.map_nil, List.mem_singleton] using member
      subst request
      exact callCovered)
  simpa only [applications, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Nat.add_assoc] using joined

/-- Full function execution is a consequence of the ordinary recursive
application derivation and its retained typed receiver. -/
theorem full_function_of_body
    (space : Space) (live parts : List Atom) (expected : Atom) (incoming : Bindings)
    (fuel : Nat) (terminals : ResultSet) (outputs : ResultPair → ResultSet)
    (types : getAtomTypes space (.symbol "function") = [arrow [Atom.atomType] Atom.atomType])
    (expectedClosed : TypeSubst.typeVars expected = [])
    (notRaw : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (returnBudget : sizeOf expected + sizeOf Atom.atomType + 2 ≤ fuel + 2)
    (headBudget : sizeOf (arrow [Atom.atomType] Atom.atomType) +
      sizeOf (arrow [Atom.atomType] Atom.atomType) + 2 < fuel + 2)
    (body : FunctionBodyDerivation space .semantic
      (.expression [.symbol "function", .expression parts] :: Atom.atomType :: live)
      (some (.expression [.symbol "function", .expression parts]))
      (.expression parts) incoming fuel terminals)
    (returns : ∀ result ∈ terminals.map (fun result => (HE.functionTerminal none result.1, result.2)),
      ReturnDerivation space .semantic live (.expression [.symbol "function", .expression parts])
        Atom.atomType result.1 result.2 (fuel + 2) (outputs result))
    (covered : ∀ result member, (returns result member).Covered) :
    let results := successPriority
      ((terminals.map (fun result => (HE.functionTerminal none result.1, result.2))).flatMap outputs)
    Covered.Realizes space
      (.atom (.expression [.symbol "function", .expression parts]) expected incoming (fuel + 5) live)
      results ∧
    ∀ result ∈ results, ∀ scope input,
      SourceBindingComparison.semantic.FrameRelated incoming input →
      ∃ output, EvalAtomRawRel space noHost live (protectedScope := scope)
        (.expression [.symbol "function", .expression parts]) expected input (result.1, output) ∧
        SourceBindingComparison.semantic.FrameRelated result.2 output := by
  obtain ⟨derived, coverage⟩ := full_function_derivation_of_body space live parts expected incoming
    fuel terminals outputs types expectedClosed notRaw notExpression returnBudget headBudget body returns covered
  exact ⟨derived.covered_realizes coverage, fun result member scope input related =>
    derived.sound result member scope input related⟩

end Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.TypedInvocation



set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.TypedInvocation.Controls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Steps Spec.Type.RuntimeRefinement
open FirstSuccessSourceExecution FirstSuccessSourceScan FirstSuccessSourceApplicability
open RecursiveTasks FirstSuccessRecursiveExecution

private def context : Space := Space.ofList
  [.expression [.symbol ":", .symbol "function", arrow [Atom.atomType] Atom.atomType]]
private def value : Atom := .symbol "Value"
private def pending : Atom := .expression [.symbol "Pair", .var "public", .var "public"]
private def answer : Atom := .expression [.symbol "Pair", value, value]
private def template : Atom := .expression [.symbol "return", pending]
private def returned : Atom := .expression [.symbol "return", answer]
private def parts : List Atom := [.symbol "unify", value, .var "public", template, .symbol "Miss"]
private def body : Atom := .expression parts
private def block : Atom := .expression [.symbol "function", body]
private def bindings : Bindings := Bindings.empty.assign "public" value
private def raw : ResultSet := [(returned, bindings)]
private def bodyDepth : Nat := 4096
private def live : List Atom := [.expression [.symbol "Outside", .var "public", .var "public"]]

private theorem raw_success :
    unifySuccessResults value (.var "public") template Bindings.empty (bodyDepth - 3) = raw := by
  decide +kernel

private theorem primitive (scope : List Atom) (caller : Option Atom) :
    PrimitiveDerivation context .semantic scope caller body Bindings.empty (bodyDepth - 2) raw := by
  have derived := PrimitiveDerivation.unifySuccess (space := context) (comparison := .semantic)
    scope caller value (.var "public") template (.symbol "Miss") Bindings.empty (bodyDepth - 3)
    (by decide +kernel) (by rw [raw_success]; simp [raw])
  rw [raw_success] at derived
  simpa only [body, parts, bodyDepth] using derived

private theorem body_admitted (scope : List Atom) (caller : Option Atom) :
    FunctionBodyDerivation context .semantic scope caller body Bindings.empty bodyDepth raw := by
  have child : MinimalDerivation context .semantic scope caller body Bindings.empty (bodyDepth - 1) raw :=
    .instruction scope caller body Bindings.empty (bodyDepth - 2) raw rfl
      (by simp [Minimal.IsChain, body, parts]) (primitive scope caller)
  have derived := FunctionBodyDerivation.run (space := context) (comparison := .semantic) scope caller body
    Bindings.empty (bodyDepth - 1) raw (fun result => [result]) child
    (by intro result member; obtain rfl := List.mem_singleton.mp member; decide +kernel)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member; rfl)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member; contradiction)
  simpa only [raw, List.flatMap_cons, List.flatMap_nil, List.singleton_append, bodyDepth] using derived

private theorem receiver :
    ReturnDerivation context .semantic live block Atom.atomType answer bindings (bodyDepth + 2)
      [(answer, bindings)] :=
  .evaluate live block Atom.atomType answer bindings (bodyDepth + 2) _
    (by simp [answer, Atom.notReducible])
    (by simp [answer, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (.leaf live answer Atom.atomType bindings (bodyDepth + 1)
      (Or.inr ⟨Atom.expressionType, .expression _, Or.inl rfl⟩))

private theorem receiver_covered : receiver.Covered := by
  exact .evaluate
    (accepted := by simp [answer, Atom.notReducible])
    (running := by simp [answer, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (child := .leaf live answer Atom.atomType bindings (bodyDepth + 1)
      (Or.inr ⟨Atom.expressionType, .expression _, Or.inl rfl⟩))
    (.leaf (leaf := Or.inr ⟨Atom.expressionType, .expression _, Or.inl rfl⟩))

private theorem joined :
    Covered.Realizes context (.atom block Atom.undefinedType Bindings.empty (bodyDepth + 5) live)
      [(answer, bindings)] ∧
    ∀ scope input, SourceBindingComparison.semantic.FrameRelated Bindings.empty input →
      ∃ output, EvalAtomRawRel context noHost live (protectedScope := scope)
        block Atom.undefinedType input (answer, output) ∧
        SourceBindingComparison.semantic.FrameRelated bindings output := by
  have actual := full_function_of_body context live parts Atom.undefinedType Bindings.empty bodyDepth
    raw (fun result => [result]) (by decide +kernel) rfl (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)
    (body_admitted (block :: Atom.atomType :: live) (some block))
    (by intro result member; obtain rfl := List.mem_singleton.mp member; exact receiver)
    (by intro result member; obtain rfl := List.mem_singleton.mp member; exact receiver_covered)
  change Covered.Realizes context (.atom block Atom.undefinedType Bindings.empty (bodyDepth + 5) live)
      [(answer, bindings)] ∧
    (∀ result ∈ [(answer, bindings)], ∀ scope input,
      SourceBindingComparison.semantic.FrameRelated Bindings.empty input →
      ∃ output, EvalAtomRawRel context noHost live (protectedScope := scope)
        block Atom.undefinedType input (result.1, output) ∧
        SourceBindingComparison.semantic.FrameRelated result.2 output) at actual
  exact ⟨actual.1, fun scope input related => actual.2 (answer, bindings) (by simp) scope input related⟩

/-- Full typed invocation enters the real raw-domain function body and returns
both correlated values with the nonempty reached binding record. -/
theorem typed_function_source_and_path :
    Covered.Realizes context (.atom block Atom.undefinedType Bindings.empty (bodyDepth + 5) live)
      [(answer, bindings)] ∧
    ∀ scope input, SourceBindingComparison.semantic.FrameRelated Bindings.empty input →
      ∃ output, EvalAtomRawRel context noHost live (protectedScope := scope)
        block Atom.undefinedType input (answer, output) ∧
        SourceBindingComparison.semantic.FrameRelated bindings output := joined

theorem typed_function_preserves_both_uses :
    bindings.lookup "public" = some value ∧ bindings ≠ Bindings.empty ∧
    answer = .expression [.symbol "Pair", value, value] ∧
    live = [.expression [.symbol "Outside", .var "public", .var "public"]] := by decide +kernel

/-- The complete output is independent of extra execution budget once the
retained computation finishes. Existing output prefixes remain intact. -/
theorem typed_function_completes (earned : ResultSet) :
    ∃ budget, ∀ later, (Checked.machine HE.GroundedDispatch.none).run (budget + later)
      ⟨context, .work (.atom block Atom.undefinedType Bindings.empty (bodyDepth + 5) live), [], earned⟩ =
      ([(answer, bindings)], .finished ⟨context, .returning [], [], earned ++ [(answer, bindings)]⟩) :=
  Covered.realizes_completed joined.1 earned

/-- This source instance starts from the earned empty selected frame; it is
not merely an implication over an uninhabited representation premise. -/
theorem typed_function_independent_source :
    ∃ output, EvalAtomRawRel context noHost live block Atom.undefinedType
      PrincipalBindingFrame.empty.sourceFrame (answer, output) ∧
      SourceBindingComparison.semantic.FrameRelated bindings output :=
  joined.2 [] PrincipalBindingFrame.empty.sourceFrame
    (.of_principal PrincipalBindingFrame.empty (.refl _))

theorem completed_binding_cannot_be_erased
    (budget : Nat) (finished : Configuration)
    (ran : (Checked.machine HE.GroundedDispatch.none).run budget
      ⟨context, .work (.atom block Atom.undefinedType Bindings.empty (bodyDepth + 5) live), [], []⟩ =
      ([(answer, Bindings.empty)], .finished finished)) : False := by
  have exactOutput := realizes_completed_unique (Covered.unchecked joined.1)
    [] [(answer, Bindings.empty)] budget finished
    (Checked.finished_refines HE.GroundedDispatch.none budget _ _ finished ran)
  have different : [(answer, Bindings.empty)] ≠ [(answer, bindings)] := by decide +kernel
  exact different exactOutput.1

theorem zero_depth_preserves_pending_task :
    (Checked.machine HE.GroundedDispatch.none).run 1
      ⟨context, .work (.atom block Atom.undefinedType Bindings.empty 0 live), [], []⟩ =
      ([], .suspended .evaluationDepth
        ⟨context, .work (.atom block Atom.undefinedType Bindings.empty 0 live), [], []⟩) := by rfl

theorem zero_depth_is_not_completed_empty (finished : Configuration) :
    (Checked.machine HE.GroundedDispatch.none).run 1
      ⟨context, .work (.atom block Atom.undefinedType Bindings.empty 0 live), [], []⟩ ≠
      ([], .finished finished) := by
  rw [zero_depth_preserves_pending_task]
  intro same
  cases same

private def initial : Configuration :=
  ⟨context, .work (.atom block Atom.undefinedType Bindings.empty (bodyDepth + 5) live), [], []⟩
private def afterWrite : Configuration :=
  ⟨context, .returning raw,
    [.bodyResults (bodyDepth - 1) (block :: Atom.atomType :: live) (some block),
     .functionTerminal none, .invocationReturn (.ordinary Atom.atomType) block (bodyDepth + 2) live,
     .append (.calls Atom.atomType (bodyDepth + 3) [] live),
     .append (.bindingAlternatives block (arrow [Atom.atomType] Atom.atomType) Atom.atomType
       (bodyDepth + 3) [] live), .filter], []⟩

/-- This is a checkpoint of the full typed entry, after the actual body write
and before the retained body and ordinary-return receivers have resumed. -/
theorem typed_checkpoint_after_write :
    (Checked.machine HE.GroundedDispatch.none).run 30 initial = ([], .exhausted afterWrite) := by rfl

theorem typed_checkpoint_retains_scope_and_caller :
    afterWrite.space = context ∧ afterWrite.control = .returning [(returned, bindings)] ∧
    Frame.bodyResults (bodyDepth - 1) (block :: Atom.atomType :: live) (some block) ∈ afterWrite.stack ∧
    Frame.invocationReturn (.ordinary Atom.atomType) block (bodyDepth + 2) live ∈ afterWrite.stack := by
  exact ⟨rfl, rfl, List.mem_cons_self,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

theorem typed_checkpoint_resumes_exactly :
    ∃ budget remaining, (Checked.machine HE.GroundedDispatch.none).run budget afterWrite =
      (remaining, .finished ⟨context, .returning [], [], [(answer, bindings)]⟩) ∧
      remaining = [(answer, bindings)] := by
  simpa only [List.nil_append] using
    Covered.completes_saved joined.1 [] 30 [] afterWrite typed_checkpoint_after_write

theorem typed_checkpoint_is_not_empty_completion (finished : Configuration) :
    (Checked.machine HE.GroundedDispatch.none).run 30 initial ≠ ([], .finished finished) := by
  rw [typed_checkpoint_after_write]
  intro same
  cases same

theorem raw_domain_retains_instruction_syntax :
    Covered.Realizes context
      (.args [body] [Atom.atomType] Bindings.empty (bodyDepth + 2)
        (.symbol "function" :: Atom.atomType :: live))
      (argumentReplies [([body], Bindings.empty)]) := by
  obtain ⟨derived, covered⟩ := raw_single_argument context
    (.symbol "function" :: Atom.atomType :: live) body Bindings.empty bodyDepth
  exact derived.covered_realizes covered

end Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.TypedInvocation.Controls


section RecursiveTypedApplicationControls
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
namespace Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.TypedInvocation.NestedControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Steps Spec.Type.RuntimeRefinement
open FirstSuccessSourceExecution FirstSuccessSourceScan FirstSuccessSourceApplicability
open RecursiveTasks FirstSuccessRecursiveExecution

def value : Atom := .symbol "Value"
def pair (key : String) : Atom := .expression [.symbol "Pair", .var key, .var key]
def answer : Atom := .expression [.symbol "Pair", value, value]
def template (key : String) : Atom := .expression [.symbol "return", pair key]
def returned : Atom := .expression [.symbol "return", answer]
def parts (key : String) : List Atom := [.symbol "unify", value, .var key, template key, .symbol "Miss"]
def body (key : String) : Atom := .expression (parts key)
def block (key : String) : Atom := .expression [.symbol "function", body key]
def nested (key : String) : Atom := .expression [.symbol "box", block key]
def final : Atom := .expression [.symbol "box", answer]
def query : Atom := .expression [.symbol "make"]
def rule : Atom := .expression [.symbol "=", query, nested "public"]
def context : Space := Space.ofList
  [.expression [.symbol ":", .symbol "function", arrow [Atom.atomType] Atom.atomType],
   .expression [.symbol ":", .symbol "box", arrow [Atom.undefinedType] Atom.atomType],
   .expression [.symbol ":", .symbol "make", arrow [] Atom.undefinedType], rule, rule]
def key (index : Fin 2) : String := if index = 0 then "public#3" else "public#4"
def bindings (index : Fin 2) : Bindings := Bindings.empty.assign (key index) value
def raw (index : Fin 2) : ResultSet := [(returned, bindings index)]
def bodyDepth : Nat := 4096
def live : List Atom := [.expression [.symbol "Outside", .var "caller", .var "caller"]]

theorem body_admitted (index : Fin 2) (scope : List Atom) (caller : Option Atom) :
    FunctionBodyDerivation context .semantic scope caller (body (key index)) Bindings.empty bodyDepth (raw index) := by
  have success : unifySuccessResults value (.var (key index)) (template (key index)) Bindings.empty (bodyDepth - 3) = raw index := by
    fin_cases index <;> decide +kernel
  have primitive : PrimitiveDerivation context .semantic scope caller (body (key index)) Bindings.empty (bodyDepth - 2) (raw index) := by
    have derived := PrimitiveDerivation.unifySuccess (space := context) (comparison := .semantic)
      scope caller value (.var (key index)) (template (key index)) (.symbol "Miss") Bindings.empty (bodyDepth - 3)
      (by fin_cases index <;> decide +kernel) (by rw [success]; simp [raw])
    rw [success] at derived
    simpa only [body, parts, bodyDepth] using derived
  have child : MinimalDerivation context .semantic scope caller (body (key index)) Bindings.empty (bodyDepth - 1) (raw index) :=
    .instruction scope caller (body (key index)) Bindings.empty (bodyDepth - 2) _ rfl
      (by simp [Minimal.IsChain, body, parts]) primitive
  have derived := FunctionBodyDerivation.run (space := context) (comparison := .semantic) scope caller (body (key index))
    Bindings.empty (bodyDepth - 1) (raw index) (fun result => [result]) child
    (by intro result member; obtain rfl := List.mem_singleton.mp member; rfl)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member; rfl)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member; contradiction)
  simpa only [raw, List.flatMap_cons, List.flatMap_nil, List.singleton_append, bodyDepth] using derived

theorem inner_derived (index : Fin 2) (scope : List Atom) :
    ∃ derived : AtomDerivation context .semantic scope (block (key index)) Atom.undefinedType
      Bindings.empty (bodyDepth + 5) [(answer, bindings index)], derived.Covered := by
  have receiver : ReturnDerivation context .semantic scope (block (key index)) Atom.atomType answer
      (bindings index) (bodyDepth + 2) [(answer, bindings index)] :=
    .evaluate scope _ _ _ _ _ _ (by simp [answer, Atom.notReducible])
      (by simp [answer, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
      (.leaf scope answer Atom.atomType (bindings index) (bodyDepth + 1)
        (Or.inr ⟨Atom.expressionType, .expression _, Or.inl rfl⟩))
  have covered : receiver.Covered := .evaluate
    (accepted := by simp [answer, Atom.notReducible])
    (running := by simp [answer, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (child := .leaf scope answer Atom.atomType (bindings index) (bodyDepth + 1)
      (Or.inr ⟨Atom.expressionType, .expression _, Or.inl rfl⟩))
    (.leaf (leaf := Or.inr ⟨Atom.expressionType, .expression _, Or.inl rfl⟩))
  have actual := full_function_derivation_of_body context scope (parts (key index)) Atom.undefinedType
    Bindings.empty bodyDepth (raw index) (fun result => [result]) (by decide +kernel)
    rfl (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (body_admitted index (block (key index) :: Atom.atomType :: scope) (some (block (key index))))
    (by intro result member; obtain rfl := List.mem_singleton.mp member; exact receiver)
    (by intro result member; obtain rfl := List.mem_singleton.mp member; exact covered)
  exact actual

private theorem equation_lhs {left right : Atom}
    (stored : .expression [.symbol "=", left, right] ∈ context.atoms) : left = query := by
  exact (show left = query ∧ right = nested "public" by
    simpa [context, Space.ofList, rule, arrow, Atom.expression.injEq] using stored).1

private theorem box_no_match (scope : List Atom) (incoming : Bindings) :
    EquationQueryNoMatchRel context scope final incoming := by
  intro freshPattern freshRhs matched selected
  obtain ⟨left, right, stored, ⟨rename, injective, renamed, rest⟩, matching⟩ := selected
  have same := equation_lhs stored
  subst left
  cases renamed with
  | expression items =>
    cases items with
    | cons head tail =>
      cases head
      cases tail
      cases matching with
      | expression items admitted =>
        cases items with
        | cons head merged tail =>
          exact Spec.Match.Merge.symbol_mismatch_not_match (by decide) _ head


theorem nested_derived (index : Fin 2) :
    ∃ derived : AtomDerivation context .semantic live (nested (key index)) Atom.undefinedType
      Bindings.empty (bodyDepth + 9) [(final, bindings index)], derived.Covered := by
  let scope := .symbol "box" :: Atom.atomType :: live
  obtain ⟨inner, innerCovered⟩ := inner_derived index scope
  let heads : ResultSet := [(answer, bindings index)]
  let tails : ResultPair → ArgumentResults := fun row => [([], row.2)]
  have safe : ∀ row ∈ heads, row.1 = block (key index) ∨ isEmptyOrError row.1 = false := by
    intro row member; obtain rfl := List.mem_singleton.mp member; right; rfl
  have tail : ∀ row ∈ heads, ArgsDerivation context .semantic (row.1 :: scope)
      [] [] row.2 (bodyDepth + 5) (tails row) := by
    intro row member
    exact .nil _ _ (bodyDepth + 4)
  let args := ArgsDerivation.cons scope (block (key index)) Atom.undefinedType [] [] Bindings.empty
    (bodyDepth + 5) heads tails inner safe tail
  have argsCovered : args.Covered :=
    .cons (head := inner) (safe := safe) (tail := tail) innerCovered (fun _ _ => .nil)
  have queryEmpty : equationCandidates context live final Atom.atomType (bindings index) (bodyDepth + 6) = [] := by
    fin_cases index <;> decide +kernel
  let call := CallDerivation.unreduced (space := context) (comparison := .semantic) live "box" [answer]
    Atom.atomType (bindings index) (bodyDepth + 6) (by decide) (by decide) (by decide)
    queryEmpty (box_no_match (Atom.atomType :: live) (bindings index))
  have callCovered : call.Covered := CallDerivation.Covered.unreduced
    (ordinary := by decide) (nonembedded := by decide) (clean := by decide)
    (empty := queryEmpty) (absent := box_no_match (Atom.atomType :: live) (bindings index))
    (by fin_cases index <;> decide +kernel)
  have derived := single_arrow_derivation context "box" [block (key index)] [Atom.undefinedType]
    Atom.undefinedType Atom.atomType Bindings.empty (bodyDepth + 6)
    [([answer], bindings index)] (fun row => [row]) live
    (by decide +kernel) (.cons (.wildcard (Or.inr rfl)) .nil)
    (by fin_cases index <;> decide +kernel)
    rfl rfl (by left; rfl) (by decide +kernel) rfl (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide)
    args argsCovered
    (by intro row member; obtain rfl := List.mem_singleton.mp member; exact call)
    (by intro row member; obtain rfl := List.mem_singleton.mp member; exact callCovered)
  exact derived

def request (index : Fin 2) : ResultPair := (nested (key index), Bindings.empty)
def answers : ResultSet := [(final, bindings 0), (final, bindings 1)]
def responses (row : ResultPair) : ResultSet :=
  if row = request 0 then [(final, bindings 0)] else [(final, bindings 1)]

theorem responses_index (index : Fin 2) : responses (request index) = [(final, bindings index)] := by
  fin_cases index <;> decide +kernel

theorem queried : equationCandidates context live query Atom.undefinedType Bindings.empty
    (bodyDepth + 9) = [request 0, request 1] := by decide +kernel

theorem prepared (index : Fin 2) : equationInputs Bindings.empty (bodyDepth + 9) (request index) = [request index] := by
  fin_cases index <;> decide +kernel

theorem query_evidence (index : Fin 2) :
    EquationBodyEvidence context live query Atom.undefinedType Bindings.empty (request index) (request index) .semantic := by
  apply EquationBodyEvidence.of_open_query_at (fuel := bodyDepth + 9) (index.val + 3) query (nested "public")
  · fin_cases index <;> rfl
  · fin_cases index <;> decide +kernel
  · fin_cases index <;> decide +kernel
  · rw [prepared]; exact List.mem_singleton_self _
  · fin_cases index <;> decide +kernel

theorem selected_request {candidate input : ResultPair}
    (member : candidate ∈ equationCandidates context live query Atom.undefinedType Bindings.empty (bodyDepth + 9))
    (present : input ∈ equationInputs Bindings.empty (bodyDepth + 9) candidate) :
    ∃ index : Fin 2, candidate = request index ∧ input = request index := by
  rw [queried] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · subst candidate
    rw [prepared] at present
    exact ⟨0, rfl, List.mem_singleton.mp present⟩
  · subst candidate
    rw [prepared] at present
    exact ⟨1, rfl, List.mem_singleton.mp present⟩

theorem received (index : Fin 2) :
    ∃ derived : ReturnDerivation context .semantic live query Atom.undefinedType (request index).1
      (request index).2 (bodyDepth + 9) (responses (request index)), derived.Covered := by
  obtain ⟨child, childCovered⟩ := nested_derived index
  have accepted : nested (key index) ≠ Atom.notReducible := by simp [nested, Atom.notReducible]
  have running : ¬IsEmptyOrErrorRel (nested (key index)) := by
    simp [nested, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  rw [responses_index]
  let derived := ReturnDerivation.evaluate live query Atom.undefinedType (nested (key index)) Bindings.empty
    (bodyDepth + 9) [(final, bindings index)] accepted running child
  exact ⟨derived, .evaluate (accepted := accepted) (running := running) (child := child) childCovered⟩

theorem call_derived :
    ∃ derived : CallDerivation context .semantic live query Atom.undefinedType Bindings.empty
      (bodyDepth + 10) answers, derived.Covered := by
  have evidence : ∀ candidate ∈ equationCandidates context live query Atom.undefinedType Bindings.empty (bodyDepth + 9),
      ∀ input ∈ equationInputs Bindings.empty (bodyDepth + 9) candidate,
      EquationBodyEvidence context live query Atom.undefinedType Bindings.empty candidate input .semantic := by
    intro candidate member input present
    obtain ⟨index, rfl, rfl⟩ := selected_request member present
    exact query_evidence index
  have producers : ∀ candidate ∈ equationCandidates context live query Atom.undefinedType Bindings.empty (bodyDepth + 9),
      ∀ input ∈ equationInputs Bindings.empty (bodyDepth + 9) candidate,
      ProducedDerivation context .semantic (Atom.undefinedType :: live) (some query)
        input.1 input.2 (bodyDepth + 9) [input] := by
    intro candidate member input present
    obtain ⟨index, rfl, rfl⟩ := selected_request member present
    exact .raw _ _ _ _ (bodyDepth + 8) (by simp [request, nested, Minimal.IsFunction])
  have receivers : ∀ candidate ∈ equationCandidates context live query Atom.undefinedType Bindings.empty (bodyDepth + 9),
      ∀ input ∈ equationInputs Bindings.empty (bodyDepth + 9) candidate, ∀ produced ∈ [input],
      ∃ derived : ReturnDerivation context .semantic live query Atom.undefinedType produced.1 produced.2
        (bodyDepth + 9) (responses produced), derived.Covered := by
    intro candidate member input present produced appeared
    obtain rfl := List.mem_singleton.mp appeared
    obtain ⟨index, rfl, rfl⟩ := selected_request member present
    exact received index
  choose returns returnsCovered using receivers
  have selected : rawQueryResults context query Atom.undefinedType Bindings.empty (bodyDepth + 9) live ≠ [] := by
    decide +kernel
  let derived := CallDerivation.equations live "make" [] Atom.undefinedType Bindings.empty (bodyDepth + 9)
    (fun _ input => [input]) (fun _ _ => responses) (by decide) (by decide) (by decide)
    selected evidence producers returns
  have covered : derived.Covered := CallDerivation.Covered.equations
    (ordinary := by decide) (nonembedded := by decide) (clean := by decide) (selected := selected)
    (evidence := evidence) (producers := producers) (bodies := returns)
    (by decide +kernel)
    (by
      intro candidate member
      change candidate ∈ equationCandidates context live query Atom.undefinedType Bindings.empty (bodyDepth + 9) at member
      rw [queried] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> constructor
      · decide +kernel
      · intro merged present acyclic
        have same : merged = Bindings.empty := by
          change merged ∈ [Bindings.empty] at present
          exact List.mem_singleton.mp present
        subst merged
        decide +kernel
      · decide +kernel
      · intro merged present acyclic
        have same : merged = Bindings.empty := by
          change merged ∈ [Bindings.empty] at present
          exact List.mem_singleton.mp present
        subst merged
        decide +kernel)
    returnsCovered
  have rows := queried
  dsimp only [query] at rows
  have output :
      ((equationCandidates context live (.expression [.symbol "make"]) Atom.undefinedType Bindings.empty (bodyDepth + 9)).flatMap
        fun candidate => (equationInputs Bindings.empty (bodyDepth + 9) candidate).flatMap
          fun input => [input].flatMap responses) = answers := by
    simp only [rows, prepared, List.flatMap_cons, List.flatMap_nil, responses_index,
      List.append_nil, List.cons_append, List.nil_append, answers]
  rw [← output]
  exact ⟨derived, covered⟩

theorem full_derived :
    ∃ derived : AtomDerivation context .semantic live query Atom.undefinedType Bindings.empty
      (bodyDepth + 12) answers, derived.Covered := by
  obtain ⟨call, callCovered⟩ := call_derived
  have actual := single_arrow_derivation context "make" [] [] Atom.undefinedType Atom.undefinedType
    Bindings.empty (bodyDepth + 9) [([], Bindings.empty)] (fun _ => answers) live
    (by decide +kernel) .nil (by decide +kernel) rfl rfl (Or.inl rfl)
    (by decide +kernel) rfl (by decide +kernel) (by decide) (by decide) (by decide) (by decide)
    (.nil _ _ (bodyDepth + 8)) .nil
    (by intro request member; obtain rfl := List.mem_singleton.mp member; exact call)
    (by intro request member; obtain rfl := List.mem_singleton.mp member; exact callCovered)
  exact actual

/-- An ordinary emitted equation result is recursively interpreted through two
actual typed application nodes. Its inner function writes once and keeps both
uses, while duplicate physical declarations remain two result occurrences. -/
theorem nested_source_and_checked_path :
    Covered.Realizes context (.atom query Atom.undefinedType Bindings.empty (bodyDepth + 12) live) answers ∧
    ∀ result ∈ answers, ∀ scope input,
      SourceBindingComparison.semantic.FrameRelated Bindings.empty input →
      ∃ output, EvalAtomRawRel context noHost live (protectedScope := scope)
        query Atom.undefinedType input (result.1, output) ∧
        SourceBindingComparison.semantic.FrameRelated result.2 output := by
  obtain ⟨derived, covered⟩ := full_derived
  exact ⟨derived.covered_realizes covered, fun result member scope input related =>
    derived.sound result member scope input related⟩

theorem physical_duplicates_and_two_uses :
    context.atoms[3]? = some rule ∧ context.atoms[4]? = some rule ∧
    answers.length = 2 ∧ bindings 0 ≠ bindings 1 ∧
    (bindings 0).lookup (key 0) = some value ∧ (bindings 1).lookup (key 1) = some value ∧
    final = .expression [.symbol "box", .expression [.symbol "Pair", value, value]] := by decide +kernel

theorem nested_independent_source (index : Fin 2) :
    ∃ output, EvalAtomRawRel context noHost live query Atom.undefinedType
      PrincipalBindingFrame.empty.sourceFrame (final, output) ∧
      SourceBindingComparison.semantic.FrameRelated (bindings index) output :=
  nested_source_and_checked_path.2 (final, bindings index)
    (by fin_cases index <;> simp [answers]) [] PrincipalBindingFrame.empty.sourceFrame
    (.of_principal PrincipalBindingFrame.empty (.refl _))

theorem nested_checked_completion (earned : ResultSet) :
    ∃ budget, ∀ later, (Checked.machine HE.GroundedDispatch.none).run (budget + later)
      ⟨context, .work (.atom query Atom.undefinedType Bindings.empty (bodyDepth + 12) live), [], earned⟩ =
      (answers, .finished ⟨context, .returning [], [], earned ++ answers⟩) :=
  Covered.realizes_completed nested_source_and_checked_path.1 earned

theorem duplicate_cannot_be_collapsed (budget : Nat) (finished : Configuration)
    (ran : (Checked.machine HE.GroundedDispatch.none).run budget
      ⟨context, .work (.atom query Atom.undefinedType Bindings.empty (bodyDepth + 12) live), [], []⟩ =
      ([(final, bindings 0)], .finished finished)) : False := by
  have exactOutput := realizes_completed_unique (Covered.unchecked nested_source_and_checked_path.1)
    [] [(final, bindings 0)] budget finished
    (Checked.finished_refines HE.GroundedDispatch.none budget _ _ finished ran)
  have different : [(final, bindings 0)] ≠ answers := by decide +kernel
  exact different exactOutput.1

theorem reached_bindings_cannot_be_erased (budget : Nat) (finished : Configuration)
    (ran : (Checked.machine HE.GroundedDispatch.none).run budget
      ⟨context, .work (.atom query Atom.undefinedType Bindings.empty (bodyDepth + 12) live), [], []⟩ =
      ([(final, Bindings.empty), (final, Bindings.empty)], .finished finished)) : False := by
  have exactOutput := realizes_completed_unique (Covered.unchecked nested_source_and_checked_path.1)
    [] [(final, Bindings.empty), (final, Bindings.empty)] budget finished
    (Checked.finished_refines HE.GroundedDispatch.none budget _ _ finished ran)
  have different : [(final, Bindings.empty), (final, Bindings.empty)] ≠ answers := by decide +kernel
  exact different exactOutput.1

theorem raw_demand_still_holds_nested_calls (index : Fin 2) :
    Covered.Realizes context (.atom (nested (key index)) Atom.atomType Bindings.empty 1 live)
      [(nested (key index), Bindings.empty)] := by
  have leaf := AtomDerivation.leaf (space := context) (comparison := .semantic) live (nested (key index))
    Atom.atomType Bindings.empty 0 (Or.inr ⟨Atom.expressionType, .expression _, Or.inl rfl⟩)
  exact leaf.covered_realizes (.leaf (leaf := Or.inr ⟨Atom.expressionType, .expression _, Or.inl rfl⟩))

theorem old_fallback_restriction_really_excluded_function :
    Minimal.embeddedInstruction (.expression [.symbol "function"]) = true := rfl

def initial : Configuration :=
  ⟨context, .work (.atom query Atom.undefinedType Bindings.empty (bodyDepth + 12) live), [], []⟩

def innerScope : List Atom := .symbol "box" :: Atom.atomType :: live

def afterWrite : Configuration :=
  ⟨context, .work (.bodyResults (bodyDepth - 1) []
      (block (key 0) :: Atom.atomType :: innerScope) (some (block (key 0)))),
    [.prepend (raw 0), .functionTerminal none,
     .invocationReturn (.ordinary Atom.atomType) (block (key 0)) (bodyDepth + 2) innerScope,
     .append (.calls Atom.atomType (bodyDepth + 3) [] innerScope),
     .append (.bindingAlternatives (block (key 0)) (arrow [Atom.atomType] Atom.atomType)
       Atom.atomType (bodyDepth + 3) [] innerScope), .filter,
     .argumentHeads (block (key 0)) [] [] (bodyDepth + 5) innerScope,
     .functionTail (.symbol "box"),
     .append (.heads (arrow [Atom.undefinedType] Atom.atomType) [block (key 0)]
       (bodyDepth + 6) [] (Atom.atomType :: live)),
     .calls Atom.atomType (bodyDepth + 7) live,
     .append (.bindingAlternatives (nested (key 0)) (arrow [Atom.undefinedType] Atom.atomType)
       Atom.atomType (bodyDepth + 7) [] live), .filter,
     .append (.returns query Atom.undefinedType (bodyDepth + 9) [request 1] live),
     .append (.calls Atom.undefinedType (bodyDepth + 10) [] live),
     .append (.bindingAlternatives query (arrow [] Atom.undefinedType) Atom.undefinedType
       (bodyDepth + 10) [] live), .filter], []⟩

/-- The physical continuation contains the first changed frame, the typed
receiver, its outer argument receiver and the second occurrence still pending. -/
theorem nested_checkpoint_after_write :
    (Checked.machine HE.GroundedDispatch.none).run 80 initial = ([], .exhausted afterWrite) := by rfl

theorem saved_scope_caller_and_remaining_occurrence :
    afterWrite.space = context ∧
    afterWrite.control = .work (.bodyResults (bodyDepth - 1) []
      (block (key 0) :: Atom.atomType :: innerScope) (some (block (key 0)))) ∧
    Frame.prepend (raw 0) ∈ afterWrite.stack ∧
    Frame.invocationReturn (.ordinary Atom.atomType) (block (key 0)) (bodyDepth + 2) innerScope ∈ afterWrite.stack ∧
    Frame.append (.returns query Atom.undefinedType (bodyDepth + 9) [request 1] live) ∈ afterWrite.stack := by
  decide +kernel

theorem saved_nested_receiver_resumes_exactly :
    ∃ budget remaining, (Checked.machine HE.GroundedDispatch.none).run budget afterWrite =
      (remaining, .finished ⟨context, .returning [], [], answers⟩) ∧ remaining = answers := by
  simpa only [List.nil_append] using
    Covered.completes_saved nested_source_and_checked_path.1 [] 80 [] afterWrite nested_checkpoint_after_write

theorem checkpoint_is_not_completed_empty (finished : Configuration) :
    (Checked.machine HE.GroundedDispatch.none).run 80 initial ≠ ([], .finished finished) := by
  rw [nested_checkpoint_after_write]
  intro same
  cases same

theorem nested_path_preserves_arbitrary_saved_stack (stack : List Frame) (earned : ResultSet) :
    Covered.SilentPath
      ⟨context, .work (.atom query Atom.undefinedType Bindings.empty (bodyDepth + 12) live), stack, earned⟩
      ⟨context, .returning answers, stack, earned⟩ :=
  nested_source_and_checked_path.1 stack earned

theorem conflicting_binding_is_not_silently_overwritten :
    unifyMatchesCovered value (.var (key 0)) (Bindings.empty.assign (key 0) (.symbol "Other")) (bodyDepth - 3) = true ∧
    unifySuccessResults value (.var (key 0)) (template (key 0))
      (Bindings.empty.assign (key 0) (.symbol "Other")) (bodyDepth - 3) = [] := by decide +kernel

theorem zero_depth_still_suspends :
    (Checked.machine HE.GroundedDispatch.none).run 1
      ⟨context, .work (.atom query Atom.undefinedType Bindings.empty 0 live), [], []⟩ =
      ([], .suspended .evaluationDepth
        ⟨context, .work (.atom query Atom.undefinedType Bindings.empty 0 live), [], []⟩) := rfl
end Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness.TypedInvocation.NestedControls

end RecursiveTypedApplicationControls
