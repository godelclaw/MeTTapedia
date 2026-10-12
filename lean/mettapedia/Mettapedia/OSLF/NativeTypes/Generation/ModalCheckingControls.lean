import Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingLaws
import Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer
import Mettapedia.OSLF.NativeTypes.Generation.ModalFormation

open Mettapedia.OSLF.Framework

/-!
# Scoped beta as a generated specified-contractum query

The root schema is read from the actual generated catalogue. Its dependent
continuation checks the complete captured body and argument as well as the
declared result carrier. The full query executes beta, returns its actual
receipt, and remains unknown when paused before that event is discovered.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules Mettapedia.OSLF.NativeTypes.Modal.Formation Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer (generated source target body argument term)

theorem actual_equation_admission : generated.equationAdmission = some true := by
  change Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled?
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.compileLaws Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.chosen.language
      (selectedEquationLaws Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.chosen.language {}))
    Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.vertex.2 = some true
  have empty : Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.chosen.language.equations = [] := by
    rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.chosen_language]
    rfl
  have noLaws : selectedEquationLaws Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.chosen.language {} = [] := by
    simp [selectedEquationLaws, Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.equationLaws, empty]
  rw [noLaws]
  rfl

theorem actual_catalogue : generated.modalCatalogue = schemas generated.plan := by
  change (if (generated.equationAdmission != some false) && generated.logicFragment.core.modal
    then schemas generated.plan else []) = _
  have accepted : (generated.equationAdmission != some false) = true := by
    rw [actual_equation_admission]
    rfl
  simp only [accepted]
  rfl

theorem catalogue_nonempty : 0 < generated.modalCatalogue.length := by
  have lengths := (congrArg List.length actual_catalogue).trans
    (congrArg (fun plan => (schemas plan).length) Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtime_plan_actual)
  have present : 0 < (schemas Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtimePlan).length := by decide +kernel
  exact lengths.symm ▸ present

def schema : Schema generated.plan := generated.modalCatalogue[0]'catalogue_nonempty

theorem computed_schema_shape : schema.position = [] ∧ schema.bound = [] ∧
    schema.focusBound = [] ∧ schema.focusCarrier = term ∧ schema.programCarrier = term ∧
    schema.relyNames = [] ∧ schema.declaration = Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.declaration := by
  cbv

def parameters : ModalParameters schema :=
  (generated.modalParameters? schema).get (by cbv)

theorem actual_parameters : generated.modalParameters? schema = some parameters :=
  (Option.some_get _).symm

def supplied : ScopedRuleMatching.Assignment :=
  [("A", ⟨[], 0, argument⟩), ("B", ⟨[term], 0, body⟩)]

def relyCodes : RelyCodes schema parameters.inputs := fun name => by
  have absent := name.property
  simp only [computed_schema_shape.2.2.2.2.2.1, List.not_mem_nil] at absent

def continuationCode (assignment : ScopedRuleMatching.Assignment) :
    TypeCode generated.plan schema.bound schema.programCarrier parameters.output where
  meaning result :=
    checkOpenPatternWellSorted generated.plan.snapshot.language generated.plan.snapshot.free
      schema.bound schema.programCarrier result = true ∧
    ScopedRuleMatching.lookup assignment "A" = some ⟨[], 0, argument⟩ ∧
    ScopedRuleMatching.lookup assignment "B" = some ⟨[term], 0, body⟩
  bounded _ valid := (checkOpenPatternWellSorted_sound valid.1).1

def codes : ModalInstanceCodes generated schema :=
  ⟨parameters, actual_parameters, relyCodes, continuationCode⟩

def decisions : ModalInstanceDecisions codes where
  rely name _ := by
    have absent := name.property
    simp only [computed_schema_shape.2.2.2.2.2.1, List.not_mem_nil] at absent
  continuation assignment result := by
    change Decidable (checkOpenPatternWellSorted generated.plan.snapshot.language generated.plan.snapshot.free
      schema.bound schema.programCarrier result = true ∧
      ScopedRuleMatching.lookup assignment "A" = some ⟨[], 0, argument⟩ ∧
      ScopedRuleMatching.lookup assignment "B" = some ⟨[term], 0, body⟩)
    infer_instance

theorem selected_former_is_actual : (generated.modalFormer? schema codes.actualInputs).isSome = true := by
  unfold Generated.modalFormer?
  rw [if_pos ⟨actual_equation_admission, rfl,
    generated_schema_admitted (List.getElem_mem catalogue_nonempty)⟩]
  split
  · rename_i absent
    rw [actual_parameters] at absent
    cases absent
  · rfl

theorem source_filling : schema.fill? supplied source = some source := by
  simp only [Schema.fill?, computed_schema_shape.1, Mettapedia.OSLF.NativeTypes.Modal.Instantiation.fill?]

theorem actual_rhs : schema.rhs? supplied = some target := by
  simp only [Schema.rhs?, Schema.operation, computed_schema_shape.2.2.2.2.2.2,
    computed_schema_shape.2.1]
  cbv

theorem checked_assignment : checkInstanceRequest codes decisions supplied = true := by
  have typed : GeneralPremise.checkTypedAssignment (GeneralPlanEnvironment.environment generated.plan)
      schema.context supplied = true := by
    unfold Schema.context
    rw [computed_schema_shape.2.2.2.2.2.2, computed_schema_shape.2.1]
    dsimp only [GeneralPremise.checkTypedAssignment]
    rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtime_plan_actual]
    cbv
  have relies : checkInstanceRely codes decisions supplied = true := by
    simp [checkInstanceRely, computed_schema_shape.2.2.2.2.2.1]
  have names : checkInstanceNames schema supplied = true := by
    unfold checkInstanceNames
    rw [computed_schema_shape.2.2.2.2.2.2]
    cbv
  simp only [checkInstanceRequest, typed, relies, names, Bool.true_and]

theorem checked_focus : checkOpenPatternWellSorted generated.plan.snapshot.language generated.plan.snapshot.free
    schema.focusBound schema.focusCarrier source = true := by
  rw [computed_schema_shape.2.2.1, computed_schema_shape.2.2.2.1]
  rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtime_plan_actual]
  decide +kernel

def instanceRequest : ModalInstanceRequest codes supplied source where
  source := source
  target := target
  filling := source_filling
  rhs := actual_rhs
  sourceCanonical := by decide +kernel
  targetCanonical := by decide +kernel
  carrier := (checkOpenPatternWellSorted_sound checked_focus).1
  typedRequest := check_instance_request_sound checked_assignment

theorem request_admitted : admitModalInstance? codes decisions supplied source = .ok instanceRequest := by
  unfold admitModalInstance?
  split
  · rename_i missing
    rw [source_filling] at missing
    cases missing
  · rename_i actual filling
    have same : actual = source := Option.some.inj (filling.symm.trans source_filling)
    subst actual
    split
    · rename_i missing
      rw [actual_rhs] at missing
      cases missing
    · rename_i actual right
      have same : actual = target := Option.some.inj (right.symm.trans actual_rhs)
      subst actual
      have sourceCanonical : source.hasCanonicalBinderMetadata = true := instanceRequest.sourceCanonical
      have targetCanonical : target.hasCanonicalBinderMetadata = true := instanceRequest.targetCanonical
      rw [dif_pos sourceCanonical, dif_pos targetCanonical,
        dif_pos checked_focus, dif_pos checked_assignment]
      rfl

open GeneralOccurrenceFrontier

def sourceState (budget : Nat) : State instanceRequest.sourceRequest :=
  run instanceRequest.sourceRequest budget (start instanceRequest.sourceRequest)

def targetState (budget : Nat) : State instanceRequest.targetRequest :=
  run instanceRequest.targetRequest budget (start instanceRequest.targetRequest)

theorem source_request_actual : instanceRequest.sourceRequest = Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.request := by
  change generated.request schema.bound schema.programCarrier source = generated.request [] term source
  rw [computed_schema_shape.2.1, computed_schema_shape.2.2.2.2.1]

theorem source_readouts_actual (budget : Nat) :
    (sourceState budget).answers.map (fun answer => Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.rawReadout answer.val) =
      Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.readouts Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.request budget :=
  congrArg (fun request => Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.readouts request budget) source_request_actual

theorem source_one_answer : (sourceState 40).answers.length = 1 := by
  have reads := (source_readouts_actual 40).trans Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.actual_beta_readout
  have counts := congrArg List.length reads
  simpa only [List.length_map, List.length_singleton] using counts

def actualAnswer : Answer instanceRequest.sourceRequest :=
  (sourceState 40).answers[0]'(by rw [source_one_answer]; decide)

theorem actual_answer_readout : Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.rawReadout actualAnswer.val =
    Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.expectedReadout := by
  have member : Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.rawReadout actualAnswer.val ∈
      (sourceState 40).answers.map (fun answer => Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.rawReadout answer.val) :=
    List.mem_map.mpr ⟨actualAnswer, List.getElem_mem _, rfl⟩
  rw [source_readouts_actual, Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.actual_beta_readout] at member
  exact List.mem_singleton.mp member

theorem actual_answer_target : actualAnswer.val.target = target :=
  congrArg Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.Readout.target actual_answer_readout

theorem accepts_continuation : (codes.inputs.2 supplied).meaning instanceRequest.target := by
  change (continuationCode supplied).meaning target
  change checkOpenPatternWellSorted generated.plan.snapshot.language generated.plan.snapshot.free
    schema.bound schema.programCarrier target = true ∧ _
  rw [computed_schema_shape.2.1, computed_schema_shape.2.2.2.2.1]
  rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtime_plan_actual]
  decide +kernel

theorem actual_response_found : (checkModalResponse? decisions instanceRequest (targetState 0) actualAnswer).isSome = true := by
  apply Option.isSome_iff_exists.mpr
  apply modal_response_exists instanceRequest decisions (targetState 0) actualAnswer
  · apply Option.isSome_iff_exists.mp
    have same : instanceRequest.target = actualAnswer.val.target := actual_answer_target.symm
    simp only [contractumPath?, dif_pos same, Option.isSome_some]
  · exact accepts_continuation

def response : CheckedModalInstance instanceRequest :=
  (checkModalResponse? decisions instanceRequest (targetState 0) actualAnswer).get actual_response_found

theorem response_in_actual_results : response ∈ modalResponses decisions instanceRequest (sourceState 40) (targetState 0) :=
  List.mem_filterMap.mpr ⟨actualAnswer, List.getElem_mem _, (Option.some_get actual_response_found).symm⟩

def actualRun (budget conversionBudget : Nat) : ModalInstanceRun codes supplied source :=
  {request := instanceRequest, sourceState := sourceState budget, targetState := targetState conversionBudget,
    responses := modalResponses decisions instanceRequest (sourceState budget) (targetState conversionBudget),
    result := modalInstanceReadout decisions instanceRequest (sourceState budget) (targetState conversionBudget)}

theorem actual_generated_run (budget conversionBudget : Nat) :
    generated.checkModalInstance schema codes decisions supplied source budget conversionBudget =
      .ok (actualRun budget conversionBudget) := by
  unfold Generated.checkModalInstance
  rw [selected_former_is_actual]
  simp only [ite_true, request_admitted]
  rfl

theorem actual_generated_beta_query : (actualRun 40 0).result = .decided true := by
  change modalInstanceReadout decisions instanceRequest (sourceState 40) (targetState 0) = .decided true
  cases results : modalResponses decisions instanceRequest (sourceState 40) (targetState 0) with
  | nil =>
    have member := response_in_actual_results
    rw [results] at member
    exact False.elim (List.not_mem_nil member)
  | cons head tail => simp [modalInstanceReadout, results]

theorem zero_source_unfinished : complete instanceRequest.sourceRequest (sourceState 0) = false := by
  have equality := congrArg (fun request => complete request (run request 0 (start request))) source_request_actual
  change complete instanceRequest.sourceRequest (run instanceRequest.sourceRequest 0 (start instanceRequest.sourceRequest)) = false
  rw [equality, Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.actual_request, Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.literal_start]
  rfl

theorem zero_source_silent : (sourceState 0).answers = [] := by
  apply List.eq_nil_iff_length_eq_zero.mpr
  have counts := congrArg List.length (source_readouts_actual 0)
  change (sourceState 0).answers.length = 0
  rw [List.length_map] at counts
  have silent : (Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.readouts Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.request 0).length = 0 := by
    unfold Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.readouts
    rw [List.length_map]
    exact Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.zero_budget_has_no_answer
  exact counts.trans silent

theorem zero_budget_instance_unknown : (actualRun 0 0).result = .unknown :=
  unfinished_empty_instance_unknown instanceRequest decisions (sourceState 0) (targetState 0)
    zero_source_silent zero_source_unfinished accepts_continuation

theorem specified_beta_rhs : response.outcome.target = target := response.targetAgreement

theorem full_assignment_continuation :
    (continuationCode supplied).meaning response.outcome.target := response.outcome.certificate.down

theorem actual_receipt_is_preserved : response.outcome.receipt = actualAnswer.val := by
  generalize storedEq : response = stored
  have computed : checkModalResponse? decisions instanceRequest (targetState 0) actualAnswer = some stored :=
    (Option.some_get actual_response_found).symm.trans (congrArg some storedEq)
  unfold checkModalResponse? at computed
  split at computed
  · cases computed
  · split at computed
    · cases Option.some.inj computed
      rfl
    · cases computed

theorem original_beta_declaration : response.outcome.receipt.firing.job.declaration.declarationIndex = 0 := by
  rw [actual_receipt_is_preserved]
  exact congrArg Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.Readout.declarationIndex actual_answer_readout

theorem actual_beta_captures :
    ScopedRuleMatching.lookup response.outcome.receipt.firing.completed "B" = some ⟨[term], 0, body⟩ ∧
    ScopedRuleMatching.lookup response.outcome.receipt.firing.completed "A" = some ⟨[], 0, argument⟩ := by
  rw [actual_receipt_is_preserved]
  exact ⟨congrArg Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.Readout.body actual_answer_readout,
    congrArg Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.Readout.argument actual_answer_readout⟩

theorem primitive_count : response.outcome.history.length = 1 :=
  Mettapedia.OSLF.NativeTypes.Modal.NativeEvidence.primitive_history_count response.outcome

end Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls
