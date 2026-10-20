import Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeIntroduction
import Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeTransport
import Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls
import Mathlib.Tactic.FinCases

open Mettapedia.OSLF.Framework

/-!
# A proper native sort model for the generated scoped lambda calculus

The two subobjects distinguish typed variable syntax from typed compound
syntax. Native App and Lam introduction preserve the generated star output;
the box subobject still contains actual bound variables. The scoped beta
family is introduced by the computed matcher for every compatible complete
assignment, and its continuation reads the retained body and argument.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Sorted.LambdaControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules Mettapedia.OSLF.NativeTypes.Modal.Formation
open Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeIntroduction
open Mettapedia.OSLF.NativeTypes.SortProfiles.Source (LeafCodes Code ClassifiedCode)
open Mettapedia.OSLF.NativeTypes.Generation (structuralDeclaration structuralOutputSort structuralInputSort)
open Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer (generated source target body argument term)
open ModalHypercube (HSort)

open Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls (schema parameters supplied codes instanceRequest actual_parameters
  computed_schema_shape actual_equation_admission actual_rhs catalogue_nonempty)

def syntaxSort : Pattern → HSort
  | .bvar _ | .fvar _ => .box
  | _ => .star

def model : Model generated := fun bound =>
  {sortDomain := fun carrier sort native =>
    HasType generated.snapshot.language generated.snapshot.free bound native carrier ∧ syntaxSort native = sort
   carrierBounded := fun _ _ _ inhabited => inhabited.1}

theorem native_constructor_model : OperationClosed model := by
  intro bound index value _inputs
  refine ⟨value.typed (List.getElem_mem _), ?_⟩
  have output : structuralOutputSort generated index = .star := rfl
  rw [output]
  cases value <;> rfl

theorem native_equation_model : EquationsInterpreted model := by
  intro bound carrier sort first receipt complete
  have impossible := complete.job.1
  rw [Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtime_plan_actual] at impossible
  exact False.elim (List.not_mem_nil impossible)

theorem native_equation_sort_invariance (bound : List TypeExpr) (carrier : TypeExpr) (sort : HSort)
    {first second : Pattern}
    (related : Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound carrier) first second) :
    (model bound).sortDomain carrier sort first ↔ (model bound).sortDomain carrier sort second :=
  equation_sort_transport native_equation_model bound carrier sort related

theorem proper_sort_domains :
    (model [term]).sortDomain term .box (.bvar 0) ∧
      ¬ (model [term]).sortDomain term .star (.bvar 0) ∧
      (model []).sortDomain term .star source ∧
      ¬ (model []).sortDomain term .box source := by
  refine ⟨⟨.bvar rfl, rfl⟩, ?_, ⟨Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.source_is_typed.1, rfl⟩, ?_⟩
  · intro same
    cases same.2
  · intro same
    cases same.2

theorem dependent_lambda_is_in_star :
    (model []).sortDomain (.arrow term term) .star (.lambda none (.bvar 0)) :=
  ⟨.lambda (.bvar rfl), rfl⟩

def function : Pattern := .apply "Lam" [.lambda none body]

def component (index : Nat) : Pattern := if index = 0 then function else argument

theorem component_typed (index : Nat) :
    HasType generated.snapshot.language generated.snapshot.free schema.focusBound (component index) term := by
  rw [computed_schema_shape.2.2.1]
  unfold component
  split <;> exact (checkHasType_sound (by decide +kernel))

def leaves : LeafCodes generated schema.focusBound := fun index =>
  ⟨term, .star,
    {
      meaning := fun native => native = component index
      bounded := fun _native equal => equal.symm ▸ component_typed index
    }⟩

theorem leaf_interpretation (index : Nat) (native : Pattern)
    (inhabited : (leaves index).2.2.meaning native) :
    (model schema.focusBound).sortDomain (leaves index).1 (leaves index).2.1 native := by
  change native = component index at inhabited
  subst native
  refine ⟨component_typed index, ?_⟩
  unfold component
  split <;> rfl

def appIndex : Fin generated.snapshot.language.terms.length := ⟨0, by decide +kernel⟩

def focusExpression : Code generated.snapshot.language :=
  .constructor appIndex (fun position => .variableCode position.val)

theorem focus_carrier :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Carries (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.leafCarriers leaves)
      focusExpression schema.focusCarrier := by
  rw [computed_schema_shape.2.2.2.1]
  change Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Carries _ (.constructor appIndex _) (.base "Term")
  apply Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Carries.constructor
  intro position
  have small : position.val < 2 := position.isLt
  fin_cases position <;> exact .variableCode _

theorem focus_universe :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Kinded generated.vertex.2 (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.leafSorts leaves)
      focusExpression parameters.output := by
  have output : parameters.output = .star := by cbv
  rw [output]
  change Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Kinded _ _ (.constructor appIndex _) .star
  apply Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Kinded.constructor
  intro position
  exact .variableCode _

def focusCode : ClassifiedCode generated schema.focusBound leaves schema.focusCarrier parameters.output :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Source.classify focusExpression focus_carrier focus_universe

def sourceValue : Mettapedia.OSLF.NativeTypes.Structural.ConstructorValue generated.snapshot.language generated.snapshot.free
    schema.focusBound (structuralDeclaration generated appIndex) :=
  .ordinary [function, argument] (by
    rintro ⟨name, kind, elementType, shape⟩
    have impossible := congrArg List.length shape
    change 2 = 1 at impossible
    omega)
    (.cons trivial rfl (component_typed 0) (.cons trivial rfl (component_typed 1) .nil))

theorem actual_focus_reading : focusCode.code.meaning source := by
  change HasType _ _ _ source (.base "Term") ∧ _
  refine ⟨?_, sourceValue, .refl _, ?_⟩
  · rw [computed_schema_shape.2.2.1]
    exact Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.source_is_typed.1
  · intro position
    fin_cases position <;> rfl

theorem actual_focus_in_model :
    (model schema.focusBound).sortDomain schema.focusCarrier parameters.output source :=
  classified_code_in_model native_constructor_model native_equation_model leaf_interpretation
    focusCode actual_focus_reading

theorem actual_structural_compilation :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Source.compileEquationNativeCode generated schema.focusBound leaves focusExpression =
      .accepted ⟨schema.focusCarrier, parameters.output, focusCode⟩ :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Source.equation_native_code_accepts rfl actual_equation_admission focus_carrier focus_universe

theorem matched_variables : schema.matchedNames = ["B", "A"] := by cbv

theorem compatible_reads {A : String → ContextualValue → Prop} {assignment : Assignment}
    (request : TypedRequest schema A supplied assignment) :
    lookup assignment "A" = some ⟨[], 0, argument⟩ ∧
      lookup assignment "B" = some ⟨[term], 0, body⟩ := by
  refine ⟨?_, ?_⟩
  · exact (request.2.2.1 "A" (by rw [matched_variables]; simp)).trans (by rfl)
  · exact (request.2.2.1 "B" (by rw [matched_variables]; simp)).trans (by rfl)

theorem anchor_present : ∀ name ∈ schema.matchedNames,
    ∃ value, lookup supplied name = some value := by
  intro name member
  rw [matched_variables] at member
  rcases List.mem_cons.mp member with equal | tail
  · subst name
    exact ⟨⟨[term], 0, body⟩, rfl⟩
  · have equal := List.mem_singleton.mp tail
    subst name
    exact ⟨⟨[], 0, argument⟩, rfl⟩

theorem compatible_source_instance {assignment : Assignment}
    (reads : lookup assignment "A" = some ⟨[], 0, argument⟩ ∧
      lookup assignment "B" = some ⟨[term], 0, body⟩) :
    instantiateWith? schema.operation schema.declaration.rule schema.declaration.binding.spec
      schema.bound.length .left [] 0 assignment schema.declaration.rule.left = some source := by
  have operation : schema.operation = instantiateBVar := by
    unfold Schema.operation
    have reflection := congrArg (fun plan : GeneralExecutionAdmission.Plan => plan.permissions.reflection)
      Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtime_plan_actual
    rw [reflection, computed_schema_shape.2.2.2.2.2.2]
    rfl
  rw [operation, computed_schema_shape.2.2.2.2.2.2, computed_schema_shape.2.1]
  dsimp only [Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.declaration]
  change instantiateWith? instantiateBVar Mettapedia.GSLT.Examples.ScopedLamCongExecution.betaRule
    (Mettapedia.GSLT.Examples.ScopedLamCongExecution.betaRule.bindings.getD {dependencies := []})
    0 .left [] 0 assignment Mettapedia.GSLT.Examples.ScopedLamCongExecution.betaRule.left = some source
  simp only [Mettapedia.GSLT.Examples.ScopedLamCongExecution.betaRule, instantiateWith?, instantiateArgsWith?,
    reads.1, reads.2]
  rfl

theorem compatible_rhs {assignment : Assignment}
    (reads : lookup assignment "A" = some ⟨[], 0, argument⟩ ∧
      lookup assignment "B" = some ⟨[term], 0, body⟩) :
    schema.rhs? assignment = some target := by
  unfold Schema.rhs?
  have operation : schema.operation = instantiateBVar := by
    unfold Schema.operation
    have reflection := congrArg (fun plan : GeneralExecutionAdmission.Plan => plan.permissions.reflection)
      Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.runtime_plan_actual
    rw [reflection, computed_schema_shape.2.2.2.2.2.2]
    rfl
  rw [operation, computed_schema_shape.2.2.2.2.2.2, computed_schema_shape.2.1]
  dsimp only [Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.declaration]
  change instantiateWith? instantiateBVar Mettapedia.GSLT.Examples.ScopedLamCongExecution.betaRule
    (Mettapedia.GSLT.Examples.ScopedLamCongExecution.betaRule.bindings.getD {dependencies := []})
    0 .right [] 0 assignment Mettapedia.GSLT.Examples.ScopedLamCongExecution.betaRule.right = some target
  simp only [Mettapedia.GSLT.Examples.ScopedLamCongExecution.betaRule, instantiateWith?, reads.1, reads.2]
  cbv

theorem compatible_introductions {assignment : Assignment}
    (reads : lookup assignment "A" = some ⟨[], 0, argument⟩ ∧
      lookup assignment "B" = some ⟨[term], 0, body⟩) :
    Mettapedia.OSLF.NativeTypes.Modal.SourceIntroduction.baseIntroductions schema assignment [] =
      Mettapedia.OSLF.NativeTypes.Modal.SourceIntroduction.baseIntroductions schema supplied [] := by
  unfold Mettapedia.OSLF.NativeTypes.Modal.SourceIntroduction.baseIntroductions
  rw [compatible_source_instance reads, compatible_rhs reads,
    compatible_source_instance (assignment := supplied) ⟨rfl, rfl⟩, actual_rhs]

theorem actual_introduction_nonempty :
    Mettapedia.OSLF.NativeTypes.Modal.SourceIntroduction.baseIntroductions schema supplied [] ≠ [] := by
  cbv
  simp

def inputs := codes.inputs

def introduction : {_implementation : Evidence schema
      (relyMeaning (restrictRelyCodes model inputs.1))
      (continuationMeaning (restrictContinuations model inputs.2)) source //
    (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.GeneratedCodes.form model parameters actual_parameters inputs).code.meaning source} :=
  introduce native_constructor_model native_equation_model parameters actual_parameters inputs
    leaf_interpretation focusCode actual_focus_reading supplied instanceRequest.typedRequest.2.1
    anchor_present
    (fun assignment request => by
      rw [computed_schema_shape.1]
      exact .here (compatible_source_instance (compatible_reads request)))
    (fun _ _ => [])
    (fun assignment request => by
      rw [compatible_introductions (compatible_reads request)]
      exact actual_introduction_nonempty)
    (fun assignment request native rhs => by
      have reads := compatible_reads request
      have same : native = target := Option.some.inj (rhs.symm.trans (compatible_rhs reads))
      subst native
      refine ⟨⟨?_, ?_, reads.1, reads.2⟩⟩
      · refine ⟨?_, ?_⟩
        · rw [computed_schema_shape.2.1, computed_schema_shape.2.2.2.2.1]
          exact Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.target_is_typed.1
        · have output : parameters.output = .star := by cbv
          exact output.symm
      · rw [computed_schema_shape.2.1, computed_schema_shape.2.2.2.2.1]
        exact checkOpenPatternWellSorted_complete Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.target_is_typed)

theorem actual_generated_modal_inhabitant :
    (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.GeneratedCodes.form model parameters actual_parameters inputs).code.meaning source :=
  introduction.property

private theorem transport_roundtrip {α : Type} (family : α → Type)
    {first second : α} (equal : first = second) (value : family second) :
    equal ▸ (equal.symm ▸ value) = value := by
  cases equal
  rfl

theorem classified_modal_compilation :
    Mettapedia.OSLF.NativeTypes.Semantics.Sorted.GeneratedCodes.compile generated model schema codes.actualInputs =
      some ⟨parameters.output,
        Mettapedia.OSLF.NativeTypes.Semantics.Sorted.GeneratedCodes.form model parameters actual_parameters inputs⟩ := by
  unfold Mettapedia.OSLF.NativeTypes.Semantics.Sorted.GeneratedCodes.compile
  rw [if_pos ⟨actual_equation_admission, rfl,
    Mettapedia.OSLF.NativeTypes.Generation.generated_schema_admitted (List.getElem_mem catalogue_nonempty)⟩]
  split
  · rename_i absent
    rw [actual_parameters] at absent
    cases absent
  · rename_i actualParameters computed
    have same : actualParameters = parameters := Option.some.inj (computed.symm.trans actual_parameters)
    subst actualParameters
    have roundtrip : computed ▸ codes.actualInputs = inputs :=
      transport_roundtrip (Mettapedia.OSLF.NativeTypes.Generation.ModalInputs schema) computed inputs
    rw [roundtrip]

theorem all_compatible_modal_eliminations (assignment : Assignment)
    (request : TypedRequest schema (relyMeaning (restrictRelyCodes model inputs.1))
      introduction.val.anchor assignment) :
    let result := Mettapedia.OSLF.NativeTypes.Modal.NativeElimination.eliminate introduction.val assignment request
    schema.rhs? assignment = some result.native.2.1 ∧
      (GeneralOccurrenceSemantics.gslt generated.plan schema.bound schema.programCarrier).Step
        result.source result.native.2.1 ∧
      (model schema.bound).sortDomain schema.programCarrier parameters.output result.native.2.1 ∧
      lookup assignment "B" = some ⟨[term], 0, body⟩ ∧
      lookup assignment "A" = some ⟨[], 0, argument⟩ := by
  have contract := modal_m_step_elim introduction.val assignment request
  exact ⟨contract.2.1, contract.2.2.1, contract.2.2.2.1,
    contract.2.2.2.2.2.2, contract.2.2.2.2.2.1⟩

theorem modal_introduction_keeps_actual_history (assignment : Assignment)
    (request : TypedRequest schema (relyMeaning (restrictRelyCodes model inputs.1))
      introduction.val.anchor assignment) :
    (GeneralOccurrenceNativeReceipts.history generated.plan schema.bound schema.programCarrier
      (Mettapedia.OSLF.NativeTypes.Modal.NativeElimination.eliminate introduction.val assignment request).native.1).length = 1 :=
  Mettapedia.OSLF.NativeTypes.Modal.NativeElimination.elimination_primitive_count _

theorem actual_request : TypedRequest schema (relyMeaning (restrictRelyCodes model inputs.1))
    introduction.val.anchor supplied := by
  refine ⟨?_, instanceRequest.typedRequest.2⟩
  intro name present
  simp only [computed_schema_shape.2.2.2.2.2.1, List.not_mem_nil] at present

def expectedReceipt : GeneralOccurrenceSemantics.Receipt :=
  ⟨source, [],
    {job := ⟨0, Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.declaration,
       GeneralTypedSites.SiteData.here [] term source⟩
     matcherTrace := []
     captured := supplied
     completed := supplied
     premiseHistory := []
     localTarget := target
     target := target}⟩

theorem introduced_receipt_shape :
    (introduction.val.respond supplied actual_request).receipt = expectedReceipt := by
  cbv

def ruleReadout (rule : RewriteRule) :
    String × List (String × TypeExpr) × List Premise × Pattern × Pattern × Option RuleBindingSpec :=
  ⟨rule.name, rule.typeContext, rule.premises, rule.left, rule.right, rule.bindings⟩

theorem rule_readout_exact (first second : RewriteRule) : ruleReadout first = ruleReadout second ↔ first = second := by
  cases first
  cases second
  simp only [ruleReadout, Prod.mk.injEq, RewriteRule.mk.injEq]

/-- All primitive fields are checked. Empty administrative and premise paths
are checked separately from the retained declaration, zipper and captures. -/
def matchesExpectedReceipt (receipt : GeneralOccurrenceSemantics.Receipt) : Bool :=
  receipt.representative == source && receipt.conversions.isEmpty &&
    receipt.firing.job.ordinal == 0 &&
    receipt.firing.job.declaration.declarationIndex == Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.declaration.declarationIndex &&
    ruleReadout receipt.firing.job.declaration.authored == ruleReadout Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.declaration.authored &&
    receipt.firing.job.declaration.binding == Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.declaration.binding &&
    receipt.firing.job.site == GeneralTypedSites.SiteData.here [] term source &&
    receipt.firing.matcherTrace == [] && receipt.firing.captured == supplied &&
    receipt.firing.completed == supplied && receipt.firing.premiseHistory.isEmpty &&
    receipt.firing.localTarget == target && receipt.firing.target == target

theorem expected_receipt_checker_exact (receipt : GeneralOccurrenceSemantics.Receipt) :
    matchesExpectedReceipt receipt = true ↔ receipt = expectedReceipt := by
  cases receipt with
  | mk representative conversions firing =>
    cases firing with
    | mk job trace captured completed history localTarget actualTarget =>
      cases job with
      | mk ordinal declaration site =>
        cases declaration with
        | mk index authored binding =>
          simp [matchesExpectedReceipt, expectedReceipt, GeneralOccurrenceSemantics.Receipt.mk.injEq,
            GeneralRuleJobs.Receipt.mk.injEq, GeneralRuleJobs.Job.mk.injEq,
            rule_readout_exact, Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.declaration,
            GeneralExecutionAdmission.RulePlan.mk.injEq, and_assoc]

theorem actual_engine_receipt_shape :
    Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.actualAnswer.val = expectedReceipt := by
  have inventory : (Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.sourceState 40).answers.map
      (fun answer => matchesExpectedReceipt answer.val) = [true] := by
    change (GeneralOccurrenceFrontier.run instanceRequest.sourceRequest 40
      (GeneralOccurrenceFrontier.start instanceRequest.sourceRequest)).answers.map
        (fun answer => matchesExpectedReceipt answer.val) = _
    rw [Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.source_request_actual,
      Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.actual_request, Mettapedia.OSLF.NativeTypes.Instances.Lambda.GeneratorConsumer.literal_start]
    decide +kernel
  have member : matchesExpectedReceipt Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.actualAnswer.val ∈
      (Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.sourceState 40).answers.map
        (fun answer => matchesExpectedReceipt answer.val) :=
    List.mem_map.mpr ⟨Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.actualAnswer, List.getElem_mem _, rfl⟩
  rw [inventory] at member
  exact (expected_receipt_checker_exact _).mp (List.mem_singleton.mp member)

theorem introduced_receipt_is_actual_engine_receipt :
    (introduction.val.respond supplied actual_request).receipt =
      Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.actualAnswer.val :=
  introduced_receipt_shape.trans actual_engine_receipt_shape.symm

theorem actual_native_readout :
    let result := Mettapedia.OSLF.NativeTypes.Modal.NativeElimination.eliminate introduction.val supplied actual_request
    result.native.2.1 = target ∧
      result.native.1.val = Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingControls.actualAnswer.val ∧
      (model schema.bound).sortDomain schema.programCarrier parameters.output result.native.2.1 := by
  let result := Mettapedia.OSLF.NativeTypes.Modal.NativeElimination.eliminate introduction.val supplied actual_request
  have contract := modal_m_step_elim introduction.val supplied actual_request
  have same : result.native.2.1 = target := Option.some.inj (contract.2.1.symm.trans actual_rhs)
  exact ⟨same, introduced_receipt_is_actual_engine_receipt, contract.2.2.2.1⟩

end Mettapedia.OSLF.NativeTypes.Semantics.Sorted.LambdaControls
