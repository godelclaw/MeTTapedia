import Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Formation
import Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer

open Mettapedia.OSLF.Framework

/-!
# Classified modal formation for the original scoped COMM

The continuation schema and its rely coordinates come from the same generator
that executes the original rule without a collection remainder. Each rely
code reads its carrier and dependency context from that authored declaration.
The continuation is indexed by the complete scoped assignment and names its
specified right-hand-side instance.

Formation uses the equation center. The actual native receipt separately
justifies directed reduction, its current target and primitive history.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Source.RhoControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.SortProfiles.Source
open Mettapedia.OSLF.NativeTypes.Generation (ModalParameters ModalInputs)
open Mettapedia.OSLF.NativeTypes.Modal.Rules (Schema TypeCode)
open Mettapedia.OSLF.NativeTypes.Modal.Formation (RelyCode RelyIndex)
open Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer (generated continuationSchema)
open ModalHypercube (HSort)

theorem actual_equation_admission : generated.equationAdmission = some true := by
  change Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled?
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.compileLaws Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.chosen.language
      (Mettapedia.OSLF.NativeTypes.Generation.selectedEquationLaws Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.chosen.language
        Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityBinding.permissions)) Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.vertex.2 = some true
  have noLaws : Mettapedia.OSLF.NativeTypes.Generation.selectedEquationLaws Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.chosen.language
      Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityBinding.permissions = [] := by
    rw [Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.chosen_snapshot]
    cbv
  rw [noLaws]
  rfl

theorem original_schema_declaration :
    continuationSchema.declaration = Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityBinding.declaration := by
  have original := continuationSchema.declared
  have rules : generated.plan.rules = [Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityBinding.declaration] :=
    congrArg GeneralExecutionAdmission.Plan.rules Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.runtime_plan_actual
  rw [rules] at original
  exact List.mem_singleton.mp (List.fst_mem_of_mem_zipIdx original)

theorem actual_rely_declaration_present (name : RelyIndex continuationSchema) :
    (RelyDeclaration.read? continuationSchema name.val).isSome = true := by
  rcases name with ⟨name, member⟩
  have names := Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.actual_continuation_carriers_and_inputs.2.2.2.2.2.2
  rw [names] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with first | second
  · subst name
    have carrierRead : continuationSchema.declaration.rule.typeContext.lookup "n" = some (.base "Name") := by
      rw [original_schema_declaration]
      decide +kernel
    have dependenciesRead : dependencies? continuationSchema.declaration.binding.spec "n" = some [] := by
      rw [original_schema_declaration]
      decide +kernel
    unfold RelyDeclaration.read?
    split
    · rename_i absent
      rw [carrierRead] at absent
      cases absent
    · split
      · rename_i absent
        rw [dependenciesRead] at absent
        cases absent
      · rfl
  · subst name
    have carrierRead : continuationSchema.declaration.rule.typeContext.lookup "q" = some (.base "Proc") := by
      rw [original_schema_declaration]
      decide +kernel
    have dependenciesRead : dependencies? continuationSchema.declaration.binding.spec "q" = some [] := by
      rw [original_schema_declaration]
      decide +kernel
    unfold RelyDeclaration.read?
    split
    · rename_i absent
      rw [carrierRead] at absent
      cases absent
    · split
      · rename_i absent
        rw [dependenciesRead] at absent
        cases absent
      · rfl

def readRely (name : RelyIndex continuationSchema) : RelyDeclaration continuationSchema name.val :=
  (RelyDeclaration.read? continuationSchema name.val).get (actual_rely_declaration_present name)

theorem actual_parameters_present : (generated.modalParameters? continuationSchema).isSome = true :=
  Option.isSome_iff_exists.mpr Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.continuation_parameters_are_computed

def parameters : ModalParameters continuationSchema :=
  (generated.modalParameters? continuationSchema).get actual_parameters_present

theorem parameters_are_computed : generated.modalParameters? continuationSchema = some parameters :=
  (Option.some_get actual_parameters_present).symm

def relyCode (name : RelyIndex continuationSchema) :
    RelyCode continuationSchema name.val (parameters.inputs name) where
  carrier := (readRely name).carrier
  dependencies := (readRely name).dependencies
  declaredCarrier := (readRely name).declaredCarrier
  declaredDependencies := (readRely name).declaredDependencies
  meaning value := value.dependencies = (readRely name).dependencies ∧
    value.ambient = continuationSchema.bound.length ∧
    HasType generated.plan.snapshot.language generated.plan.snapshot.free
      ((readRely name).dependencies ++ continuationSchema.bound) value.body (readRely name).carrier
  bounded _ inhabited := inhabited

def continuationCode (assignment : Assignment) :
    TypeCode generated.plan continuationSchema.bound continuationSchema.programCarrier parameters.output where
  meaning target := HasType generated.plan.snapshot.language generated.plan.snapshot.free
      continuationSchema.bound target continuationSchema.programCarrier ∧
    continuationSchema.rhs? assignment = some target
  bounded _ inhabited := inhabited.1

def nativeInputs : ModalInputs continuationSchema (some parameters) :=
  ⟨relyCode, continuationCode⟩

def classifiedInputs : ClassifiedModalInputs generated continuationSchema
    (generated.modalParameters? continuationSchema) :=
  liftModalInputs (parameters_are_computed.symm ▸ nativeInputs)

theorem actual_scoped_assignment_continuation :
    (continuationCode (Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityBinding.captured 0 Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.channel
      Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.receivedBody Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.zero)).meaning
      Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.result := by
  obtain ⟨carrier, _, bound, _, _, _, _⟩ :=
    Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.actual_continuation_carriers_and_inputs
  constructor
  · rw [carrier, bound]
    exact Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.native_target_is_typed.1
  · unfold Schema.rhs? Schema.operation
    rw [original_schema_declaration, bound]
    decide +kernel

/-- This is the actual successful code-bearing generator output, with an
independent universe judgment at the computed continuation slot. -/
theorem original_comm_modal_code_forms :
    ∃ result, compileEquationModalNativeCode generated continuationSchema classifiedInputs = some result ∧
      result.1 = HSort.star ∧ result.2.expression ∈ ModalUniverse generated continuationSchema HSort.star ∧
      generated.modalFormer? continuationSchema (toNativeInputs classifiedInputs) =
        some ⟨result.1, result.2.code⟩ := by
  obtain ⟨result, compiled, formed⟩ := generated_equation_modal_formation_complete
    Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityBinding.snapshot Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.fragment
    Mettapedia.OSLF.NativeTypes.Structural.heytingFragment Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.vertex continuationSchema
    Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.continuation_schema_member actual_equation_admission classifiedInputs
  have resultSort : result.1 = HSort.star := result.2.resultSlot.trans
    (Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.actual_continuation_parameter_sorts result.2.computedParameters).1
  exact ⟨result, compiled, resultSort, resultSort ▸ formed,
    equation_modal_code_native_comparison classifiedInputs compiled⟩

theorem every_rely_readout_is_preserved (name : RelyIndex continuationSchema) (value : ContextualValue) :
    (liftRelyCode (relyCode name)).native.meaning value ↔ (relyCode name).meaning value :=
  lifted_rely_readout (relyCode name) value

/-- Native classified formation and actual directed execution are both
present. Neither an undecided display rewrite nor a kind tag replaces the
original operational receipt. -/
theorem classified_comm_keeps_actual_native_execution :
    (∃ result, compileEquationModalNativeCode generated continuationSchema classifiedInputs = some result ∧
      result.1 = HSort.star) ∧
    (GeneralOccurrenceSemantics.gslt generated.plan [] (.base "Proc")).Step
      Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.communication Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.result ∧
    (GeneralOccurrenceNativeReceipts.history generated.plan [] (.base "Proc")
      Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.receipt).length = 1 ∧
    GeneralOccurrenceNativeReceipts.administration generated.plan [] (.base "Proc")
      Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.receipt = 0 := by
  obtain ⟨result, formed, sort, _, _⟩ := original_comm_modal_code_forms
  exact ⟨⟨result, formed, sort⟩, Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.actual_generated_semantic_communication,
    Mettapedia.OSLF.NativeTypes.Instances.Rho.FixedArityConsumer.one_primitive_no_equation_administration⟩

end Mettapedia.OSLF.NativeTypes.SortProfiles.Source.RhoControls
