import Mettapedia.OSLF.NativeTypes.Executable
import Mettapedia.OSLF.NativeTypes.Runtime.Atoms
import Mettapedia.OSLF.NativeTypes.Runtime.Evidence
import Mettapedia.OSLF.NativeTypes.Modal.InstanceExecutionControls

/-!
# Supplied non-root native modal instances through public generation

The original machine enters through the public generation request. The
invariant observation names the selected schema's specified contractum and
its assignment-substituted continuation. Adding that observation retains
the generated constructor leaves and the original operational cursor.
The public search consumes the same retained total-work machine as other
generated judgments; the native comparison concerns the supplied instance.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Runtime.ModalInstanceControls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.Executable
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core (Formula)
open Mettapedia.OSLF.NativeTypes.Modal.InstanceDecision
open Mettapedia.OSLF.NativeTypes.Decision.Reference.ModalControls
open Mettapedia.OSLF.NativeTypes.Runtime.Description (Meaning Readout)
open Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated (generated)

def generationRequest : Request := .originalMachine
  Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot
  Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.fragment {} []

theorem generation_success : generate generationRequest = .ok (Local.partrec {} []) := by
  change (if GeneralOccurrenceFrontier.CoverageClaims.snapshotKey
      Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot =
      GeneralOccurrenceFrontier.CoverageClaims.snapshotKey
        Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot then
    if Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.fragment =
        Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.fragment then .ok (Local.partrec {} [])
    else .error (.fragmentMismatch .originalMachine)
    else .error (.snapshotMismatch .originalMachine) : Except GenerationIssue Installed) = .ok (Local.partrec {} [])
  simp

def base : Installed := Local.partrec {} []

def observation (permit : Bool) : Atoms.Observation base.native where
  predicate := contractumPredicate base.native.system (request permit).target
    (((codes permit).inputs.2 supplied).meaning (request permit).target)
  accepts (actual : Pattern) := decide (actual = (request permit).target) &&
    @decide (((codes permit).inputs.2 supplied).meaning (request permit).target)
      ((decisions permit).continuation supplied (request permit).target)
  exact actual := by
    simp only [Bool.and_eq_true, decide_eq_true_iff]
    refine and_congr ?_ Iff.rfl
    change actual = (request permit).target ↔
      (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.theory []).Equiv
        actual (request permit).target
    exact (Mettapedia.OSLF.NativeTypes.Instances.Local.Structural.no_equation_iff_eq
      Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan_equations [] (.base "Cfg")
      actual (request permit).target).symm

def atomicAdmission (permit : Bool) : Mettapedia.OSLF.NativeTypes.Decision.Admission.LeafAdmission Unit where
  admitted _ := (generated.modalFormer? schema (codes permit).actualInputs).isSome = true
  probe _ := if (generated.modalFormer? schema (codes permit).actualInputs).isSome then .ok ()
    else .error (.malformedJudgment (.base "Cfg"))
  exact _ := by
    split <;> simp_all [Except.isOk, Except.toBool]

def installed (permit : Bool) : Installed :=
  Atoms.installed base (fun (_ : Unit) => observation permit) (atomicAdmission permit)

def formula (permit : Bool) : (installed permit).native.Formula := .possibility (.atom (.inr ()))

def run (permit : Bool) (budget : Nat) :=
  Mettapedia.OSLF.NativeTypes.Executable.search (installed permit) (formula permit)
    (request permit).source budget

def source (permit : Bool) : (installed permit).native.Decoded (request permit).source :=
  ⟨(request permit).source, by
    change Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source [] (request permit).source
    have typed := typed_plugged_source permit
    change Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.Source generated.plan [] (.base "Cfg")
      (request permit).source at typed
    rw [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_plan] at typed
    exact typed,
   rfl⟩

/-- The generated source/schema comparison is a whole original-profile
comparison; no concrete step is installed as the public denotation. -/
theorem instance_system : base.native.system = GeneratedInstance.system schema := by
  change GeneralOccurrenceSemantics.gslt Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan [] (.base "Cfg") =
    GeneralOccurrenceSemantics.gslt generated.plan [] (.base "Cfg")
  rw [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_plan]

/-- The original installed system and the generated supplied-instance system
agree for every source, specified target and continuation proposition. -/
theorem generated_contractum_meaning (first target : Pattern) (continuation : Prop) :
    Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticDiamond base.native.system
      (contractumPredicate base.native.system target continuation) first ↔
    Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticDiamond (GeneratedInstance.system schema)
      (contractumPredicate (GeneratedInstance.system schema) target continuation) first := by
  change Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticDiamond
      (GeneralOccurrenceSemantics.gslt Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan [] (.base "Cfg"))
      (contractumPredicate
        (GeneralOccurrenceSemantics.gslt Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan [] (.base "Cfg"))
        target continuation) first ↔
    Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticDiamond
      (GeneralOccurrenceSemantics.gslt generated.plan [] (.base "Cfg"))
      (contractumPredicate (GeneralOccurrenceSemantics.gslt generated.plan [] (.base "Cfg"))
        target continuation) first
  rw [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_plan]

theorem native_meaning (permit : Bool) :
    Meaning (installed permit).native (formula permit) (request permit).source ↔
      Nonempty (Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome
        schema focus supplied (codes permit).continuation) := by
  rw [Mettapedia.OSLF.NativeTypes.Runtime.Description.meaning_at_decoded
    (installed permit).native (formula permit) (request permit).source (source permit)]
  change Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticDiamond base.native.system
    (contractumPredicate base.native.system (request permit).target
      (((codes permit).inputs.2 supplied).meaning (request permit).target)) (request permit).source ↔ _
  have joined := (instance_native_comparison (admitted := Source) equations (request permit).target
    (((codes permit).inputs.2 supplied).meaning (request permit).target)
    (@decide (((codes permit).inputs.2 supplied).meaning (request permit).target)
      ((decisions permit).continuation supplied (request permit).target))
    (@decide_eq_true_iff (((codes permit).inputs.2 supplied).meaning (request permit).target)
      ((decisions permit).continuation supplied (request permit).target))
    (request permit).source).trans (GeneratedInstance.outcome_exact (request permit))
  exact (generated_contractum_meaning (request permit).source (request permit).target
    (((codes permit).inputs.2 supplied).meaning (request permit).target)).trans joined

theorem formed (permit : Bool) :
    Mettapedia.OSLF.NativeTypes.Decision.Admission.Formed
      (installed permit).native.generated.logicFragment (installed permit).native.leafAdmission (formula permit) := by
  apply Mettapedia.OSLF.NativeTypes.Decision.Admission.Formed.possibility rfl
  apply Mettapedia.OSLF.NativeTypes.Decision.Admission.Formed.atom
  change (generated.modalFormer? schema (codes permit).actualInputs).isSome = true
  unfold Mettapedia.OSLF.NativeTypes.Generation.Generated.modalFormer?
  rw [if_pos ⟨Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_equation_admission,
    rfl, Mettapedia.OSLF.NativeTypes.Generation.generated_schema_admitted actual_schema⟩]
  split
  · rename_i absent
    rw [actual_parameters] at absent
    cases absent
  · rfl

def completeBudget (permit : Bool) : Nat :=
  Mettapedia.OSLF.NativeTypes.Executable.decisionBound (installed permit) (formula permit) (source permit)

theorem public_complete (permit : Bool) (budget : Nat) (enough : completeBudget permit ≤ budget) :
    ∃ answer, (run permit budget).readout = .judgment (.decided answer) := by
  apply Mettapedia.OSLF.NativeTypes.Executable.search_complete
  · exact ⟨(request permit).source, (source permit).property.1, rfl⟩
  · exact formed permit
  · rfl
  · intro actual
    have same : actual = source permit := Subtype.ext actual.property.2
    rw [same]
    exact enough

theorem positive_at_bound : (run true (completeBudget true)).readout = .judgment (.decided true) := by
  obtain ⟨answer, read⟩ := public_complete true _ (Nat.le_refl _)
  cases answer with
  | true => exact read
  | false =>
    have absent := Mettapedia.OSLF.NativeTypes.Executable.search_negative
      (installed true) (formula true) (request true).source _ read
    exact (absent ((native_meaning true).mpr
      Mettapedia.OSLF.NativeTypes.Modal.InstanceExecutionControls.original_instance_positive)).elim

theorem negative_at_bound : (run false (completeBudget false)).readout = .judgment (.decided false) := by
  obtain ⟨answer, read⟩ := public_complete false _ (Nat.le_refl _)
  cases answer with
  | false => exact read
  | true =>
    have holds := Mettapedia.OSLF.NativeTypes.Executable.search_positive
      (installed false) (formula false) (request false).source _ read
    exact (Mettapedia.OSLF.NativeTypes.Modal.InstanceExecutionControls.false_substituted_continuation
      ((native_meaning false).mp holds)).elim

theorem exact_public_resume (permit : Bool) (first more : Nat) :
    run permit (first + more) = Mettapedia.OSLF.NativeTypes.Executable.resume more (run permit first) :=
  Mettapedia.OSLF.NativeTypes.Executable.search_resume (installed permit) (formula permit) (request permit).source first more

theorem shared_public_budget (permit : Bool) (budget : Nat) : (run permit budget).spent ≤ budget :=
  Mettapedia.OSLF.NativeTypes.Executable.search_spent_le (installed permit) (formula permit) (request permit).source budget

theorem retained_instance (permit : Bool) : schema.position = [0] ∧ schema.relyNames = ["k", "v"] ∧
    (request permit).source = Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source ∧
    (request permit).target = Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.firstTarget :=
  ⟨computed_schema.1, computed_schema.2.1, rfl, rfl⟩

def origins (permit : Bool) (budget : Nat) : List Nat :=
  (run permit budget).observations.map fun observed =>
    observed.receipt.val.firing.job.declaration.declarationIndex

/-- A successful public generation result is extended with this independently
checked atom. The supplied result remains the operational base. -/
def installGenerated (actual : Installed) (same : actual = base) (permit : Bool) : Installed :=
  Atoms.installed actual
    (by rw [same]; exact fun (_ : Unit) => observation permit) (atomicAdmission permit)

def generatedRun (permit : Bool) (budget : Nat) : Except GenerationIssue (Readout × Nat × List (Pattern × Pattern)) :=
  match success : generate generationRequest with
  | .error issue => .error issue
  | .ok actual =>
    have same : actual = base := by
      rw [generation_success] at success
      exact (Except.ok.inj success).symm
    let output := installGenerated actual same permit
    let current := Mettapedia.OSLF.NativeTypes.Executable.search output
      (.possibility (.atom (.inr ()))) (request permit).source budget
    .ok (current.readout, current.spent, current.observations.map fun observed =>
      (output.native.render observed.source,
        output.native.render (output.runtime.cursor.target observed.source observed.receipt)))

theorem generated_run_exact (permit : Bool) (budget : Nat) :
    generatedRun permit budget = .ok ((run permit budget).readout, (run permit budget).spent,
      (run permit budget).observations.map fun observed =>
        ((installed permit).native.render observed.source,
          (installed permit).native.render
            ((installed permit).runtime.cursor.target observed.source observed.receipt))) := by
  unfold generatedRun
  split
  · rename_i issue failure
    rw [generation_success] at failure
    cases failure
  · rename_i actual success
    have same : actual = base := by
      rw [generation_success] at success
      exact (Except.ok.inj success).symm
    subst actual
    rfl

/-- A computed positive instance retains a real original-machine receipt
whose target is the specified RHS and whose substituted continuation holds. -/
theorem saved_specified_receipt (permit : Bool) (budget : Nat)
    (read : (run permit budget).readout = .judgment (.decided true)) :
    ∃ actual : (installed permit).native.Decoded (request permit).source, ∃ receipt listed,
      (Mettapedia.OSLF.NativeTypes.Decision.Machine.Observation.mk actual.val receipt listed []) ∈
        (run permit budget).observations ∧
      Mettapedia.Languages.PartrecMachine.Reduces actual.val
        ((installed permit).runtime.cursor.target actual.val receipt) ∧
      (installed permit).runtime.cursor.target actual.val receipt = (request permit).target ∧
      ((codes permit).inputs.2 supplied).meaning (request permit).target := by
  obtain ⟨actual, receipt, listed, saved, stepped, holds⟩ :=
    Mettapedia.OSLF.NativeTypes.Runtime.Evidence.search_positive_receipt
      (installed permit).native (installed permit).runtime (.atom (.inr ()))
      (request permit).source budget read
  change (∃ candidate : Pattern,
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source [] candidate ∧
    candidate = (installed permit).runtime.cursor.target actual.val receipt ∧
    base.native.system.Equiv candidate (request permit).target ∧
    ((codes permit).inputs.2 supplied).meaning (request permit).target) at holds
  obtain ⟨candidate, _, same, related, continuation⟩ := holds
  have equal : candidate = (request permit).target :=
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Comparison.generated_equivalence_is_equality [] related
  exact ⟨actual, receipt, listed, saved,
    (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Comparison.generated_step_iff_original [] actual.property.1).mp stepped,
    same.symm.trans equal, continuation⟩

#guard (run true 0).readout == .judgment .unknown
#guard (run true 1).readout == .judgment .unknown
#guard (run true 1000).readout == .judgment (.decided true)
#guard (run false 1000).readout == .judgment (.decided false)
#guard origins true 1000 == [0]
#guard origins false 1000 == [0]
#guard (Mettapedia.OSLF.NativeTypes.Executable.resume 999 (run true 1)).readout == .judgment (.decided true)
#guard (run true 1000).spent ≤ 1000
#guard (generatedRun true 0).map (fun view => view.1) == .ok (.judgment .unknown)
#guard (generatedRun true 1000).map (fun view => view.1) == .ok (.judgment (.decided true))
#guard (generatedRun false 1000).map (fun view => view.1) == .ok (.judgment (.decided false))

#print axioms generated_contractum_meaning
#print axioms native_meaning
#print axioms public_complete
#print axioms saved_specified_receipt

end Mettapedia.OSLF.NativeTypes.Runtime.ModalInstanceControls
