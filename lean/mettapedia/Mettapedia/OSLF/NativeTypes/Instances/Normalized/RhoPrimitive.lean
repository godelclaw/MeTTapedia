import Mettapedia.OSLF.MeTTaIL.GeneralRhoStandardSites
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobCoverage
import Mettapedia.OSLF.NativeTypes.Decision.Machine.Interface

/-!
# Finite original primitive receipts for rho's standard reduction contexts

The finite readout completes the actual licensed rule jobs in declaration and
site order. Coverage is of complete receipt values, including assignments,
matcher choices and premise histories; it does not follow from eventual
reachable-state exploration. The outer native cursor suspends the complete
readout as one operation, so its logical budget is not a physical cost bound.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Normalized.RhoPrimitive

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Decision.Machine
open Mettapedia.OSLF.NativeTypes.Decision.Scheduling

abbrev plan := GeneralRho.Standard.plan
abbrev proc : TypeExpr := .base "Proc"

def Source (source : Pattern) : Prop :=
  OpenPatternWellSorted plan.snapshot.language plan.snapshot.free [] proc source

def raw : Mettapedia.GSLT.GSLT := equalityGSLT Pattern fun source target =>
  ∃ receipt, GeneralOccurrenceSemantics.Primitive plan [] proc source receipt ∧ receipt.target = target

def receipts (source : Pattern) : List GeneralRuleJobs.Receipt :=
  GeneralRuleJobExecution.completedReceipts plan [] proc source

theorem receipts_exact (source : Pattern) (receipt : GeneralRuleJobs.Receipt) :
    receipt ∈ receipts source ↔ GeneralOccurrenceSemantics.Primitive plan [] proc source receipt :=
  GeneralRuleJobExecution.mem_completedReceipts_iff plan [] proc source GeneralRho.Standard.stratified receipt

theorem receipts_source_step {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (member : receipt ∈ receipts source) : raw.Step source receipt.target :=
  ⟨receipt, (receipts_exact source receipt).mp member, rfl⟩

theorem receipts_target_typed {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (member : receipt ∈ receipts source) : Source receipt.target :=
  (GeneralPlanEnvironment.typing_iff plan [] proc receipt.target).mp
    ((receipts_exact source receipt).mp member).2.2.2.2

def frontier (budget : Nat) (source : Pattern) := (receipts source).take budget

def backend : Backend raw Source where
  Receipt _ := GeneralRuleJobs.Receipt
  target _ receipt := receipt.target
  frontier := frontier
  closed budget source := decide ((receipts source).length ≤ budget)
  sound _ _ _ member := receipts_source_step (List.mem_of_mem_take member)
  coverage budget source closed target stepped := by
    obtain ⟨receipt, valid, same⟩ := stepped
    refine ⟨receipt, ?_, same.symm⟩
    change receipt ∈ (receipts source).take budget
    rw [List.take_of_length_le (of_decide_eq_true closed)]
    exact (receipts_exact source receipt).mpr valid
  target_admitted _ _ _ _ member := receipts_target_typed (List.mem_of_mem_take member)
  completionBudget source := (receipts source).length
  complete_at _ _ := by simp
  frontier_stable source budget enough := by
    change (receipts source).take budget = (receipts source).take (receipts source).length
    rw [List.take_of_length_le enough, List.take_length]
  closed_stable _ _ enough := by
    simp [enough]

def cursor : CursorBackend raw Source where
  Receipt _ := GeneralRuleJobs.Receipt
  target _ receipt := receipt.target
  tasks source := .pause fun _ => Stream.ofList (receipts source)
  sound _ _ member := receipts_source_step
    (by simpa only [Stream.flatten, Stream.flatten_ofList] using member)
  coverage source _ target stepped := by
    obtain ⟨receipt, valid, same⟩ := stepped
    exact ⟨receipt, by simpa only [Stream.flatten, Stream.flatten_ofList] using
      (receipts_exact source receipt).mpr valid, same.symm⟩
  target_admitted _ _ _ member := receipts_target_typed
    (by simpa only [Stream.flatten, Stream.flatten_ofList] using member)

/-- Every original primitive receipt remains in the finite cursor. -/
theorem cursor_receipts_exact (source : Pattern) :
    (cursor.tasks source).flatten = receipts source := Stream.flatten_ofList _

end Mettapedia.OSLF.NativeTypes.Instances.Normalized.RhoPrimitive
