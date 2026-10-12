import Mettapedia.OSLF.Framework.RhoGeneratedScopeMinimum
import Mettapedia.OSLF.Framework.RhoScopeDecisionControls
import Mettapedia.OSLF.Framework.RhoScopeReceiptLoops

/-!
# Exact minimum depths and retained receipts in the displayed scope

The actual quoted output has minimum depth zero, while its retained receipts
have unbounded depths and additional atomic premise occurrences. The displayed
scope rejects the quoted null at every depth, even though the separately
seeded scope admits it. These are different authored generators.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeMinimumControls

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls RhoIntrinsicReadback
open RhoEquationGeneratedScope RhoGeneratedScopeMinimum RhoGeneratedScopeDecision
open RhoScopeSeedReadings RhoScopeDecisionControls RhoScopeReceiptLoops

local instance : DecidableEq (Process []) := equationClassDecision [] Srt.pr

local instance : DecidablePred leftAtom :=
  fun process => show Decidable (process = zero []) from inferInstance

local instance : DecidablePred rightAtom :=
  fun process => show Decidable (process = visible) from inferInstance

def displayedReceipt : Certificate leftAtom rightAtom (quote visible) :=
  (congrArg quote (join_zero_left visible)) ▸ Certificate.atoms (zero []) visible rfl rfl

theorem displayed_receipt_depth_zero : displayedReceipt.depth = 0 := by
  simp only [displayedReceipt, RhoGeneratedScopeSubstitution.depth_cast, Certificate.depth]

theorem displayed_output_minimum_zero : minimumDepth? leftAtom rightAtom (quote visible) = some 0 := by
  apply (minimum_zero_iff_bounded _ _ _).mpr
  exact ⟨displayedReceipt, Nat.le_of_eq displayed_receipt_depth_zero⟩

theorem displayed_null_minimum_absent : minimumDepth? leftAtom rightAtom (quote (zero [])) = none :=
  (minimum_none_iff _ _ _).mpr ((guard_false_iff _ _ _).mp displayed_null_rejected)

theorem exact_minimum_does_not_identify_receipt_depths :
    minimumDepth? leftAtom rightAtom (quote visible) = some 0 ∧
      ∀ cutoff, ∃ receipt : Certificate leftAtom rightAtom (quote visible), cutoff < receipt.depth :=
  ⟨displayed_output_minimum_zero,
    receipt_depths_exceed_every_cutoff (left := leftAtom) (right := rightAtom) rfl displayedReceipt⟩

theorem loop_keeps_an_additional_atomic_occurrence :
    (extend (left := leftAtom) (right := rightAtom) rfl displayedReceipt).atomicOrigins =
      Sum.inl (zero []) :: displayedReceipt.atomicOrigins :=
  extend_atomic_origins (left := leftAtom) (right := rightAtom) rfl displayedReceipt

theorem seeded_null_admission_does_not_change_displayed_rejection
    (env : RhoScopeExpression.Environment []) :
    RhoScopeExpression.denote atoms seeded env (quote (zero [])) ∧
      minimumDepth? leftAtom rightAtom (quote (zero [])) = none :=
  ⟨seeded_admits_null env, displayed_null_minimum_absent⟩

end Mettapedia.OSLF.Framework.RhoScopeMinimumControls
