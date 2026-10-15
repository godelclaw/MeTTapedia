import Mettapedia.OSLF.Framework.RhoScopeMinimumReceipts
import Mettapedia.OSLF.Framework.RhoScopeMinimumControls
import Mettapedia.OSLF.Syntax.RhoFiniteParallelSplitCounts

/-!
# Constructed receipt controls on actual intrinsic equation classes

An admitted quoted null returns its actual two atomic premises at depth zero.
The unseeded least scope returns no receipt despite its equation loops.
Minimum selection does not identify separately supplied origins or bound
their depths. Repeated equal component occurrences yield repeated search
positions but only three distinct split values.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeReceiptSearchControls

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoIntrinsicReadback
open RhoQuotedParallelLists RhoIntrinsicCanonicalBag RhoFiniteParallelSplits
open RhoFiniteParallelSplitCounts
open RhoEquationGeneratedScope RhoGeneratedScopeStrata RhoGeneratedScopeSubstitution
open RhoScopeMinimumReceipts RhoGeneratedScopeMinimum RhoScopeReceiptLoops
open RhoGeneratedScopeControls RhoScopeDecisionControls

local instance processClassDecision (context : Ctx sig) : DecidableEq (Process context) :=
  equationClassDecision context Srt.pr

def nullAtom {context : Ctx sig} (process : Process context) : Prop := process = zero context

local instance nullAtomDecision (context : Ctx sig) : DecidablePred (nullAtom (context := context)) :=
  fun process => show Decidable (process = zero context) from inferInstance

local instance emptyAtomDecision : DecidablePred unseededAtom := fun _ => isFalse id

local instance zeroAtomDecision : DecidablePred RhoScopeQuotientControls.leftScope :=
  fun process => show Decidable (process = zero []) from inferInstance

local instance doubleOriginDecision : DecidablePred RhoScopeQuotientControls.rightScope :=
  fun process => show Decidable (process = visible ∨ process = suspended) from inferInstance

def nullCertificate {context : Ctx sig} : Certificate nullAtom nullAtom (quote (zero context)) :=
  (congrArg quote (join_zero_left (zero context))) ▸
    Certificate.atoms (zero context) (zero context) rfl rfl

theorem null_certificate_depth {context : Ctx sig} : (nullCertificate (context := context)).depth = 0 := by
  simp only [nullCertificate, depth_cast, Certificate.depth]

theorem null_minimum_zero (context : Ctx sig) :
    minimumDepth? nullAtom nullAtom (quote (zero context)) = some 0 := by
  apply (minimum_zero_iff_bounded _ _ _).mpr
  exact ⟨nullCertificate, Nat.le_of_eq null_certificate_depth⟩

theorem zero_depth_null_receipt_origins {context : Ctx sig} {name : Name context}
    (receipt : Certificate nullAtom nullAtom name) (depth : receipt.depth = 0) :
    receipt.atomicOrigins = [Sum.inl (zero context), Sum.inr (zero context)] := by
  cases receipt with
  | atoms first second firstAtom secondAtom =>
    change first = zero context at firstAtom
    change second = zero context at secondAtom
    subst first
    subst second
    rfl
  | left child certificate second admitted => simp [Certificate.depth] at depth
  | right first admitted child certificate => simp [Certificate.depth] at depth
  | both first second firstReceipt secondReceipt =>
    simp [Certificate.depth] at depth

theorem constructed_null_receipt (context : Ctx sig) :
    ∃ receipt : Certificate nullAtom nullAtom (quote (zero context)),
      minimumReceipt? nullAtom nullAtom (quote (zero context)) = some receipt ∧
      receipt.depth = 0 ∧ receipt.atomicOrigins = [Sum.inl (zero context), Sum.inr (zero context)] := by
  have present := (minimumReceipt?_presence nullAtom nullAtom (quote (zero context))).mpr
    (certificate_sound nullCertificate)
  cases readout : minimumReceipt? nullAtom nullAtom (quote (zero context)) with
  | none => rw [readout] at present; cases present
  | some receipt =>
    have attained := minimumReceipt?_some_depth nullAtom nullAtom (quote (zero context)) readout
    have depth : receipt.depth = 0 := Option.some.inj (attained.symm.trans (null_minimum_zero context))
    exact ⟨receipt, rfl, depth, zero_depth_null_receipt_origins receipt depth⟩

theorem equation_loops_return_no_unseeded_receipt (name : Name []) :
    (step unseededAtom RhoScopeQuotientControls.leftScope).gfp name ∧
      minimumReceipt? unseededAtom RhoScopeQuotientControls.leftScope name = none :=
  ⟨unseeded_greatest_scope_admits_every_name name,
    (minimumReceipt?_none_iff _ _ _).mpr (unseeded_least_scope_empty name)⟩

theorem selected_minimum_does_not_bound_supplied_receipts (context : Ctx sig) :
    ∃ receipt : Certificate nullAtom nullAtom (quote (zero context)),
      minimumReceipt? nullAtom nullAtom (quote (zero context)) = some receipt ∧ receipt.depth = 0 ∧
      ∀ cutoff, ∃ supplied : Certificate nullAtom nullAtom (quote (zero context)), cutoff < supplied.depth := by
  obtain ⟨receipt, readout, depth, _⟩ := constructed_null_receipt context
  exact ⟨receipt, readout, depth,
    receipt_depths_exceed_every_cutoff (left := nullAtom) (right := nullAtom) rfl nullCertificate⟩

theorem selection_does_not_identify_two_actual_origins :
    ¬ (minimumReceipt? RhoScopeQuotientControls.leftScope RhoScopeQuotientControls.rightScope
          (quote visible) = some outputCertificate ∧
      minimumReceipt? RhoScopeQuotientControls.leftScope RhoScopeQuotientControls.rightScope
          (quote visible) = some suspendedCertificate) := by
  rintro ⟨first, second⟩
  exact distinct_atomic_certificate_origins (Option.some.inj (first.symm.trans second))

theorem duplicate_component_search_positions {context : Ctx sig} (process : Process context)
    (component : MeTTaIL.Syntax.Pattern) (inventory : components process = {component, component}) :
    (candidateList process).length = 4 ∧ (candidates process).card = 3 := by
  constructor
  · rw [candidateList_length, inventory]
    simp
  · exact two_equal_components_have_three_value_splits process component inventory

end Mettapedia.OSLF.Framework.RhoScopeReceiptSearchControls
