import Mathlib.Data.Finset.Card

/-!
# Stable capped cardinalities under bounded deletion

Finite interface profiles record cardinalities only up to a threshold.  When
an interface is advanced, a bounded number of formerly exterior labels can
become explicit interface labels and must be subtracted.  A cap at the final
threshold alone loses information at exactly this operation: from
`min n threshold` one cannot distinguish `n = threshold` from a larger `n`.

The sufficient and sharp generic remedy is to retain the cap at
`threshold + deletionBound`.  After deleting at most `deletionBound` labels,
the cap at `threshold` of the remainder is then determined exactly.  This is
the arithmetic step used by the facial transfer state, where a path component
can lose at most its two endpoints when the rolling interface advances.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CappedCardSubtraction

/-- Executable capped subtraction.  `stored` is a cardinality capped at the
final threshold plus the deletion budget; `removed` is the exact number
deleted, itself bounded by that budget. -/
def cappedCardAfterDeletion (threshold deletionBound : Nat)
    (stored : Fin (threshold + deletionBound + 1))
    (removed : Fin (deletionBound + 1)) : Fin (threshold + 1) :=
  ⟨min (stored.val - removed.val) threshold,
    Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

@[simp]
theorem cappedCardAfterDeletion_val (threshold deletionBound : Nat)
    (stored : Fin (threshold + deletionBound + 1))
    (removed : Fin (deletionBound + 1)) :
    (cappedCardAfterDeletion threshold deletionBound stored removed).val =
      min (stored.val - removed.val) threshold :=
  rfl

/-- A cap enlarged by the deletion budget determines the smaller cap after
any deletion within that budget. -/
theorem min_sub_eq_min_min_add_sub
    (card threshold deletionBound removed : Nat)
    (hremoved : removed ≤ deletionBound) :
    min (card - removed) threshold =
      min (min card (threshold + deletionBound) - removed) threshold := by
  omega

/-- Semantic exactness of the executable decoder. -/
theorem cappedCardAfterDeletion_eq_of_exact
    (card threshold deletionBound removed : Nat)
    (stored : Fin (threshold + deletionBound + 1))
    (removedCode : Fin (deletionBound + 1))
    (hstored : stored.val = min card (threshold + deletionBound))
    (hremoved : removedCode.val = removed) :
    (cappedCardAfterDeletion threshold deletionBound stored removedCode).val =
      min (card - removed) threshold := by
  have hremoved_le : removed ≤ deletionBound := by
    rw [← hremoved]
    omega
  rw [cappedCardAfterDeletion_val, hstored, hremoved]
  exact (min_sub_eq_min_min_add_sub card threshold deletionBound removed
    hremoved_le).symm

/-- Finset form of capped subtraction.  If `removed` is contained in
`support`, retaining the support cardinality up to `threshold + deletionBound`
is enough to recover the threshold-capped cardinality after deletion. -/
theorem min_card_sdiff_eq_min_min_card_add_sub
    {Label : Type*} [DecidableEq Label]
    (support removed : Finset Label) (threshold deletionBound : Nat)
    (hsubset : removed ⊆ support)
    (hremoved : removed.card ≤ deletionBound) :
    min (support \ removed).card threshold =
      min (min support.card (threshold + deletionBound) - removed.card)
        threshold := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsubset]
  exact min_sub_eq_min_min_add_sub support.card threshold deletionBound
    removed.card hremoved

/-- The facial specialization: remembering a component up to seven distinct
labels recovers its cap at five after removing at most two labels. -/
theorem min_card_sdiff_five_eq_min_min_card_seven_sub
    {Label : Type*} [DecidableEq Label]
    (support removed : Finset Label)
    (hsubset : removed ⊆ support)
    (hremoved : removed.card ≤ 2) :
    min (support \ removed).card 5 =
      min (min support.card 7 - removed.card) 5 := by
  simpa using min_card_sdiff_eq_min_min_card_add_sub support removed 5 2
    hsubset hremoved

/-- The smaller cap alone is genuinely insufficient for deletion: cardinality
five and cardinality six have the same cap at five, but deleting one label
separates their new capped values. -/
theorem cap_five_does_not_determine_cap_after_one_deletion :
    min 5 5 = min 6 5 ∧ min (5 - 1) 5 ≠ min (6 - 1) 5 := by
  omega

end GoertzelV24CappedCardSubtraction

end Mettapedia.GraphTheory.FourColor
