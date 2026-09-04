import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Retaining endpoint margins in a selected finite sweep

Finite-state repetition is useful for physical decomposition only away from
the endpoints of the swept path.  This file supplies the generic counting
lemma: imposing a margin of `margin` at each end discards at most
`2 * margin` selected coordinates.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace RestrictedPositionMargins

/-- Selected coordinates with at least `margin` vertices available on both
sides of the cut. -/
def withMargins (n margin : Nat) (positions : Finset (Fin (n + 1))) :
    Finset (Fin (n + 1)) :=
  positions.filter fun cut =>
    margin ≤ cut.val ∧ margin ≤ n + 1 - cut.val

private def leftFailures (n margin : Nat)
    (positions : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  positions.filter fun cut => cut.val < margin

private def rightFailures (n margin : Nat)
    (positions : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  positions.filter fun cut => n + 1 - cut.val < margin

private theorem card_leftFailures_le (n margin : Nat)
    (positions : Finset (Fin (n + 1))) :
    (leftFailures n margin positions).card ≤ margin := by
  let encode : {cut // cut ∈ leftFailures n margin positions} → Fin margin :=
    fun cut => ⟨cut.1.val, (Finset.mem_filter.mp cut.2).2⟩
  have hinjective : Function.Injective encode := by
    intro first second heq
    apply Subtype.ext
    apply Fin.ext
    have hvalues := congrArg Fin.val heq
    change first.1.val = second.1.val at hvalues
    exact hvalues
  have hcard := Fintype.card_le_of_injective encode hinjective
  simpa using hcard

private theorem card_rightFailures_le (n margin : Nat)
    (positions : Finset (Fin (n + 1))) :
    (rightFailures n margin positions).card ≤ margin := by
  let encode : {cut // cut ∈ rightFailures n margin positions} → Fin margin :=
    fun cut => ⟨n + 1 - cut.1.val, (Finset.mem_filter.mp cut.2).2⟩
  have hinjective : Function.Injective encode := by
    intro first second heq
    apply Subtype.ext
    apply Fin.ext
    have hvalues := congrArg Fin.val heq
    change n + 1 - first.1.val = n + 1 - second.1.val at hvalues
    have hfirst := first.1.isLt
    have hsecond := second.1.isLt
    omega
  have hcard := Fintype.card_le_of_injective encode hinjective
  simpa using hcard

/-- Removing both endpoint margins loses at most `2 * margin` positions. -/
theorem card_le_withMargins_add_two_mul (n margin : Nat)
    (positions : Finset (Fin (n + 1))) :
    positions.card ≤ (withMargins n margin positions).card + 2 * margin := by
  let left := leftFailures n margin positions
  let right := rightFailures n margin positions
  let middle := withMargins n margin positions
  have hcover : positions ⊆ middle ∪ left ∪ right := by
    intro cut hcut
    simp only [Finset.mem_union, middle, left, right, withMargins,
      leftFailures, rightFailures, Finset.mem_filter]
    by_cases hleft : margin ≤ cut.val
    · by_cases hright : margin ≤ n + 1 - cut.val
      · exact Or.inl (Or.inl ⟨hcut, hleft, hright⟩)
      · exact Or.inr ⟨hcut, Nat.lt_of_not_ge hright⟩
    · exact Or.inl (Or.inr ⟨hcut, Nat.lt_of_not_ge hleft⟩)
  have hleftCard : left.card ≤ margin := by
    exact card_leftFailures_le n margin positions
  have hrightCard : right.card ≤ margin := by
    exact card_rightFailures_le n margin positions
  calc
    positions.card ≤ (middle ∪ left ∪ right).card :=
      Finset.card_le_card hcover
    _ ≤ (middle ∪ left).card + right.card := Finset.card_union_le _ _
    _ ≤ (middle.card + left.card) + right.card := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ middle.card + 2 * margin := by omega

/-- A strict cardinal surplus beyond both endpoint margins survives the
restriction. -/
theorem target_lt_card_withMargins_of_add_two_mul_lt
    (n margin target : Nat) (positions : Finset (Fin (n + 1)))
    (hmany : target + 2 * margin < positions.card) :
    target < (withMargins n margin positions).card := by
  have hcover := card_le_withMargins_add_two_mul n margin positions
  omega

end RestrictedPositionMargins

end Mettapedia.GraphTheory.FourColor.Compositional
