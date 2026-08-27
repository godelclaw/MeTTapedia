import Mettapedia.GraphTheory.FourColor.GoertzelV24BridgeTwoSided

/-!
# A finite orbit can leave a region only through one of its doors

This is the two-door version of the walk argument used for bridges.  A
permutation orbit starts on one side of a Boolean cut, crosses it on its
first step, and can return only at one of two distinguished points.  Since
the orbit is finite and must return, it contains one of those two doors.

The lemma is deliberately independent of maps.  Its intended application is
the exterior of a cubic digon: after the two digon vertices are removed, the
two remaining incident darts are the only doors through which a facial orbit
can return.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TwoDoorOrbit

open Equiv Equiv.Perm

variable {D : Type*} [Fintype D]

/-- If a finite permutation orbit crosses a Boolean side on its first step,
and every point on the far side stays there except possibly at `firstDoor`
or `secondDoor`, then the orbit contains one of the two doors. -/
theorem sameCycle_firstDoor_or_secondDoor
    (φ : Perm D) (side : D → Bool) (start firstDoor secondDoor : D)
    (hstep : ∀ x, x ≠ firstDoor → x ≠ secondDoor →
      side x ≠ side start → side (φ x) = side x)
    (hcross : side (φ start) ≠ side start) :
    φ.SameCycle start firstDoor ∨ φ.SameCycle start secondDoor := by
  classical
  have hN : (φ ^ (orderOf φ)) start = start := by
    rw [pow_orderOf_eq_one]
    rfl
  have hexists : ∃ k, 1 ≤ k ∧ side ((φ ^ k) start) = side start :=
    ⟨orderOf φ, orderOf_pos φ, by rw [hN]⟩
  obtain ⟨k, hk_min, hk_one, hk_side⟩ :
      ∃ k, (∀ j, j < k → ¬ (1 ≤ j ∧
          side ((φ ^ j) start) = side start)) ∧
        1 ≤ k ∧ side ((φ ^ k) start) = side start :=
    ⟨Nat.find hexists, fun j hj => Nat.find_min hexists hj,
      (Nat.find_spec hexists).1, (Nat.find_spec hexists).2⟩
  have hk_two : 2 ≤ k := by
    rcases Nat.eq_or_lt_of_le hk_one with h1 | h2
    · exfalso
      apply hcross
      rw [← h1] at hk_side
      simpa [pow_one] using hk_side
    · omega
  let previous := (φ ^ (k - 1)) start
  have hprevious_side : side previous ≠ side start := fun hEq =>
    hk_min (k - 1) (by omega) ⟨by omega, hEq⟩
  have hstepEq : (φ ^ k) start = φ previous := by
    dsimp [previous]
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ', Perm.mul_apply]
  by_cases hfirst : previous = firstDoor
  · exact Or.inl ⟨((k - 1 : ℕ) : ℤ), by
      rw [zpow_natCast]
      exact hfirst⟩
  by_cases hsecond : previous = secondDoor
  · exact Or.inr ⟨((k - 1 : ℕ) : ℤ), by
      rw [zpow_natCast]
      exact hsecond⟩
  have hstay := hstep previous hfirst hsecond hprevious_side
  rw [hstepEq, hstay] at hk_side
  exact absurd hk_side hprevious_side

end GoertzelV24TwoDoorOrbit

end Mettapedia.GraphTheory.FourColor
