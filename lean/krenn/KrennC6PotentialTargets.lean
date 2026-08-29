import KrennDoilyPotential
import Mathlib

/-!
Exact potential targets for the fixed C6 non-collapse branch.

A non-collapse adjugate slot at vertex `0` supplies the two cycle P-kills
on edges `04` and `05`.  The finite potential calculation below proves two
facts needed to make the remaining balanced-layer task precise:

* P-kills supported only on the six C6 cycle edges cannot have nonzero mean;
* the three chord P-kills `01`, `02`, `03` complete the two local kills to a
  vertex-star, which contradicts monochromatic normalization.

Thus a successful non-collapse harvest must produce diagonal-side chord
kills; merely accumulating cycle-side adjugate kills cannot close the branch.
-/

namespace Krenn.C6PotentialTargets

open Krenn.DoilyPotential

/-- Six chord-zero relations already force a potential supported on the C6
cycle to vanish.  The first three form the complement triangle `023`; the
remaining three propagate that zero to `1`, `4`, and `5`. -/
theorem potential_zero_of_c6_chord_zero
    {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R] [CharZero R]
    (s : Fin 6 → R)
    (h01 : s 0 + s 1 = 0)
    (h02 : s 0 + s 2 = 0)
    (h03 : s 0 + s 3 = 0)
    (h14 : s 1 + s 4 = 0)
    (h15 : s 1 + s 5 = 0)
    (h23 : s 2 + s 3 = 0) :
    ∀ vertex, s vertex = 0 := by
  have htwice0 : (2 : R) * s 0 = 0 := by
    calc
      (2 : R) * s 0 = (s 0 + s 2) + (s 0 + s 3) - (s 2 + s 3) := by ring
      _ = 0 := by rw [h02, h03, h23]; ring
  have h0 : s 0 = 0 := by
    exact (mul_eq_zero.mp htwice0).resolve_left two_ne_zero
  have h1 : s 1 = 0 := by linear_combination h01 - h0
  have h2 : s 2 = 0 := by linear_combination h02 - h0
  have h3 : s 3 = 0 := by linear_combination h03 - h0
  have h4 : s 4 = 0 := by linear_combination h14 - h1
  have h5 : s 5 = 0 := by linear_combination h15 - h1
  intro vertex
  fin_cases vertex <;> assumption

/-- There is no mean-one potential whose nonzero edge coefficients are
confined to the fixed C6 cycle. -/
theorem no_mean_one_potential_supported_on_c6
    {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R] [CharZero R]
    (s : Fin 6 → R)
    (h01 : s 0 + s 1 = 0)
    (h02 : s 0 + s 2 = 0)
    (h03 : s 0 + s 3 = 0)
    (h14 : s 1 + s 4 = 0)
    (h15 : s 1 + s 5 = 0)
    (h23 : s 2 + s 3 = 0)
    (hmean : totalPotential s = 1) : False := by
  have hzero := potential_zero_of_c6_chord_zero s h01 h02 h03 h14 h15 h23
  have htotal : totalPotential s = 0 := by
    simp [totalPotential, hzero]
  rw [htotal] at hmean
  exact zero_ne_one hmean

/-- The vertex-zero star potential. -/
def star0Potential {R : Type*} [Zero R] [One R] : Fin 6 → R :=
  ![1, 0, 0, 0, 0, 0]

/-- The three diagonal-side chord kills at vertex `0`, together with the
two C6 adjugate kills at that vertex, are a sufficient certified endpoint. -/
theorem no_normalized_diagonal_witness_of_star0_kills
    {R : Type*} [CommRing R] [Nontrivial R]
    (d : Fin 15 → R)
    (h01 : coSum d 0 = 0)
    (h02 : coSum d 1 = 0)
    (h03 : coSum d 2 = 0)
    (h04 : coSum d 3 = 0)
    (h05 : coSum d 4 = 0)
    (hmono : totalMatching (matchingProduct d) = 1) : False := by
  apply no_normalized_diagonal_witness_of_potential_kills
    (s := star0Potential) d
  · intro edge hactive
    fin_cases edge <;>
      simp [star0Potential, edgePotential] at hactive
    · exact h01
    · exact h02
    · exact h03
    · exact h04
    · exact h05
  · simp [star0Potential, totalPotential]
  · exact hmono

#print axioms Krenn.C6PotentialTargets.potential_zero_of_c6_chord_zero
#print axioms Krenn.C6PotentialTargets.no_mean_one_potential_supported_on_c6
#print axioms Krenn.C6PotentialTargets.no_normalized_diagonal_witness_of_star0_kills

end Krenn.C6PotentialTargets
