import KrennC6PotentialTargets
import KrennFrozenCase0AdjugateLayer
import Mathlib

/-!
The exact semantic connector from a fixed C6 non-collapse slot to the doily
star endpoint.

This is intentionally conditional on the three chord co-sum kills which the
balanced-layer argument still has to harvest.  It proves that those kills are
the right missing interface: a nonzero determinant at slot `(0,0)` supplies
the two C6-side kills, while the original frozen monochromatic row supplies
normalization.
-/

namespace Krenn.FrozenCase0StarConnector

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.DoilyPotential
open Krenn.FrozenCase0AdjugateLayer

/-- The colour-zero diagonal of the 75-coordinate frozen C6 case-0 system,
in the lexicographic fifteen-edge order used by `KrennDoilyPotential`. -/
def diagonal0 {R : Type*} [CommRing R] (values : Fin 75 → R) : Fin 15 → R :=
  ![values 0, values 3, values 6, values 9, values 17,
    values 25, values 33, values 41, values 44, values 47,
    values 50, values 53, values 61, values 69, values 72]

/-- Slot `(0,0)`'s left adjugate kill is exactly the `04` diagonal co-sum. -/
theorem slot0_left_eq_coSum04 {R : Type*} [CommRing R]
    (values : Fin 75 → R) :
    slotLeft values 0 = coSum (diagonal0 values) 3 := by
  simp [slotLeft, diagonal0, coSum]

/-- Slot `(0,0)`'s right adjugate kill is exactly the `05` diagonal co-sum. -/
theorem slot0_right_eq_coSum05 {R : Type*} [CommRing R]
    (values : Fin 75 → R) :
    slotRight values 0 = coSum (diagonal0 values) 4 := by
  simp [slotRight, diagonal0, coSum]

/- Frozen source row 744 is the colour-zero monochromatic equation. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem mono0_source_eq {R : Type*} [CommRing R]
    (values : Fin 75 → R) :
    sourceValue values 744 =
      totalMatching (matchingProduct (diagonal0 values)) - 1 := by
  simp [sourceValue, diagonal0, totalMatching, matchingProduct,
    Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly] <;>
    ring

/-- The monochromatic source row is retained by the pre-collapse base
system; it is not one of the eighteen added determinant rows. -/
theorem mono0_source_not_determinant (slot : Fin 18) :
    determinantSourceIndex slot ≠ 744 := by
  fin_cases slot <;> decide

/-- A nonzero determinant in slot `(0,0)` plus the three diagonal-side
chord P-kills at the same vertex gives a direct contradiction. -/
theorem no_base_witness_of_slot0_noncollapse_and_star_chord_kills
    {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R] [CharZero R]
    (values : Fin 75 → R)
    (base : BaseCommonZero values)
    (hdet : slotDeterminant values 0 ≠ 0)
    (h01 : coSum (diagonal0 values) 0 = 0)
    (h02 : coSum (diagonal0 values) 1 = 0)
    (h03 : coSum (diagonal0 values) 2 = 0) : False := by
  have h04 : coSum (diagonal0 values) 3 = 0 := by
    rw [← slot0_left_eq_coSum04]
    exact (left_kill_or_collapse values base 0).resolve_left hdet
  have h05 : coSum (diagonal0 values) 4 = 0 := by
    rw [← slot0_right_eq_coSum05]
    exact (right_kill_or_collapse values base 0).resolve_left hdet
  have hsource := base 744 mono0_source_not_determinant
  rw [mono0_source_eq] at hsource
  have hmono : totalMatching (matchingProduct (diagonal0 values)) = 1 := by
    linear_combination hsource
  exact Krenn.C6PotentialTargets.no_normalized_diagonal_witness_of_star0_kills
    (diagonal0 values) h01 h02 h03 h04 h05 hmono

#print axioms Krenn.FrozenCase0StarConnector.slot0_left_eq_coSum04
#print axioms Krenn.FrozenCase0StarConnector.slot0_right_eq_coSum05
#print axioms Krenn.FrozenCase0StarConnector.mono0_source_eq
#print axioms Krenn.FrozenCase0StarConnector.no_base_witness_of_slot0_noncollapse_and_star_chord_kills

end Krenn.FrozenCase0StarConnector
