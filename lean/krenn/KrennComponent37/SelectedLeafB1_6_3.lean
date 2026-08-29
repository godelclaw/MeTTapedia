import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB1_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4e3a9695620b2dd496552a7e928fc4d3e7fa08f719d16adc8e0b59d7d6d6bac0"
def certificateSHA256 : String := "bb187208d4825b7137b96d51d3b031102b85be6d369c52df516f0b0631d41ab6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 11 → Fin 667 := ![
  16,
  313,
  435,
  453,
  466,
  475,
  608,
  658,
  660,
  661,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 11 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 11 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(20, 1), (23, 1), (41, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(54, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (23, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(41, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1), (23, 1), (41, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (23, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (29, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (52, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (1 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 11,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB1_6_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB1_6_3
