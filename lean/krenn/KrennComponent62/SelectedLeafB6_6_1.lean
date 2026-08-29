import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB6_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1a8e8fa9b895b89921d2c9ad8c76dbe1649ae65f7437fd022d97f9fab3fe3ec2"
def certificateSHA256 : String := "e178c222446c54d00b746110948355ffd7df29a3edd7cde34ba4803fe2618cc4"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 6 → Fin 667 := ![
  10,
  128,
  265,
  659,
  661,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 6 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(10, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (24, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(1, 1), (37, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(37, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 6 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (49, 1), (61, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (49, 1), (61, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(61, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(1, 1), (56, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (61, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 6,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB6_6_1.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB6_6_1
