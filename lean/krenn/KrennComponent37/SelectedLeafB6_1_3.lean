import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB6_1_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "625d44e61470dd8d752de0ad4dfecb371ecb2c9c24eed23e499572f3b17bb271"
def certificateSHA256 : String := "450b7e5524353e840871e1a7fffcf67b69cec6e0cabbe367978a2e84c040b16a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 10 → Fin 667 := ![
  3,
  4,
  297,
  424,
  480,
  608,
  659,
  662,
  663,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 10 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 10 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(25, 1), (47, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (47, 1), (48, 1), (63, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (47, 1), (63, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (48, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(54, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (47, 1), (48, 1), (55, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (47, 1), (55, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (47, 1), (54, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (44, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (47, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 10,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB6_1_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB6_1_3
