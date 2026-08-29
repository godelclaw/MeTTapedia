import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB0_0_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f3e0111cc072a25a35e389e346cc26abf9e5f9e5ef8576f2066e7d22e906557d"
def certificateSHA256 : String := "3c3499c80349fb978096ec1c16cac696a03dabe8a106e7bf7fb87d05f93d8829"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 11 → Fin 667 := ![
  294,
  313,
  424,
  472,
  475,
  608,
  645,
  658,
  662,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 11 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 11 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(52, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(54, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(26, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (44, 1), (54, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (38, 1), (44, 1), (54, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (38, 1), (58, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (44, 1), (46, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (46, 1), (52, 1), (58, 1), (63, 1)] }, { coefficient := 2, powers := [(25, 1), (47, 1), (52, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(47, 1), (54, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (44, 1), (54, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (46, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (52, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (57, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (26, 1), (44, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (26, 1), (47, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (58, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (44, 1), (54, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (58, 1), (63, 1)] }],
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 11,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB0_0_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB0_0_5
