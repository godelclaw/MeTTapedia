import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component54.SelectedLeafB7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "13d36c8bf011103f88617de05533efab1c9519f9d3f066cf140853b53549f7d2"
def certificateSHA256 : String := "49909dea9c21a383196e628b88be7044f6c72cd5546145adf21934f798b0d4c9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 21 → Fin 642 := ![
  2,
  3,
  6,
  9,
  11,
  196,
  203,
  204,
  214,
  348,
  350,
  359,
  360,
  364,
  366,
  383,
  384,
  473,
  638,
  639,
  641
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (57, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (54, 1)] }, { coefficient := 1, powers := [(20, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(20, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (21, 1), (37, 1), (42, 1), (57, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (21, 1), (36, 1), (37, 1), (54, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (30, 1), (37, 1), (42, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (27, 1), (37, 1), (42, 1), (59, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (26, 1), (37, 1), (48, 1), (54, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (26, 1), (33, 1), (37, 1), (48, 1), (59, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (33, 1), (37, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (37, 1), (41, 1), (42, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (37, 1), (42, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (37, 1), (42, 1), (46, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (42, 1), (44, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (37, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (52, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (37, 1), (52, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (37, 1), (46, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (37, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (14, 1), (37, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (36, 1), (37, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (37, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (37, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (42, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (37, 1), (42, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (41, 1), (42, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (21, 1), (37, 1), (42, 1), (46, 1), (57, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (26, 1), (37, 1), (48, 1), (52, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (27, 1), (37, 1), (42, 1), (47, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (21, 1), (36, 1), (37, 1), (46, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (26, 1), (33, 1), (37, 1), (48, 1), (52, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (30, 1), (37, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component54.SelectedLeafB7.selectedHasNoCommonZero

end Krenn.Component54.SelectedLeafB7
