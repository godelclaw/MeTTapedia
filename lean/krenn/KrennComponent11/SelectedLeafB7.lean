import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "37ac1e4d43cfd826099d095f39e354e4ef8893ffade4a7cda8f2e821cb2564cf"
def certificateSHA256 : String := "bbcd17b8b4411514914db802cc04fc744f4756f8c7fe20ad4ff923bc246ffb7d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 666 := ![
  1,
  3,
  4,
  6,
  7,
  10,
  12,
  30,
  163,
  175,
  179,
  186,
  192,
  262,
  286,
  328,
  329,
  330,
  341,
  343,
  453,
  487,
  594,
  662,
  663,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(0, 2), (2, 1), (37, 1), (49, 1), (54, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 2), (37, 1), (49, 1), (54, 1), (59, 1), (63, 2)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (17, 1), (23, 1), (37, 1), (54, 1), (59, 1), (63, 2)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (19, 1), (37, 1), (44, 1), (54, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (12, 1), (18, 1), (30, 1), (37, 1), (49, 1), (59, 1), (63, 2)] }, { coefficient := -1, powers := [(2, 1), (12, 1), (18, 1), (36, 1), (37, 1), (39, 1), (59, 1), (63, 2)] }],
  [{ coefficient := 1, powers := [(2, 1), (17, 1), (24, 1), (30, 1), (37, 1), (42, 1), (59, 1), (63, 2)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (39, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (28, 1), (37, 1), (53, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (30, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (37, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (39, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (23, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (37, 1), (42, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (23, 1), (37, 1), (47, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (37, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (53, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (30, 1), (37, 1), (49, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (18, 1), (36, 1), (37, 1), (39, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (30, 1), (37, 1), (42, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (49, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 2), (37, 1), (49, 1), (59, 1), (63, 1)] }, { coefficient := 2, powers := [(2, 1), (17, 1), (23, 1), (37, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (37, 1), (44, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 2)] }],
  [{ coefficient := 1, powers := [(2, 1), (30, 1), (37, 1), (49, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (37, 1), (39, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (30, 1), (37, 1), (42, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (54, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (49, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (30, 1), (37, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (17, 1), (37, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (23, 1), (37, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (42, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (37, 1), (46, 1), (49, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 2), (37, 1), (46, 1), (49, 1), (54, 1), (59, 1), (63, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (17, 1), (23, 1), (37, 1), (46, 1), (54, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (19, 1), (37, 1), (44, 1), (46, 1), (54, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (12, 1), (18, 1), (30, 1), (37, 1), (46, 1), (49, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(2, 1), (12, 1), (18, 1), (36, 1), (37, 1), (39, 1), (46, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (24, 1), (30, 1), (37, 1), (42, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (42, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB7.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB7
