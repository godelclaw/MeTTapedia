import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component13.SelectedLeafB7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "aed66970a28f86502fab8ea563d4e2cd28c04d85b03e59e9d66e0252780eabd2"
def certificateSHA256 : String := "f79f39bcce86ec3762e9c07d7f551709b0294a6a15887ea692c216ae903bebf5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 608 := ![
  5,
  7,
  13,
  17,
  19,
  150,
  154,
  155,
  156,
  160,
  162,
  170,
  171,
  173,
  174,
  175,
  177,
  182,
  187,
  188,
  193,
  196,
  202,
  284,
  290,
  325,
  357,
  360,
  361,
  385,
  464,
  482,
  488,
  498,
  565,
  604,
  605,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(11, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (34, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (45, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(2, 1), (16, 1), (24, 1), (30, 1), (34, 1), (44, 1), (50, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (36, 1), (47, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (24, 1), (34, 1), (51, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (34, 1), (51, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (16, 1), (19, 1), (33, 1), (34, 1), (44, 1), (50, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (30, 1), (34, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (33, 1), (34, 1), (44, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (12, 1), (33, 1), (34, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (30, 1), (34, 1), (43, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (16, 1), (30, 1), (34, 1), (44, 1), (50, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (36, 1), (47, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 2), (34, 1), (51, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (34, 1), (51, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (16, 1), (33, 1), (34, 1), (44, 1), (50, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (27, 1), (34, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (30, 1), (34, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (34, 1), (51, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (34, 1), (44, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (22, 1), (34, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (30, 1), (34, 1), (45, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (33, 1), (34, 1), (39, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (18, 1), (33, 1), (34, 1), (44, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (33, 1), (34, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (33, 1), (34, 1), (43, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (33, 1), (34, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (30, 1), (34, 1), (44, 1), (49, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (33, 1), (34, 1), (39, 1), (43, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (30, 1), (34, 1), (44, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (18, 1), (30, 1), (34, 1), (44, 1), (49, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (23, 1), (30, 1), (34, 1), (44, 1), (49, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (30, 1), (34, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (23, 1), (30, 1), (34, 1), (44, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (16, 1), (23, 1), (60, 2)] }],
  [{ coefficient := -1, powers := [(2, 1), (12, 1), (16, 1), (23, 1), (33, 1), (34, 1), (44, 1), (50, 1), (60, 2)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (17, 1), (23, 1), (30, 1), (34, 1), (44, 1), (50, 1), (60, 2)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (23, 1), (60, 2)] }],
  [{ coefficient := 1, powers := [(2, 1), (16, 1), (23, 1), (34, 1), (44, 1), (57, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (12, 1), (33, 1), (34, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (30, 1), (34, 1), (58, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (12, 1), (33, 1), (34, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (17, 1), (30, 1), (34, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (33, 1), (34, 1), (44, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (33, 1), (34, 1), (44, 1), (50, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (30, 1), (34, 1), (44, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (12, 1), (23, 1), (33, 1), (34, 1), (44, 1), (50, 1), (60, 2)] }, { coefficient := 1, powers := [(2, 1), (17, 1), (23, 1), (30, 1), (34, 1), (44, 1), (50, 1), (60, 2)] }],
  [{ coefficient := -1, powers := [(2, 1), (27, 1), (34, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (22, 1), (34, 1), (56, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (34, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (60, 2)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (60, 2)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (34, 1), (44, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (44, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (23, 1), (60, 2)] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 2)] }],
  [{ coefficient := -1, powers := [(2, 1), (34, 1), (57, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (34, 1), (56, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (12, 1), (33, 1), (34, 1), (36, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (12, 1), (33, 1), (34, 1), (44, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (17, 1), (30, 1), (34, 1), (36, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (17, 1), (30, 1), (34, 1), (44, 1), (50, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(2, 2), (34, 1), (45, 1), (51, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (30, 1), (34, 1), (41, 1), (44, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (33, 1), (34, 1), (44, 1), (47, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (34, 1), (39, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (12, 1), (23, 1), (33, 1), (34, 1), (43, 1), (44, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (17, 1), (23, 1), (30, 1), (34, 1), (43, 1), (44, 1), (50, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (34, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (34, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 61 → R) :
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component13.SelectedLeafB7.selectedHasNoCommonZero

end Krenn.Component13.SelectedLeafB7
