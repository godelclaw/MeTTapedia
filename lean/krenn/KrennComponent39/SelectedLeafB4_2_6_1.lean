import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_2_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3e4533e943c0d97e301675d309dc1d7d19d4d4d094c349c6adc6c01fac682048"
def certificateSHA256 : String := "1dd9aa5b3f42c60065a6595f778561b044801154d0e20ae10dbdece2017c9154"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 673 := ![
  10,
  11,
  21,
  277,
  301,
  304,
  305,
  318,
  324,
  383,
  396,
  397,
  430,
  511,
  515,
  523,
  529,
  542,
  561,
  602,
  603,
  659,
  660,
  662,
  663,
  666,
  667,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(4, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (22, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (10, 1), (22, 1), (51, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (53, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (31, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (44, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1), (49, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (34, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (22, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (20, 1), (22, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (33, 1), (36, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (10, 1), (22, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (37, 1), (49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (28, 1), (34, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (22, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (44, 1), (51, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (20, 1), (34, 1), (39, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (20, 1), (34, 1), (44, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(4, 1), (5, 1), (20, 1), (34, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (20, 1), (34, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (34, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (20, 1), (22, 1), (51, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (20, 1), (22, 1), (56, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (22, 1), (33, 1), (36, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (39, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (44, 2), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (44, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (33, 1), (34, 1), (36, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (39, 2), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (39, 1), (44, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (39, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (33, 1), (34, 1), (36, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (22, 1), (44, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (20, 1), (22, 1), (44, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (33, 1), (36, 1), (44, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (20, 1), (22, 1), (39, 1), (51, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (20, 1), (22, 1), (39, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (22, 1), (33, 1), (36, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (34, 1), (37, 1), (39, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (37, 1), (45, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (37, 1), (39, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (43, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (37, 1), (44, 1), (49, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (39, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (22, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (34, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (22, 1), (44, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (22, 1), (44, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (20, 1), (34, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (51, 1), (54, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_2_6_1.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_2_6_1
