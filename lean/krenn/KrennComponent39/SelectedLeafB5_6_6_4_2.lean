import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_6_6_4_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b002a1dccb5711831070b8b8ec9c67129f3d27dcc5f2f36032c88cbc539ab784"
def certificateSHA256 : String := "d65560656f6b67d02bc1f45e3b9fc3624206a7bb43e3503287e864861fa02039"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 676 := ![
  10,
  20,
  27,
  191,
  193,
  304,
  305,
  425,
  440,
  476,
  477,
  511,
  566,
  602,
  603,
  659,
  660,
  662,
  664,
  666,
  667,
  669,
  670,
  671,
  672,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(10, 1), (34, 1), (36, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (34, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (34, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (14, 1), (34, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (34, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (16, 1), (20, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (33, 1), (36, 1), (47, 1)] }, { coefficient := 2, powers := [(14, 1), (16, 1), (20, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (20, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (20, 1), (47, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (12, 1), (20, 1), (42, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (33, 1), (36, 1), (42, 1)] }, { coefficient := 2, powers := [(12, 1), (14, 1), (20, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (20, 1), (42, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (20, 1), (42, 1), (67, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (33, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (20, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (47, 1)] }, { coefficient := -2, powers := [(14, 1), (20, 1), (47, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (47, 1), (67, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (36, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (17, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (33, 1), (36, 1)] }, { coefficient := -2, powers := [(14, 1), (17, 1), (20, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (20, 1), (67, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (12, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (33, 1), (36, 1)] }, { coefficient := -2, powers := [(12, 1), (14, 1), (20, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (20, 1), (67, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (23, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(38, 1), (39, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(39, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(39, 1), (55, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(43, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (10, 1), (20, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (33, 1), (34, 1), (36, 1)] }, { coefficient := -2, powers := [(8, 1), (14, 1), (20, 1), (34, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (20, 1), (34, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (20, 1), (34, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (33, 1), (34, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (10, 1), (20, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := -2, powers := [(2, 1), (14, 1), (20, 1), (40, 1), (51, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (20, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (20, 1), (40, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (33, 1), (36, 1), (40, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (20, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (31, 1), (33, 1), (36, 1)] }, { coefficient := -2, powers := [(5, 1), (14, 1), (20, 1), (31, 1), (51, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (31, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (31, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (38, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (20, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (33, 1), (36, 1), (60, 1)] }, { coefficient := -2, powers := [(5, 1), (14, 1), (20, 1), (51, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (33, 1), (36, 1), (60, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (20, 1), (42, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (20, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (33, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (33, 1), (36, 1), (47, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (20, 1), (47, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (33, 1), (36, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(10, 1), (17, 1), (20, 1), (46, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (17, 1), (33, 1), (36, 1), (46, 1), (49, 1)] }, { coefficient := -2, powers := [(12, 1), (14, 1), (20, 1), (42, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (20, 1), (42, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (20, 1), (42, 1), (46, 1), (67, 1)] }, { coefficient := 2, powers := [(12, 1), (14, 1), (20, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (20, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (20, 1), (47, 1), (67, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (33, 1), (36, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (33, 1), (36, 1), (47, 1)] }, { coefficient := -2, powers := [(14, 1), (16, 1), (20, 1), (47, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (20, 1), (47, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (20, 1), (47, 1), (49, 1), (67, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (33, 1), (36, 1), (47, 1), (49, 1)] }, { coefficient := 2, powers := [(14, 1), (17, 1), (20, 1), (46, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (20, 1), (46, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (20, 1), (46, 1), (49, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (33, 1), (36, 1), (46, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (10, 1), (20, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (33, 1), (36, 1), (37, 1)] }, { coefficient := -2, powers := [(2, 1), (14, 1), (20, 1), (37, 1), (51, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (20, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (14, 1), (20, 1), (37, 1), (67, 1)] }, { coefficient := -1, powers := [(2, 1), (14, 1), (33, 1), (36, 1), (37, 1)] }, { coefficient := -1, powers := [(8, 1), (10, 1), (20, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (10, 1), (22, 1), (33, 1), (36, 1)] }, { coefficient := -2, powers := [(8, 1), (14, 1), (20, 1), (22, 1), (51, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (20, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (14, 1), (20, 1), (22, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (22, 1), (33, 1), (36, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_6_6_4_2.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_6_6_4_2
