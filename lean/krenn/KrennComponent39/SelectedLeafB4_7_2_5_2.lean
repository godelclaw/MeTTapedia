import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_7_2_5_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ad3b99f76c78a01b3a92b635d7d087a2c5c01180c3d49448cc1774729360f79c"
def certificateSHA256 : String := "63d003bf6c135c9d3fcdcb90c4f2aec540731906572dbc13fe8158b741571fe3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 42 → Fin 676 := ![
  10,
  11,
  19,
  180,
  181,
  187,
  189,
  197,
  268,
  300,
  301,
  302,
  303,
  304,
  305,
  316,
  318,
  324,
  360,
  397,
  434,
  463,
  476,
  515,
  521,
  523,
  537,
  602,
  603,
  659,
  660,
  661,
  662,
  663,
  664,
  666,
  668,
  669,
  670,
  671,
  672,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 42 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (37, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 42 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(4, 1), (34, 1), (51, 1), (54, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (19, 1), (33, 1), (36, 1), (39, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (19, 1), (33, 1), (36, 1), (44, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (39, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (44, 1), (64, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (36, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (34, 1), (37, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (22, 1), (30, 1), (45, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (22, 1), (30, 1), (42, 1), (54, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (28, 1), (30, 1), (47, 1), (49, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (34, 1), (37, 1), (49, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (34, 1), (37, 1), (49, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (28, 1), (30, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (34, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (33, 1), (36, 1), (39, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (36, 1), (44, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (39, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (44, 1), (64, 1)] }, { coefficient := -2, powers := [(20, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (16, 1), (22, 1), (30, 1), (54, 1), (56, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (12, 1), (28, 1), (30, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (16, 1), (28, 1), (30, 1), (47, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (33, 1), (34, 1), (37, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (16, 1), (22, 1), (30, 1), (45, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (23, 1), (28, 1), (30, 1), (40, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (28, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (30, 1), (40, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (22, 1), (30, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (16, 1), (22, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (33, 1), (36, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (30, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (54, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (28, 1), (33, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (28, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (16, 1), (22, 1), (30, 1), (42, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (28, 1), (30, 1), (47, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (16, 1), (33, 1), (34, 1), (37, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(38, 1), (39, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(39, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (37, 1), (56, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (40, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (47, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (44, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (30, 1), (34, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (16, 1), (22, 1), (30, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (33, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (33, 1), (34, 1), (37, 1), (49, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (34, 1), (54, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (34, 1), (46, 1), (54, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (38, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (33, 1), (36, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (39, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (23, 1), (28, 1), (30, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (28, 1), (30, 1), (56, 1)] }]
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
    ¬ ∀ index : Fin 42,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_7_2_5_2.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_7_2_5_2
