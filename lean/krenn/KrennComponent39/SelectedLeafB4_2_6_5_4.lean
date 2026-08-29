import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_2_6_5_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f4895d3eaf4297cad3af45aabd97307158f63bfcc68e2dea7919dc94cdd2c6c3"
def certificateSHA256 : String := "6ef942df1987ec7e438b941f97c9403beb048b1b00346fcca1e4cce2f98402ff"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 676 := ![
  10,
  180,
  187,
  191,
  250,
  302,
  304,
  305,
  313,
  318,
  425,
  439,
  440,
  515,
  523,
  580,
  581,
  602,
  603,
  604,
  618,
  620,
  637,
  659,
  660,
  661,
  662,
  663,
  666,
  669,
  670,
  671,
  672,
  674,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(14, 1), (34, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (49, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (44, 1), (49, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (47, 1)] }, { coefficient := -1, powers := [(17, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (34, 1), (37, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (54, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (34, 1), (37, 1), (51, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (37, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (34, 1), (37, 1), (49, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (39, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (44, 2), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (44, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (34, 1), (37, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (16, 1), (34, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (34, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (44, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (34, 1), (35, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (34, 1), (35, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (34, 1), (35, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (23, 1), (34, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (23, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (23, 1), (34, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (20, 1), (28, 1), (34, 1), (54, 1), (66, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (20, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (34, 1), (37, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (18, 1), (34, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (18, 1), (34, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (34, 1), (37, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (28, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1)] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_2_6_5_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_2_6_5_4
