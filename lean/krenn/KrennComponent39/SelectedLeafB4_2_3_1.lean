import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB4_2_3_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3df347b63eb7be81c0cc87725713ba9ce6f46bb04c69bc7117323c757d1b3a13"
def certificateSHA256 : String := "72a05a818f6256f5760fe96889c8efef38561001941582ee7849ffdb7d4618c3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 673 := ![
  14,
  26,
  170,
  181,
  187,
  232,
  277,
  280,
  300,
  301,
  304,
  305,
  313,
  317,
  319,
  324,
  382,
  396,
  397,
  430,
  434,
  452,
  511,
  520,
  602,
  603,
  651,
  659,
  660,
  662,
  663,
  666,
  668,
  669,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 36 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (45, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (34, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (24, 1), (34, 1), (44, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (24, 1), (34, 1), (54, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (26, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (30, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (33, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (27, 1), (33, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (10, 1), (34, 1), (42, 1), (54, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (51, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (45, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (44, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (54, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (34, 1), (54, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (51, 2), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (51, 1), (53, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (34, 1), (37, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (34, 1), (37, 1), (44, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (31, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (44, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (34, 1), (37, 1), (44, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (57, 1)] }, { coefficient := -1, powers := [(27, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (22, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (46, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (52, 1), (57, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (22, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (44, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (39, 1), (54, 1)] }, { coefficient := -2, powers := [(5, 1), (20, 1), (34, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (34, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (34, 1), (36, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (34, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (34, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (44, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (60, 1)] }, { coefficient := -1, powers := [(40, 1), (56, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(40, 1), (57, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (27, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (34, 1), (37, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (20, 1), (34, 1), (39, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(4, 1), (5, 1), (20, 1), (34, 1), (51, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (20, 1), (34, 1), (54, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (34, 1), (36, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (39, 1), (44, 1), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (20, 1), (34, 1), (44, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (33, 1), (34, 1), (36, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (39, 2), (54, 1)] }, { coefficient := 2, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (39, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (20, 1), (34, 1), (39, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (33, 1), (34, 1), (36, 1), (39, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (24, 1), (42, 1), (51, 2), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (42, 1), (51, 1), (53, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (34, 1), (37, 1), (42, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (34, 1), (37, 1), (42, 1), (44, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (22, 1), (39, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (22, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (27, 1), (39, 1), (46, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1), (27, 1), (44, 1), (46, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (39, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (44, 1), (52, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (31, 1), (37, 1), (45, 1)] }, { coefficient := -1, powers := [(17, 1), (31, 1), (37, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (34, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (34, 1), (44, 1), (54, 1)] }]
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
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB4_2_3_1.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB4_2_3_1
