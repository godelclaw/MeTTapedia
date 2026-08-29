import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB6_3_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9c45d0bca3c81c8c81f2f0bb6811b5304bd6f9a4d251847dd4efb6191d31649c"
def certificateSHA256 : String := "26ff66c7035ce139ae167c7d366a4dfe15e5f1de2a03219297f322104d56cd2f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 670 := ![
  0,
  1,
  2,
  3,
  4,
  20,
  146,
  151,
  171,
  181,
  301,
  318,
  412,
  440,
  446,
  450,
  454,
  503,
  566,
  570,
  602,
  603,
  612,
  649,
  655,
  657,
  659,
  660,
  661,
  662,
  664,
  666,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (63, 1)] }],
  [{ coefficient := 4, powers := [(0, 1), (19, 1), (30, 1), (42, 1), (43, 1), (63, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (20, 1), (30, 1), (42, 1), (63, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 2), (30, 1), (42, 1), (45, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (30, 1), (42, 1), (43, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (30, 1), (42, 1), (43, 1), (63, 1)] }, { coefficient := 2, powers := [(19, 1), (30, 1), (34, 1), (37, 1), (42, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (28, 1), (42, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1), (44, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (37, 1), (42, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (29, 1), (42, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(13, 1), (20, 1), (30, 1), (42, 1)] }, { coefficient := 2, powers := [(20, 2), (30, 1), (42, 1), (45, 1)] }, { coefficient := -2, powers := [(20, 1), (30, 1), (42, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (21, 1), (30, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (26, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (25, 1), (30, 1), (42, 1), (43, 1), (68, 1)] }, { coefficient := -2, powers := [(19, 1), (30, 1), (34, 1), (37, 1), (42, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (26, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (25, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (19, 1), (30, 1), (42, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(13, 1), (30, 1), (42, 1)] }, { coefficient := -2, powers := [(20, 1), (30, 1), (42, 1), (45, 1)] }, { coefficient := 2, powers := [(30, 1), (42, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (42, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (30, 1), (42, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (20, 1), (30, 1), (42, 1), (45, 1)] }, { coefficient := -2, powers := [(19, 1), (30, 1), (42, 1), (43, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (20, 1), (30, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(0, 1), (19, 1), (30, 1), (37, 1), (42, 1), (59, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (30, 1), (42, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := -2, powers := [(13, 1), (19, 1), (20, 1), (30, 1), (42, 1), (50, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (42, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (42, 1), (44, 1), (54, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (36, 1), (37, 1), (42, 1), (54, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 2), (30, 1), (42, 1), (45, 1), (50, 1)] }, { coefficient := -2, powers := [(19, 1), (20, 1), (30, 1), (42, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (30, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (26, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (30, 1), (42, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (42, 1), (54, 1), (64, 1)] }, { coefficient := -2, powers := [(19, 1), (30, 1), (34, 1), (37, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [(41, 1), (42, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(42, 1), (47, 1), (54, 1), (64, 1)] }, { coefficient := 1, powers := [(42, 1), (58, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (1, 1), (19, 1), (30, 1), (42, 1), (56, 1), (63, 1)] }, { coefficient := -2, powers := [(0, 1), (19, 1), (30, 1), (42, 1), (56, 1)] }, { coefficient := -2, powers := [(6, 1), (19, 1), (30, 1), (34, 1), (42, 1)] }, { coefficient := 2, powers := [(13, 1), (19, 1), (25, 1), (30, 1), (42, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (30, 2), (42, 1), (43, 1), (68, 1)] }, { coefficient := 2, powers := [(19, 1), (30, 2), (34, 1), (37, 1), (42, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1), (44, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (19, 1), (30, 1), (31, 1), (42, 1)] }, { coefficient := 2, powers := [(19, 1), (20, 1), (30, 1), (42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (19, 1), (21, 1), (30, 1), (63, 1)] }, { coefficient := -1, powers := [(11, 1), (19, 1), (24, 1), (26, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(9, 1), (19, 1), (25, 1), (30, 1), (42, 1), (43, 1)] }, { coefficient := 2, powers := [(9, 1), (19, 1), (30, 1), (34, 1), (37, 1), (42, 1)] }]
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
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB6_3_2_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB6_3_2_5
