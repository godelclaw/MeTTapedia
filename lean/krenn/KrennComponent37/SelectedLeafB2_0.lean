import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB2_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6f2a595731fa7eeb9e1b9a7cc805699a964ec5d4cd4c9596e5d1a77bbab835cd"
def certificateSHA256 : String := "3f2cdf3f24503120a0989fe116a6597c21976a3660f4370647a36448dd651e69"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 664 := ![
  0,
  1,
  2,
  3,
  4,
  6,
  13,
  148,
  149,
  171,
  174,
  181,
  221,
  222,
  317,
  358,
  410,
  425,
  444,
  446,
  450,
  454,
  475,
  515,
  566,
  580,
  602,
  603,
  608,
  655,
  657,
  658,
  659,
  660,
  661,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(9, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (26, 1), (48, 1)] }, { coefficient := 1, powers := [(31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (31, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (31, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (31, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (34, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1), (44, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(9, 1), (17, 1), (25, 1), (33, 1), (37, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (25, 1), (33, 1), (37, 1), (56, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (34, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (43, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (56, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (43, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (34, 1), (37, 1), (58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (24, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (33, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (21, 1), (33, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (33, 1), (37, 1), (49, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (43, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (19, 1), (33, 1), (37, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (33, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (33, 1), (37, 1), (43, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (25, 1), (33, 1), (37, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (56, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (33, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (19, 1), (33, 1), (37, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (33, 1), (37, 1)] }, { coefficient := -1, powers := [(33, 1), (37, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (21, 1), (33, 1), (37, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (18, 1), (33, 1), (37, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (33, 1), (37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (33, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (18, 1), (21, 1), (33, 1), (37, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (50, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (43, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (37, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (21, 1), (33, 1), (37, 1), (46, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (33, 1), (37, 1), (48, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (33, 1), (34, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (50, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (43, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (34, 1), (37, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(9, 1), (17, 1), (25, 1), (33, 1), (37, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(9, 1), (18, 1), (25, 1), (33, 1), (37, 1), (48, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := 1, powers := [(49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (33, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (33, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (25, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (26, 1), (33, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (26, 1), (33, 1), (37, 1), (49, 1)] }, { coefficient := -1, powers := [(13, 1), (19, 1), (26, 1), (33, 1), (37, 1), (48, 1)] }, { coefficient := -1, powers := [(17, 1), (21, 1), (26, 1), (33, 1), (37, 1), (47, 1)] }, { coefficient := -1, powers := [(18, 1), (26, 1), (33, 1), (37, 1), (43, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (33, 1), (37, 1), (43, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB2_0.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB2_0
