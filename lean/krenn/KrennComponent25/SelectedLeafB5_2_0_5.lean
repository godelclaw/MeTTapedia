import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_2_0_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2dacf47af25bd60b36db75f0156037d28f7d26bb45d5d4c68eec6d7138b3d544"
def certificateSHA256 : String := "768cfd925c702a838853f5bcd602f7967a3dc05d2d1a560d50c57641200519e9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 41 → Fin 668 := ![
  1,
  14,
  20,
  21,
  142,
  152,
  162,
  168,
  169,
  170,
  173,
  177,
  238,
  300,
  306,
  312,
  316,
  349,
  388,
  425,
  430,
  435,
  450,
  467,
  513,
  578,
  579,
  580,
  601,
  646,
  653,
  655,
  656,
  658,
  659,
  661,
  662,
  663,
  664,
  665,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 41 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(9, 1), (29, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (49, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 41 → SparsePoly (Fin 66) := ![
  [{ coefficient := -2, powers := [(3, 1), (23, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (11, 1), (27, 1), (48, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (16, 1), (27, 1), (48, 1), (49, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (30, 1), (48, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(2, 1), (9, 1), (24, 1), (48, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (29, 1), (50, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (29, 1), (50, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (6, 1), (48, 1), (52, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (13, 1), (30, 1), (48, 1), (52, 1)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (48, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (13, 1), (48, 1), (49, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (13, 1), (24, 1), (48, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(2, 1), (24, 1), (42, 1), (48, 1), (54, 1), (65, 1)] }, { coefficient := -2, powers := [(2, 1), (33, 1), (36, 1), (48, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (19, 1), (54, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (3, 1), (24, 1), (48, 1), (54, 1), (58, 1), (65, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (13, 1), (24, 1), (30, 1), (48, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (3, 1), (48, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (13, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (48, 1), (49, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (24, 1), (48, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (48, 1), (49, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (29, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (3, 1), (48, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (13, 1), (30, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (6, 1), (48, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (6, 1), (13, 1), (30, 1), (48, 1), (54, 1)] }, { coefficient := -2, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (13, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (48, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (48, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (36, 1), (48, 1), (54, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 1), (15, 1), (27, 1), (48, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (33, 1), (48, 1), (54, 1)] }, { coefficient := 2, powers := [(2, 1), (24, 1), (29, 1), (42, 1), (48, 1), (54, 1), (65, 1)] }, { coefficient := 2, powers := [(2, 1), (29, 1), (33, 1), (36, 1), (48, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (2, 2), (39, 1), (48, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (11, 1), (22, 1), (48, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (16, 1), (22, 1), (48, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (39, 1), (48, 1), (54, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (30, 1), (48, 1), (54, 1)] }, { coefficient := -2, powers := [(2, 1), (9, 1), (18, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (6, 1), (18, 1), (48, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(2, 1), (6, 1), (13, 1), (18, 1), (30, 1), (48, 1), (54, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (29, 1), (48, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (29, 1), (48, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (23, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (22, 1), (54, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (19, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := -2, powers := [(3, 1), (12, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1)] }, { coefficient := -1, powers := [(16, 1), (22, 1), (23, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 1), (3, 1), (24, 1), (40, 1), (48, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (3, 1), (24, 1), (45, 1), (48, 1), (54, 1), (58, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (11, 1), (27, 1), (42, 1), (48, 1), (54, 1), (62, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (16, 1), (27, 1), (42, 1), (48, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (29, 1), (47, 1), (50, 1), (64, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (13, 1), (24, 1), (30, 1), (40, 1), (48, 1), (54, 1)] }, { coefficient := -2, powers := [(2, 1), (3, 1), (13, 1), (24, 1), (30, 1), (45, 1), (48, 1), (54, 1)] }, { coefficient := 2, powers := [(2, 1), (3, 1), (24, 1), (48, 1), (54, 1), (58, 1)] }, { coefficient := 2, powers := [(2, 1), (6, 1), (30, 1), (42, 1), (48, 1), (54, 1)] }, { coefficient := -2, powers := [(2, 1), (9, 1), (13, 1), (24, 1), (48, 1), (54, 1)] }, { coefficient := 2, powers := [(2, 1), (9, 1), (24, 1), (42, 1), (48, 1), (54, 1)] }, { coefficient := 2, powers := [(2, 1), (9, 1), (33, 1), (36, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (19, 1), (43, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [(17, 1), (24, 1), (29, 1), (47, 1), (50, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 41,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_2_0_5.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_2_0_5
