import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component1.SelectedLeafB7_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3c39ddfdaf37be4d2db24a7b2277e660f5fda263c90ca0688833ca8819d1cb11"
def certificateSHA256 : String := "1de5bf89fda34c160b210ae668d4071785c7ce727096115d96b5a5d538ed5314"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 37 → Fin 588 := ![
  0,
  1,
  4,
  14,
  15,
  25,
  31,
  32,
  37,
  39,
  48,
  55,
  225,
  230,
  245,
  260,
  262,
  276,
  354,
  364,
  366,
  370,
  384,
  385,
  399,
  442,
  503,
  507,
  511,
  556,
  562,
  578,
  580,
  581,
  583,
  584,
  587
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 37 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (39, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (44, 1)] }, { coefficient := 1, powers := [(29, 1), (49, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 37 → SparsePoly (Fin 61) := ![
  [{ coefficient := 2, powers := [(2, 1), (5, 1), (7, 1), (33, 1), (35, 1), (47, 1), (52, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 2), (7, 1), (32, 1), (33, 1), (36, 1), (52, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 2), (7, 1), (33, 1), (35, 1), (36, 1), (52, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 2), (7, 1), (30, 1), (32, 1), (33, 1), (52, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (23, 1), (33, 1), (52, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (33, 2), (47, 1), (52, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (53, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (45, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (29, 1), (33, 1), (53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (33, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (35, 1), (45, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (33, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (33, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (18, 1), (33, 1), (35, 1), (50, 1), (52, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (35, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (33, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (35, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (27, 1), (33, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (41, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (29, 1), (32, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (35, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (18, 1), (33, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (18, 1), (33, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (35, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (7, 1), (33, 1), (52, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (19, 1), (33, 2), (52, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 2), (7, 1), (32, 1), (33, 1), (52, 1), (53, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (52, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (32, 1), (33, 1), (47, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (30, 1), (32, 1), (33, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (19, 1), (32, 1), (33, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (19, 1), (33, 1), (35, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (14, 1), (32, 1), (33, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (5, 1), (7, 1), (33, 1), (35, 1), (52, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (33, 2), (52, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (33, 1), (35, 1), (50, 1), (52, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (18, 1), (33, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (12, 1), (35, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (33, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (7, 1), (32, 1), (33, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (5, 1), (7, 1), (33, 1), (35, 1), (39, 1), (52, 1), (53, 1), (56, 1)] }, { coefficient := -1, powers := [(2, 1), (5, 1), (7, 1), (33, 1), (35, 1), (47, 1), (50, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 2), (7, 1), (32, 1), (33, 1), (36, 1), (50, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 2), (7, 1), (33, 1), (35, 1), (36, 1), (50, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (33, 1), (38, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (33, 1), (41, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (33, 1), (44, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (33, 1), (49, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (33, 1), (35, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (27, 1), (33, 1), (49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (5, 1), (7, 1), (33, 1), (35, 1), (52, 1), (53, 2), (58, 1)] }, { coefficient := -1, powers := [(1, 1), (2, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (5, 1), (7, 1), (32, 1), (33, 1), (52, 1), (53, 2)] }, { coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (8, 1), (32, 1), (33, 1), (36, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (19, 1), (30, 1), (32, 1), (33, 1), (52, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (19, 1), (30, 1), (33, 1), (35, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }]
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
    ¬ ∀ index : Fin 37,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component1.SelectedLeafB7_2.selectedHasNoCommonZero

end Krenn.Component1.SelectedLeafB7_2
