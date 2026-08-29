import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_7_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "12ed68a6cb6d474f0f3b9baefa01fa4311ec6dd85d5386196bfcc4a1bbbd5d72"
def certificateSHA256 : String := "2e9228c0cd0fd9f67e053a1da69502805fbc481354e2351c9f4932876d63e3ba"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 667 := ![
  7,
  16,
  19,
  23,
  27,
  171,
  175,
  179,
  180,
  182,
  283,
  298,
  299,
  359,
  393,
  433,
  438,
  446,
  450,
  590,
  604,
  605,
  656,
  657,
  659,
  660,
  661,
  663,
  665,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(8, 1), (32, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(22, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(10, 1), (33, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(10, 1), (36, 1), (38, 1), (42, 1)] }, { coefficient := -1, powers := [(15, 1), (33, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (36, 1), (38, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (24, 1), (32, 1), (38, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (30, 1), (32, 1), (38, 1), (49, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (32, 1), (36, 1), (38, 1), (39, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (30, 1), (32, 1), (38, 1), (49, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (32, 1), (38, 1), (44, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (25, 1), (30, 1), (32, 1), (38, 1), (49, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (32, 1), (36, 1), (38, 1), (39, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (32, 1), (38, 1), (49, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (21, 1), (30, 1), (32, 1), (38, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (24, 1), (26, 1), (32, 1), (38, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (32, 1), (38, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (30, 1), (32, 1), (38, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (26, 1), (32, 1), (38, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (32, 1), (38, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (44, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (52, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (51, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (41, 1), (51, 1), (65, 1)] }, { coefficient := 2, powers := [(10, 1), (46, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (41, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (26, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(15, 1), (24, 1), (26, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (30, 1), (32, 1), (38, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (36, 1), (38, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (32, 1), (38, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (36, 1), (38, 1), (39, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (18, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (32, 1), (38, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (18, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (41, 1), (65, 1)] }, { coefficient := -2, powers := [(10, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (41, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (52, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (30, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (36, 1), (38, 1), (39, 1)] }, { coefficient := -1, powers := [(15, 1), (30, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (36, 1), (38, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (30, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (30, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (24, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(10, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(10, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [(41, 1), (42, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(41, 1), (48, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(41, 1), (57, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (39, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (38, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (38, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (42, 1), (58, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1), (49, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (18, 1), (24, 1), (32, 1), (38, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (25, 1), (30, 1), (32, 1), (38, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (25, 1), (32, 1), (36, 1), (38, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (30, 1), (32, 1), (38, 1), (49, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (21, 1), (30, 1), (32, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (19, 1), (24, 1), (26, 1), (32, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(10, 1), (19, 1), (24, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (24, 1), (32, 1), (38, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (25, 1), (30, 1), (32, 1), (38, 1), (49, 1), (53, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (25, 1), (32, 1), (36, 1), (38, 1), (39, 1), (53, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (30, 1), (32, 1), (38, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (21, 1), (30, 1), (32, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(15, 1), (19, 1), (24, 1), (26, 1), (32, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (24, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (27, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (41, 1)] }, { coefficient := 2, powers := [(10, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := -1, powers := [(10, 1), (12, 1), (20, 1), (30, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := 1, powers := [(10, 1), (12, 1), (20, 1), (32, 1), (36, 1), (38, 1), (39, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1)] }, { coefficient := 1, powers := [(12, 1), (15, 1), (20, 1), (30, 1), (32, 1), (38, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (15, 1), (20, 1), (32, 1), (36, 1), (38, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (22, 1), (60, 1)] }, { coefficient := 1, powers := [(10, 1), (22, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_7_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_7_5
