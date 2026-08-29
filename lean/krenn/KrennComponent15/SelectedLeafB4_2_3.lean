import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB4_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "70a58cbd3a8fb02fc13d21f48156ffdbcafa6a21dbe8228464adce8b552931ab"
def certificateSHA256 : String := "78c1de9e4c0ecd107d183caacb163187cf9f3508ddbbd5645d2c5a20e3395199"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 595 := ![
  13,
  21,
  25,
  29,
  178,
  184,
  211,
  222,
  227,
  228,
  234,
  237,
  360,
  362,
  365,
  366,
  367,
  368,
  379,
  401,
  429,
  471,
  476,
  519,
  527,
  528,
  585,
  586,
  588,
  590,
  591,
  593
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (42, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (40, 1)] }, { coefficient := 1, powers := [(40, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (46, 1)] }, { coefficient := 1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1), (46, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(43, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (40, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(22, 1), (37, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(52, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 61) := ![
  [{ coefficient := 1, powers := [(3, 1), (12, 1), (21, 1), (29, 1), (53, 2)] }, { coefficient := -1, powers := [(3, 1), (29, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 2), (37, 1), (53, 2)] }, { coefficient := 1, powers := [(12, 1), (21, 2), (42, 1), (53, 2)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (26, 1), (44, 1), (53, 1), (57, 1)] }, { coefficient := -1, powers := [(21, 1), (37, 1), (53, 1)] }, { coefficient := -1, powers := [(21, 1), (42, 1), (53, 1)] }, { coefficient := 2, powers := [(26, 1), (44, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (18, 1), (21, 1), (26, 1), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(18, 1), (26, 1), (57, 1)] }],
  [{ coefficient := 3, powers := [(12, 1), (21, 2), (42, 1), (50, 1), (53, 1)] }, { coefficient := -2, powers := [(21, 1), (42, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (49, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (12, 1), (18, 1), (32, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (18, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1), (43, 1), (53, 2)] }, { coefficient := 1, powers := [(43, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (21, 2), (53, 2)] }, { coefficient := -1, powers := [(0, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (37, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(12, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 2), (21, 1), (53, 2)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 2), (17, 1), (21, 1), (53, 2)] }, { coefficient := 1, powers := [(12, 1), (17, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1), (49, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (12, 1), (18, 1), (26, 1), (32, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(12, 2), (21, 1), (26, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(12, 1), (26, 1), (57, 1)] }],
  [{ coefficient := -3, powers := [(12, 1), (16, 1), (21, 2), (42, 1), (53, 1)] }, { coefficient := 2, powers := [(16, 1), (21, 1), (42, 1)] }],
  [{ coefficient := -3, powers := [(12, 1), (21, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (29, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (21, 1), (26, 1), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (26, 1), (57, 1)] }, { coefficient := -1, powers := [(26, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 2), (53, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 3, powers := [(12, 1), (16, 1), (21, 2), (53, 1)] }, { coefficient := -2, powers := [(16, 1), (21, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (21, 1), (53, 2), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (53, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (53, 2), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (32, 1), (35, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(53, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 2), (21, 1), (53, 2)] }, { coefficient := -1, powers := [(12, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (12, 1), (32, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (12, 1), (26, 1), (32, 1), (53, 1)] }, { coefficient := -1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(12, 2), (21, 2), (53, 2)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 2), (21, 2), (53, 2)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (12, 1), (21, 1), (26, 1), (53, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (26, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (21, 1), (35, 1), (53, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (43, 1), (46, 1), (53, 2)] }, { coefficient := 3, powers := [(12, 1), (21, 1), (44, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (35, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(35, 1), (56, 1)] }, { coefficient := -1, powers := [(43, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(44, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (25, 1), (44, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (12, 1), (26, 1), (32, 1), (52, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (16, 1), (21, 1), (26, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (26, 1), (52, 1)] }, { coefficient := -2, powers := [(0, 1), (16, 1), (26, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (12, 1), (21, 1), (52, 1), (53, 2), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (52, 1), (53, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (12, 1), (21, 1), (52, 1), (53, 2), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (12, 1), (21, 1), (53, 2)] }, { coefficient := 1, powers := [(2, 1), (12, 1), (32, 1), (35, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(2, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := -1, powers := [(8, 1), (12, 1), (21, 1), (32, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (16, 1), (21, 1), (26, 1), (53, 1)] }, { coefficient := 2, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (12, 1), (21, 1), (29, 1), (53, 2), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (29, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 2), (21, 2), (53, 2), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (21, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (21, 1), (29, 1), (53, 2)] }, { coefficient := 1, powers := [(5, 1), (12, 1), (29, 1), (32, 1), (35, 1), (53, 1)] }, { coefficient := -1, powers := [(5, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 2), (21, 2), (53, 2)] }, { coefficient := 1, powers := [(12, 2), (21, 1), (32, 1), (35, 1), (53, 1)] }, { coefficient := -1, powers := [(12, 1), (21, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB4_2_3.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB4_2_3
