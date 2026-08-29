import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_2_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "dda93247fb6ca892c45465c259955b50c6c308d38005f18bece693ab9226f4f1"
def certificateSHA256 : String := "c9e8084e0ba4ef92c638d481536f6326b76da77ad9fcb652c05ab3d8f0bbefa9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 670 := ![
  9,
  15,
  26,
  27,
  28,
  180,
  181,
  296,
  433,
  440,
  445,
  449,
  450,
  453,
  454,
  478,
  487,
  498,
  516,
  519,
  581,
  619,
  657,
  660,
  663,
  666,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (47, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (30, 1), (49, 1), (66, 1), (67, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (67, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (21, 1), (27, 1), (36, 1), (41, 1), (55, 1), (67, 2)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (27, 1), (36, 1), (46, 1), (55, 1), (67, 2)] }, { coefficient := -1, powers := [(3, 1), (27, 1), (36, 1), (48, 1), (55, 1), (67, 2)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (48, 1), (55, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (36, 1), (55, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (36, 1), (55, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (37, 1), (41, 1), (61, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (30, 1), (37, 1), (46, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(23, 1), (39, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (37, 1), (41, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (26, 1), (37, 1), (46, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (37, 1), (54, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (55, 1), (67, 1)] }, { coefficient := -1, powers := [(28, 1), (39, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(30, 1), (37, 1), (48, 1), (61, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (23, 1), (55, 1), (60, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (55, 1), (60, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (54, 1), (61, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (30, 1), (51, 1), (66, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (51, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (55, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (30, 1), (48, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(55, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (36, 1), (55, 1), (67, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (21, 1), (27, 1), (36, 1), (55, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (30, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (30, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (55, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (36, 1), (55, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (27, 1), (36, 1), (55, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(37, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (36, 1), (37, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (37, 1), (48, 1), (54, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (21, 1), (27, 1), (36, 1), (41, 1), (55, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (18, 1), (21, 1), (27, 1), (36, 1), (46, 1), (55, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (27, 1), (36, 1), (48, 1), (55, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (23, 1), (36, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (28, 1), (36, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (36, 1), (52, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (36, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (30, 1), (49, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (30, 1), (37, 1), (41, 1), (61, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (30, 1), (37, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (41, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (26, 1), (37, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (37, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (37, 1), (48, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (30, 1), (48, 1), (51, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (48, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_2_2_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_2_7
