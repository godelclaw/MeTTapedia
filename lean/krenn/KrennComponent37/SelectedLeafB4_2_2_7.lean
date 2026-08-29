import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_2_2_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "5367863b29fa2a276bfbceb9d5868abfba92c9e5037912ee1781630e59910664"
def certificateSHA256 : String := "a22b4b7d0b51b3cad599162ffcb8ed927d032639845a21b154137551cedb19a9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 670 := ![
  9,
  15,
  27,
  28,
  180,
  181,
  296,
  312,
  316,
  364,
  433,
  447,
  450,
  454,
  478,
  516,
  529,
  580,
  657,
  660,
  663,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (47, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (30, 1), (49, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (66, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (55, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (20, 1), (30, 1), (51, 1), (65, 1), (66, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (26, 1), (41, 1), (51, 1), (66, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (29, 1), (55, 1), (66, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (29, 1), (51, 1), (66, 1)] }, { coefficient := -2, powers := [(19, 1), (26, 1), (33, 1), (37, 1), (41, 1), (66, 1)] }, { coefficient := 2, powers := [(19, 1), (28, 1), (55, 1), (66, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (51, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (25, 1), (29, 1), (55, 1), (67, 1)] }, { coefficient := -2, powers := [(19, 1), (26, 1), (29, 1), (51, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (30, 1), (48, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 1), (25, 1), (55, 1), (67, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (26, 1), (51, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (26, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (30, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (26, 1), (41, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (30, 1), (49, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (30, 1), (48, 1), (51, 1), (65, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (26, 1), (41, 1), (48, 1), (51, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (29, 1), (48, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (26, 1), (29, 1), (48, 1), (51, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (33, 1), (37, 1), (41, 1), (48, 1)] }, { coefficient := -2, powers := [(19, 1), (28, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 1), (25, 1), (41, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (25, 1), (46, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (26, 1), (41, 1), (51, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (26, 1), (46, 1), (51, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (29, 1), (48, 1), (55, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (29, 1), (48, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_2_2_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_2_2_7
