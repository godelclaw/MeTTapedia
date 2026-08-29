import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_7_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "51a6d5db66253a00b57508dc557fb92966a9235e8721b69900891ac50ae7bcc6"
def certificateSHA256 : String := "646e4aa5dda38e2d7065b0a5448714cb62751e7fe13ff90c5e5ec9be771617f9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 670 := ![
  9,
  15,
  26,
  27,
  28,
  180,
  181,
  296,
  297,
  311,
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
  646,
  650,
  657,
  658,
  663,
  665,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
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
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(26, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1), (69, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 71) := ![
  [{ coefficient := -1, powers := [(24, 1), (26, 1), (47, 1), (69, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1), (58, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(25, 1), (30, 1), (49, 1), (68, 1), (69, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (69, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (55, 1), (69, 1)] }, { coefficient := -1, powers := [(24, 1), (53, 1), (58, 1), (66, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (55, 1), (62, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (51, 1), (58, 1), (62, 1), (69, 1)] }, { coefficient := -1, powers := [(2, 1), (53, 1), (58, 1), (66, 1), (69, 1)] }, { coefficient := -1, powers := [(19, 1), (20, 1), (30, 1), (51, 1), (68, 1), (69, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (26, 1), (41, 1), (51, 1), (69, 1)] }, { coefficient := -2, powers := [(19, 1), (25, 1), (29, 1), (55, 1), (69, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (29, 1), (51, 1), (69, 1)] }, { coefficient := -2, powers := [(19, 1), (26, 1), (33, 1), (37, 1), (41, 1), (69, 1)] }, { coefficient := 2, powers := [(19, 1), (28, 1), (55, 1), (69, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (51, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (55, 1), (62, 1), (69, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (25, 1), (29, 1), (55, 1), (70, 1)] }, { coefficient := -2, powers := [(19, 1), (26, 1), (29, 1), (51, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (48, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (58, 1), (66, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 1), (25, 1), (55, 1), (70, 1)] }, { coefficient := 2, powers := [(19, 1), (24, 1), (26, 1), (51, 1), (70, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (26, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (30, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (68, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (26, 1), (41, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (2, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (25, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (26, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (57, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1), (58, 1), (66, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (28, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (20, 1), (48, 1), (51, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(2, 1), (20, 1), (49, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (21, 1), (44, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (53, 1), (58, 1), (66, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (26, 1), (47, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (52, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (30, 1), (49, 1), (68, 1)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (53, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (30, 1), (48, 1), (51, 1), (68, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (26, 1), (41, 1), (48, 1), (51, 1)] }, { coefficient := 2, powers := [(19, 1), (25, 1), (29, 1), (48, 1), (55, 1)] }, { coefficient := -2, powers := [(19, 1), (26, 1), (29, 1), (48, 1), (51, 1)] }, { coefficient := 2, powers := [(19, 1), (26, 1), (33, 1), (37, 1), (41, 1), (48, 1)] }, { coefficient := -2, powers := [(19, 1), (28, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (48, 1), (51, 1)] }],
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_2_7_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_7_7
