import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component25.SelectedLeafB5_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "72a90f71b78efe8d427c67d2154f258078e0f23cb7c3343485a206f63651afa9"
def certificateSHA256 : String := "e72132d89011e83749e7914da7bfa5d6a57dc2892bf4fee87ef90f0ccc64d71d"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 662 := ![
  1,
  14,
  17,
  21,
  24,
  142,
  162,
  163,
  168,
  173,
  175,
  178,
  196,
  238,
  300,
  306,
  310,
  312,
  317,
  388,
  406,
  430,
  435,
  450,
  475,
  478,
  497,
  578,
  580,
  655,
  656,
  658,
  660
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (45, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (48, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 65) := ![
  [{ coefficient := 4, powers := [(2, 1), (6, 1), (23, 1), (38, 1), (60, 2)] }, { coefficient := 4, powers := [(2, 1), (6, 1), (29, 1), (41, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (35, 1), (36, 1), (41, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (27, 1), (35, 1), (41, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (22, 1), (35, 1), (41, 1), (62, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (22, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(22, 1), (24, 1), (48, 1), (53, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (23, 1), (38, 1), (43, 1), (60, 1)] }, { coefficient := -2, powers := [(23, 1), (43, 1)] }, { coefficient := -1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(2, 2), (38, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (29, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (23, 1), (50, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (50, 1), (61, 1)] }],
  [{ coefficient := 4, powers := [(2, 1), (6, 1), (16, 1), (38, 1), (60, 2)] }, { coefficient := -2, powers := [(2, 1), (8, 1), (48, 1), (50, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (17, 1), (38, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (16, 1), (60, 1)] }, { coefficient := -1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 4, powers := [(2, 2), (6, 1), (38, 1), (60, 2), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(2, 2), (38, 1), (43, 1), (47, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (29, 1), (43, 1), (47, 1), (52, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (23, 1), (43, 1), (47, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (47, 1), (52, 1)] }],
  [{ coefficient := 4, powers := [(2, 1), (23, 1), (38, 1), (46, 1), (54, 1), (60, 1)] }, { coefficient := 2, powers := [(23, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 4, powers := [(2, 1), (23, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := 2, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := -4, powers := [(0, 1), (2, 1), (5, 1), (38, 1), (60, 2)] }, { coefficient := 4, powers := [(0, 1), (2, 1), (8, 1), (41, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (60, 1)] }, { coefficient := -4, powers := [(2, 1), (5, 1), (24, 1), (38, 1), (60, 2)] }, { coefficient := 4, powers := [(2, 1), (8, 1), (24, 1), (41, 1), (48, 1), (60, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (60, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (48, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (48, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (2, 2), (38, 1), (41, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (5, 1), (29, 1), (41, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (8, 1), (23, 1), (41, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (41, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 2), (38, 1), (41, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (23, 1), (54, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (32, 1), (38, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (8, 1), (23, 1), (41, 1), (60, 1)] }, { coefficient := -4, powers := [(2, 1), (12, 1), (23, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1)] }],
  [{ coefficient := -2, powers := [(2, 2), (38, 1), (43, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (29, 1), (43, 1), (60, 1), (61, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (23, 1), (43, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(24, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 4, powers := [(2, 1), (23, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (29, 1), (48, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (18, 1), (23, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(18, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (5, 1), (54, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (41, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (12, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 2, powers := [(2, 2), (38, 1), (47, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (29, 1), (47, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 1), (8, 1), (23, 1), (47, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (23, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 2, powers := [(2, 1), (8, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (17, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1), (41, 1), (62, 1)] }],
  [{ coefficient := -4, powers := [(2, 1), (6, 1), (38, 1), (60, 2)] }, { coefficient := -1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (16, 1), (35, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 4, powers := [(2, 1), (5, 1), (29, 1), (38, 1), (60, 2)] }, { coefficient := -4, powers := [(2, 1), (8, 1), (29, 1), (41, 1), (48, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(2, 2), (38, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (29, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(2, 1), (8, 1), (23, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (61, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -4, powers := [(2, 2), (6, 1), (38, 2), (59, 1), (60, 2)] }, { coefficient := -2, powers := [(2, 2), (38, 2), (60, 2)] }, { coefficient := 2, powers := [(2, 2), (38, 1), (43, 1), (47, 1), (54, 1), (60, 1)] }, { coefficient := -2, powers := [(2, 2), (38, 1), (48, 1), (54, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (29, 1), (38, 1), (60, 2)] }, { coefficient := -2, powers := [(2, 1), (5, 1), (29, 1), (43, 1), (47, 1), (54, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (5, 1), (29, 1), (48, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (23, 1), (38, 1), (60, 2)] }, { coefficient := -2, powers := [(2, 1), (8, 1), (23, 1), (43, 1), (47, 1), (54, 1), (60, 1)] }, { coefficient := 2, powers := [(2, 1), (8, 1), (23, 1), (48, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(2, 1), (43, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (41, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (2, 2), (38, 1), (41, 1), (57, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 2), (2, 1), (5, 1), (29, 1), (41, 1), (57, 1), (60, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 2), (2, 1), (8, 1), (23, 1), (41, 1), (57, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 2), (2, 1), (41, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(0, 1), (2, 2), (38, 1), (41, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (5, 1), (23, 1), (54, 1), (57, 1), (60, 1)] }, { coefficient := 4, powers := [(0, 1), (2, 1), (5, 1), (29, 1), (38, 1), (60, 2)] }, { coefficient := -2, powers := [(0, 1), (2, 1), (5, 1), (32, 1), (38, 1), (57, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (2, 1), (8, 1), (23, 1), (41, 1), (57, 1), (60, 1)] }, { coefficient := -4, powers := [(0, 1), (2, 1), (8, 1), (29, 1), (41, 1), (48, 1), (60, 1)] }, { coefficient := 4, powers := [(0, 1), (2, 1), (12, 1), (23, 1), (38, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (29, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (23, 1), (57, 1)] }, { coefficient := 4, powers := [(2, 1), (17, 1), (18, 1), (23, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := 4, powers := [(2, 1), (17, 1), (23, 1), (24, 1), (38, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (29, 1), (48, 1)] }, { coefficient := 2, powers := [(17, 1), (18, 1), (23, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (24, 1), (54, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 33,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component25.SelectedLeafB5_5.selectedHasNoCommonZero

end Krenn.Component25.SelectedLeafB5_5
