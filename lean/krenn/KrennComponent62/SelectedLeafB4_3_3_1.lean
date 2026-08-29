import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_3_3_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a66cdb43a06fa7ef0c0a2477eb79c5a6ba2837998f6d180ea7f4a4edf27b9c85"
def certificateSHA256 : String := "6fcd0b35617ef405bf79cd2150046ad5b43baaac77183bc30c4851f9ecc63317"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 36 → Fin 670 := ![
  18,
  21,
  135,
  147,
  153,
  158,
  160,
  252,
  293,
  294,
  301,
  302,
  313,
  318,
  390,
  408,
  435,
  441,
  444,
  454,
  465,
  473,
  475,
  515,
  557,
  578,
  589,
  606,
  609,
  657,
  658,
  660,
  665,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 36 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1)] }, { coefficient := 1, powers := [(41, 1), (50, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(22, 1), (41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(41, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 36 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(6, 1), (12, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (48, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (22, 1), (44, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (41, 1), (58, 1), (65, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (18, 1), (51, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (51, 1), (56, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (44, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (22, 1), (44, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (12, 1), (18, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (56, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (27, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (43, 2), (50, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (43, 2), (52, 1), (64, 1)] }, { coefficient := 2, powers := [(6, 1), (12, 1), (22, 1), (24, 1), (50, 2), (56, 1), (58, 1), (64, 1)] }, { coefficient := -2, powers := [(6, 1), (12, 1), (22, 1), (50, 1), (52, 1), (56, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (24, 1), (43, 1), (50, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (43, 1), (52, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (50, 1), (64, 1)] }, { coefficient := -1, powers := [(43, 1), (52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (8, 1), (30, 1), (50, 1), (58, 1)] }, { coefficient := -2, powers := [(6, 1), (12, 1), (27, 1), (50, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (53, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (46, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (43, 2), (64, 1)] }, { coefficient := -2, powers := [(6, 1), (12, 1), (22, 1), (24, 1), (50, 1), (56, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (43, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (8, 1), (30, 1), (58, 1)] }, { coefficient := 2, powers := [(6, 1), (12, 1), (27, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (22, 1), (56, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (22, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (27, 1), (39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (50, 1), (64, 1)] }, { coefficient := -1, powers := [(52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (27, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (22, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (17, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 2), (64, 1)] }, { coefficient := 2, powers := [(6, 1), (12, 1), (22, 1), (50, 1), (56, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (43, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (12, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (60, 1)] }, { coefficient := -1, powers := [(34, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (56, 1), (58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(60, 1)] }],
  [{ coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (43, 2)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (58, 2)] }, { coefficient := -1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1)] }, { coefficient := -1, powers := [(34, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(6, 1), (18, 1), (45, 1), (51, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (39, 1), (55, 1), (56, 1), (58, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (46, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (6, 1), (30, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (12, 1), (22, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (43, 2)] }, { coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := -2, powers := [(6, 1), (12, 1), (18, 1), (22, 1), (50, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (43, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (43, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (38, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (43, 2), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (41, 1), (43, 2), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (43, 2), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (6, 1), (58, 2), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (30, 1), (46, 1), (50, 1), (58, 1)] }, { coefficient := -2, powers := [(6, 1), (12, 1), (22, 1), (24, 1), (41, 1), (50, 2), (56, 1), (58, 1), (64, 1)] }, { coefficient := 2, powers := [(6, 1), (12, 1), (22, 1), (41, 1), (50, 1), (52, 1), (56, 1), (58, 1), (64, 1)] }, { coefficient := 2, powers := [(6, 1), (12, 1), (27, 1), (46, 1), (50, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (22, 1), (44, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (27, 1), (39, 1), (44, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (16, 1), (27, 1), (46, 1), (51, 1), (58, 1)] }, { coefficient := -2, powers := [(6, 1), (17, 1), (22, 1), (38, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (27, 1), (38, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (43, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(6, 1), (24, 1), (41, 1), (43, 1), (50, 1), (58, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (41, 1), (43, 1), (52, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(6, 1), (58, 1), (60, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (44, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (41, 1), (50, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (41, 1), (43, 1), (50, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(38, 1), (41, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(41, 1), (43, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(60, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (22, 1), (44, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (41, 1), (48, 1), (58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 36,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_3_3_1.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_3_3_1
