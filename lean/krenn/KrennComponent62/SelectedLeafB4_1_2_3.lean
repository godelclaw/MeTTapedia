import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_1_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "eaf20e29aa8b758201af636dd9cedde55eae8b7ffc6d193be1d0beb9ffaec6fa"
def certificateSHA256 : String := "194f083f42a830eb5b6e2c3935136123a516a93e73f9d68938cd167c84c6cd33"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 670 := ![
  18,
  21,
  23,
  160,
  186,
  252,
  293,
  294,
  301,
  302,
  318,
  408,
  441,
  454,
  464,
  470,
  557,
  579,
  610,
  646,
  657,
  660,
  662,
  663,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(41, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(43, 1)] }, { coefficient := 1, powers := [(50, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (39, 1), (43, 1), (45, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (39, 1), (45, 1), (55, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (33, 1), (39, 1), (43, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (41, 1), (58, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (39, 1), (45, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(17, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (8, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (18, 1), (39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (8, 1), (33, 1), (39, 1), (45, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (8, 1), (33, 1), (39, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (18, 1), (33, 1), (39, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (19, 1), (33, 1), (39, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (39, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (33, 1), (39, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (59, 1), (64, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (39, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (51, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (27, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (53, 1)] }, { coefficient := -1, powers := [(27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (39, 1), (45, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (33, 1), (39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (27, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (33, 1), (39, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (39, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (8, 1), (27, 1), (33, 1), (39, 1), (45, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 2), (8, 1), (27, 1), (33, 1), (39, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 2), (8, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (18, 1), (27, 1), (33, 1), (39, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (18, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (19, 1), (27, 1), (33, 1), (39, 1), (51, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (27, 1), (33, 1), (39, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (27, 1), (33, 1), (39, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (38, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (8, 1), (33, 1), (39, 1), (43, 1), (45, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 2), (8, 1), (33, 1), (39, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (18, 1), (33, 1), (39, 1), (43, 1), (50, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (19, 1), (33, 1), (39, 1), (43, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (22, 1), (50, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (39, 1), (43, 1), (45, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (39, 1), (45, 1), (48, 1), (55, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (39, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (22, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (22, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (33, 1), (39, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (33, 1), (39, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (18, 1), (33, 1), (39, 1), (55, 1)] }, { coefficient := -1, powers := [(8, 1), (19, 1), (33, 1), (39, 1), (43, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (41, 1), (48, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1), (45, 1), (48, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_1_2_3.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_1_2_3
