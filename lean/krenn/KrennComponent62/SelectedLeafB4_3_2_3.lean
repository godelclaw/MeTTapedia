import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_3_2_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "08802b24cf3475d82b94f4357e5bd32648575b7ae5b0c91f38defa76c6a24517"
def certificateSHA256 : String := "c57248455d494f6e832d7196f2fd39f4290a356bae94546c5ddf2ec3ff4172c9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 670 := ![
  18,
  21,
  147,
  153,
  191,
  252,
  294,
  301,
  302,
  316,
  318,
  408,
  441,
  444,
  454,
  557,
  578,
  657,
  660,
  666,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (50, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(8, 1), (30, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (27, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (24, 1), (33, 1), (43, 1), (65, 2)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (45, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (45, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (27, 1), (44, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (27, 1), (44, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(27, 2), (51, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (27, 1), (30, 1), (50, 1), (65, 1)] }, { coefficient := 2, powers := [(12, 1), (27, 2), (50, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (46, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (33, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (27, 1), (30, 1), (65, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 2), (65, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (27, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(27, 2), (39, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(27, 2), (65, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (27, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (30, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (33, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (36, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(27, 1), (46, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (30, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (30, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (27, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (33, 1), (38, 1), (53, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (33, 1), (43, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (27, 1), (30, 1), (46, 1), (50, 1), (65, 1)] }, { coefficient := -2, powers := [(12, 1), (27, 2), (46, 1), (50, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (27, 1), (44, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 2), (39, 1), (44, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 2), (46, 1), (51, 1), (65, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (27, 1), (38, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 2), (38, 1), (39, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (22, 1), (24, 1), (33, 1), (43, 1), (48, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_3_2_3.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_3_2_3
