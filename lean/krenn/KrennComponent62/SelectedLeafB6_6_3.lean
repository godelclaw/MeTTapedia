import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB6_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4ed26b25c6b836decaf08fe77c4de43a108f3c05bbb90ca10cb85ef57689ca12"
def certificateSHA256 : String := "007127bac98af9b71faaae18bb119b379d6a50a8528a50df8238f300e5895e07"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 32 → Fin 667 := ![
  12,
  17,
  18,
  21,
  83,
  130,
  133,
  135,
  136,
  137,
  140,
  141,
  160,
  191,
  192,
  301,
  302,
  311,
  440,
  454,
  557,
  578,
  589,
  609,
  619,
  657,
  659,
  660,
  661,
  662,
  663,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(10, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(41, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (25, 1), (27, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (25, 1), (27, 1), (43, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (27, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (20, 1), (22, 1), (38, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (20, 1), (22, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(17, 1), (20, 1), (22, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (38, 1), (59, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (12, 1), (27, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (27, 1), (43, 1), (61, 1)] }, { coefficient := -1, powers := [(12, 1), (27, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (22, 1), (38, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (22, 1), (50, 1), (61, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (44, 1), (51, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (51, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (41, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(41, 1), (51, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(48, 1), (56, 1)] }, { coefficient := -1, powers := [(51, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(19, 1), (55, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (45, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (19, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (55, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (38, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (9, 1), (38, 1), (59, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (46, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := -1, powers := [(12, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (22, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (43, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (38, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (43, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (64, 1)] }, { coefficient := 1, powers := [(41, 1), (52, 1), (64, 1)] }, { coefficient := 1, powers := [(56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (12, 1), (27, 1), (38, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (27, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (22, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (22, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (39, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (43, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (44, 1), (52, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1), (39, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (43, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (39, 1), (41, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (39, 1), (44, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(39, 1), (41, 1), (52, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(39, 1), (55, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (27, 1), (38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (9, 1), (27, 1), (38, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (30, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (30, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (22, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (22, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (30, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (30, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (30, 1), (38, 1), (41, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (30, 1), (44, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (23, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (23, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (38, 1), (41, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (24, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (22, 1), (56, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB6_6_3.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB6_6_3
