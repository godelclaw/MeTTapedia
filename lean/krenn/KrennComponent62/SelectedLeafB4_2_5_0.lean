import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_2_5_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c530e3c26f7090c3d0aa08e54fa7457fdd4b41f3e26388b506646a501064501c"
def certificateSHA256 : String := "3f2bfbc84f0ea3cd4dbd6d5ecaa734f3ba783ef62d0117eb591300c947896d8a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 25 → Fin 670 := ![
  6,
  7,
  11,
  139,
  159,
  207,
  301,
  302,
  362,
  374,
  408,
  454,
  496,
  557,
  605,
  656,
  657,
  659,
  660,
  663,
  665,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(4, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(5, 1), (32, 1), (50, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (29, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (46, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (32, 1), (35, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (22, 1), (32, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (12, 1), (32, 1), (41, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (21, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (29, 1), (41, 1), (43, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (32, 1), (38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (35, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (32, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (22, 1), (32, 1), (50, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (22, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (29, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (22, 1), (32, 1), (38, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (17, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (58, 1)] }, { coefficient := 1, powers := [(38, 1), (55, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (36, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (46, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (46, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (36, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (39, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (43, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (38, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (8, 1), (32, 1), (33, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (32, 1), (33, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (16, 1), (22, 1), (32, 1), (44, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (22, 1), (32, 1), (38, 1), (50, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (21, 1), (22, 1), (44, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (22, 1), (29, 1), (43, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (22, 1), (32, 1), (38, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (21, 1), (22, 1), (38, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (22, 1), (29, 1), (38, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (22, 1), (32, 1), (38, 2), (53, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (35, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (43, 1)] }, { coefficient := -1, powers := [(14, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (32, 1), (41, 1), (45, 1), (50, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (32, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (32, 1), (45, 1), (48, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (21, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (29, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (32, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (41, 1), (45, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (21, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (29, 1), (41, 1), (43, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (29, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (32, 1), (38, 1), (41, 1), (45, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (21, 1), (45, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (29, 1), (43, 1), (45, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (32, 1), (38, 1), (45, 1), (48, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_2_5_0.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_2_5_0
