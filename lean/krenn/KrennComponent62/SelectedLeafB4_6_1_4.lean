import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_6_1_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0a9d89ff18eeae5abb6c12358d8bfc1079d71d895d2bfb81c8d7c39a224e6cd6"
def certificateSHA256 : String := "da2a90069db88c7e9b32db075a43c011ae2452d18e9383aadd80aba1b15e0413"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 33 → Fin 670 := ![
  7,
  11,
  14,
  18,
  22,
  23,
  135,
  139,
  191,
  207,
  299,
  301,
  302,
  362,
  374,
  454,
  496,
  557,
  602,
  604,
  605,
  619,
  656,
  657,
  659,
  660,
  661,
  663,
  665,
  666,
  667,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 33 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(7, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (45, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 33 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(5, 1), (29, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(8, 1), (21, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (29, 1), (43, 1), (46, 1)] }, { coefficient := 2, powers := [(8, 1), (32, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (36, 1), (43, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (24, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (35, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (38, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (21, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := -2, powers := [(4, 1), (12, 1), (32, 1), (50, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (29, 1), (43, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (32, 1), (38, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (32, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (14, 1), (32, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (14, 1), (32, 1), (35, 1), (52, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (21, 1), (22, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (32, 1), (38, 1)] }, { coefficient := 2, powers := [(8, 1), (22, 1), (32, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (14, 1), (32, 1), (35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (61, 1), (64, 1)] }, { coefficient := -1, powers := [(50, 1), (61, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (29, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (21, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := 2, powers := [(4, 1), (32, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := -1, powers := [(14, 1), (32, 1), (35, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (38, 1)] }, { coefficient := 2, powers := [(5, 1), (32, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (43, 1)] }, { coefficient := -2, powers := [(8, 1), (32, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (17, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (32, 1), (38, 1)] }, { coefficient := 2, powers := [(4, 1), (17, 1), (32, 1), (50, 1)] }, { coefficient := -1, powers := [(14, 1), (17, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (38, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (12, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (32, 1), (38, 1)] }, { coefficient := 2, powers := [(4, 1), (12, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(12, 1), (14, 1), (32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(38, 1)] }, { coefficient := -1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (38, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (50, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (14, 1), (32, 1), (35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (21, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (38, 1)] }, { coefficient := -2, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (58, 1)] }, { coefficient := 1, powers := [(38, 1), (43, 1)] }, { coefficient := 1, powers := [(38, 1), (47, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (55, 1)] }, { coefficient := 2, powers := [(43, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1), (61, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (21, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := 2, powers := [(4, 1), (32, 1), (36, 1), (50, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := 2, powers := [(4, 1), (32, 1), (39, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (32, 1), (35, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (36, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (39, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (43, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (38, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(14, 1), (32, 1), (35, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (32, 1), (35, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (25, 1), (38, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (50, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (8, 1), (21, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (32, 1), (33, 1), (38, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (32, 1), (33, 1), (50, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (21, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (32, 1), (33, 1), (38, 1)] }, { coefficient := 2, powers := [(7, 1), (8, 1), (32, 1), (33, 1), (50, 1)] }, { coefficient := -1, powers := [(8, 1), (14, 1), (32, 1), (33, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (29, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (25, 1), (38, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (25, 1), (50, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (38, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (50, 1)] }, { coefficient := -1, powers := [(14, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (21, 1), (43, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (25, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (50, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (50, 2)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (43, 1)] }, { coefficient := -1, powers := [(14, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (12, 1), (21, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := -2, powers := [(4, 1), (12, 1), (32, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (21, 1), (45, 1), (48, 1), (58, 1)] }, { coefficient := -1, powers := [(4, 1), (17, 1), (32, 1), (38, 1), (45, 1), (48, 1)] }, { coefficient := -2, powers := [(4, 1), (17, 1), (32, 1), (45, 1), (48, 1), (50, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (14, 1), (32, 1), (35, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (29, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (32, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (32, 1), (35, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (14, 1), (16, 1), (32, 1), (35, 1), (45, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (29, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (29, 1), (39, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (32, 1), (38, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (14, 1), (32, 1), (35, 1), (46, 1)] }, { coefficient := 1, powers := [(14, 1), (17, 1), (32, 1), (35, 1), (45, 1), (48, 1)] }]
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

#print axioms Krenn.Component62.SelectedLeafB4_6_1_4.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_6_1_4
