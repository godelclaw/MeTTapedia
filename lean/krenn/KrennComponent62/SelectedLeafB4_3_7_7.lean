import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_3_7_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "580e03d28f35ec4b240388dc975e48f26527c769373803c4245a6109e8346117"
def certificateSHA256 : String := "14963b671195dc0bb5461b988f913a66bab4c34dd1fa911d0dccba5b849fa39a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 27 → Fin 670 := ![
  7,
  8,
  16,
  18,
  137,
  160,
  245,
  252,
  294,
  301,
  302,
  374,
  441,
  496,
  557,
  585,
  602,
  604,
  605,
  656,
  657,
  659,
  660,
  663,
  664,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(7, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] }, { coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (54, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (26, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (43, 1), (46, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(17, 1), (26, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (36, 1), (43, 1)] }, { coefficient := -1, powers := [(17, 1), (32, 1), (36, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (54, 1), (55, 1), (63, 1), (68, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1), (55, 1), (63, 1), (68, 1)] }, { coefficient := -1, powers := [(26, 1), (55, 1), (68, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (21, 1), (23, 1), (50, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (25, 1), (50, 1), (62, 1), (66, 1)] }, { coefficient := 1, powers := [(19, 1), (26, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (35, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (12, 1), (21, 1), (52, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (26, 1), (52, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (29, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (32, 1), (43, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (21, 1), (27, 1), (46, 1), (51, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (26, 1), (27, 1), (46, 1), (51, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (27, 1), (29, 1), (43, 1), (46, 1), (51, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (27, 1), (32, 1), (43, 1), (46, 1), (51, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (21, 1), (27, 1), (41, 1), (51, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (26, 1), (27, 1), (41, 1), (51, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (27, 1), (29, 1), (41, 1), (43, 1), (51, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (27, 1), (32, 1), (41, 1), (43, 1), (51, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (68, 1)] }, { coefficient := -1, powers := [(14, 1), (26, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (23, 1), (50, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (50, 1), (62, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(32, 1), (35, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (27, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (27, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (29, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (32, 1), (43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (16, 1), (21, 1), (27, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (26, 1), (27, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (27, 1), (29, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (27, 1), (32, 1), (43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (43, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (46, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (46, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (43, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (43, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (21, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (43, 1)] }, { coefficient := -1, powers := [(8, 1), (32, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (27, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (27, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (27, 1), (29, 1), (43, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (32, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (50, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (29, 1), (43, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (32, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (43, 1), (50, 1), (66, 1)] }, { coefficient := 1, powers := [(35, 1), (58, 1)] }, { coefficient := -1, powers := [(38, 1), (54, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(38, 1), (55, 1)] }, { coefficient := -1, powers := [(42, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (21, 1), (27, 1), (46, 1), (51, 1), (52, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (26, 1), (27, 1), (46, 1), (51, 1), (52, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (27, 1), (29, 1), (43, 1), (46, 1), (51, 1), (52, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (27, 1), (32, 1), (43, 1), (46, 1), (51, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (21, 1), (27, 1), (41, 1), (51, 1), (52, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (26, 1), (27, 1), (41, 1), (51, 1), (52, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (19, 1), (27, 1), (29, 1), (41, 1), (43, 1), (51, 1), (52, 1), (68, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (27, 1), (32, 1), (41, 1), (43, 1), (51, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (46, 1), (53, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (36, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (39, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (46, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (36, 1), (43, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (39, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1), (46, 1), (53, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (36, 1), (43, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (39, 1), (43, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (43, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (21, 1), (23, 1), (50, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (55, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (50, 1), (66, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (29, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (16, 1), (21, 1), (27, 1), (46, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (16, 1), (26, 1), (27, 1), (46, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (16, 1), (27, 1), (29, 1), (43, 1), (46, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (16, 1), (27, 1), (32, 1), (43, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (19, 1), (21, 1), (27, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (19, 1), (26, 1), (27, 1), (41, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (19, 1), (27, 1), (29, 1), (41, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (19, 1), (27, 1), (32, 1), (41, 1), (43, 1), (51, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (54, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (42, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (55, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (43, 1)] }]
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
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_3_7_7.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_3_7_7
