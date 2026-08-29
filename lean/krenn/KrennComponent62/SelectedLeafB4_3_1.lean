import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_3_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e5eaecfa00251d4a46fb1c617be439f61288bb2ca868625dcb4547a940ae4008"
def certificateSHA256 : String := "830429500d2cd5e89c060404463f8d5667b64a87de3659ea596f22988f60a823"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 43 → Fin 667 := ![
  7,
  16,
  18,
  21,
  22,
  137,
  147,
  149,
  153,
  158,
  223,
  245,
  252,
  293,
  294,
  295,
  296,
  301,
  302,
  309,
  311,
  390,
  408,
  437,
  441,
  444,
  454,
  476,
  483,
  557,
  588,
  602,
  604,
  605,
  610,
  656,
  657,
  658,
  659,
  660,
  662,
  663,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 43 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(7, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (43, 1)] }, { coefficient := 1, powers := [(12, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (38, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }, { coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(41, 1), (53, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (41, 1)] }, { coefficient := 1, powers := [(46, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (43, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (55, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (38, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }, { coefficient := 1, powers := [(29, 1), (35, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (35, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (26, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (29, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (29, 1), (43, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (43, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (35, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (50, 1)] }, { coefficient := 1, powers := [(14, 1), (26, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (29, 1), (35, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (22, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 43 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(5, 1), (21, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (50, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (19, 1), (21, 1), (30, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (19, 1), (25, 1), (30, 1), (50, 2), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (26, 1), (30, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (26, 1), (30, 1), (43, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (19, 1), (26, 1), (30, 1), (50, 1), (56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (10, 1), (32, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (32, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (44, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (41, 1), (53, 1), (60, 1)] }, { coefficient := 1, powers := [(22, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (41, 1), (60, 1)] }, { coefficient := -2, powers := [(27, 1), (41, 1), (45, 1), (48, 1), (60, 1)] }, { coefficient := -2, powers := [(27, 1), (41, 1), (45, 1), (51, 1)] }, { coefficient := 3, powers := [(27, 1), (46, 1), (48, 1), (60, 1)] }, { coefficient := 2, powers := [(27, 1), (46, 1), (51, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := -2, powers := [(27, 1), (41, 1), (45, 1)] }, { coefficient := 2, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (21, 1), (30, 1), (50, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (30, 1), (50, 2), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (30, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (30, 1), (43, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(5, 1), (26, 1), (30, 1), (50, 1), (56, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (53, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (39, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (27, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(16, 1), (27, 1), (41, 1), (45, 1), (60, 1)] }, { coefficient := -3, powers := [(16, 1), (27, 1), (46, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (22, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (23, 1), (56, 1)] }, { coefficient := 2, powers := [(23, 1), (27, 1), (41, 1), (45, 1)] }, { coefficient := -2, powers := [(23, 1), (27, 1), (46, 1)] }],
  [{ coefficient := 2, powers := [(22, 1), (23, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (56, 1)] }, { coefficient := 2, powers := [(27, 1), (41, 1), (45, 1)] }, { coefficient := -2, powers := [(27, 1), (46, 1)] }],
  [{ coefficient := -2, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (50, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (25, 1), (30, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (26, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (30, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (30, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1), (41, 1)] }, { coefficient := -2, powers := [(16, 1), (27, 1), (41, 1), (45, 1), (48, 1)] }, { coefficient := 3, powers := [(16, 1), (27, 1), (46, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (30, 1), (35, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (38, 1), (55, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [(38, 1), (39, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (14, 1), (21, 1), (30, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (25, 1), (30, 1), (50, 2), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (26, 1), (30, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (26, 1), (30, 1), (43, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (14, 1), (26, 1), (30, 1), (50, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (17, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (29, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (21, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (10, 1), (25, 1), (30, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (10, 1), (26, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (14, 1), (21, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (22, 1), (56, 1)] }, { coefficient := -2, powers := [(12, 1), (18, 1), (27, 1), (41, 1), (45, 1)] }, { coefficient := 2, powers := [(12, 1), (18, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (22, 1), (23, 1), (56, 1)] }, { coefficient := -2, powers := [(12, 1), (23, 1), (27, 1), (41, 1), (45, 1)] }, { coefficient := 2, powers := [(12, 1), (23, 1), (27, 1), (46, 1)] }, { coefficient := -2, powers := [(17, 1), (18, 1), (27, 1), (45, 1), (48, 1)] }, { coefficient := 2, powers := [(17, 1), (19, 1), (27, 1), (48, 1)] }, { coefficient := 2, powers := [(17, 1), (22, 1), (23, 1), (53, 1)] }]
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
    ¬ ∀ index : Fin 43,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_3_1.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_3_1
