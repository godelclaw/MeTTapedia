import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "bdde57c31435cc996566878264d87d8ec3828b3138666d114aea423569df0935"
def certificateSHA256 : String := "50d5581d499e5791fdead5f9a1057d5f438658af082bb05e2537434987f899a6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 35 → Fin 608 := ![
  0,
  2,
  4,
  16,
  18,
  19,
  20,
  32,
  33,
  39,
  42,
  213,
  311,
  312,
  323,
  324,
  325,
  335,
  400,
  415,
  434,
  441,
  541,
  558,
  567,
  568,
  596,
  599,
  601,
  602,
  603,
  604,
  605,
  606,
  607
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 35 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(1, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (40, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (47, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (55, 1)] }, { coefficient := 1, powers := [(17, 1), (29, 1), (45, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(9, 1), (19, 1), (53, 1)] }, { coefficient := 1, powers := [(9, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (19, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 35 → SparsePoly (Fin 63) := ![
  [{ coefficient := 4, powers := [(0, 2), (13, 1), (23, 1), (48, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (19, 1), (23, 1), (48, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (23, 1), (24, 1), (48, 1), (50, 1), (55, 1), (60, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (23, 1), (30, 1), (36, 1), (50, 1), (55, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (29, 1), (54, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (35, 1), (54, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (23, 1), (54, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (9, 1), (23, 1), (24, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (23, 1), (24, 1), (48, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (25, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (3, 1), (23, 1), (30, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(0, 1), (9, 1), (19, 1), (23, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (19, 1), (23, 1), (48, 1), (50, 1), (55, 1), (62, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (23, 1), (30, 1), (36, 1), (50, 1), (55, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (3, 1), (13, 1), (23, 1), (50, 1), (55, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (41, 1), (50, 2), (54, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (29, 1), (41, 1), (50, 1), (54, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (46, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (41, 1), (54, 1), (55, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (41, 1), (51, 1), (54, 1), (61, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (23, 1), (51, 1), (54, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (19, 1), (23, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (29, 1), (41, 1), (50, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (29, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (41, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 2), (13, 1), (23, 1), (50, 1), (55, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (9, 1), (23, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(0, 1), (23, 1), (48, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (29, 1), (41, 1), (50, 1), (54, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (41, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (23, 1), (48, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (13, 1), (23, 1), (42, 1), (50, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (41, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (13, 1), (23, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(0, 2), (13, 1), (23, 1), (36, 1), (50, 1), (55, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 2), (13, 1), (23, 1), (42, 1), (48, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (19, 1), (23, 1), (42, 1), (48, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (23, 1), (24, 1), (42, 1), (48, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (23, 1), (30, 1), (36, 1), (42, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (29, 1), (47, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (23, 1), (52, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (54, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (41, 1), (54, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (45, 1), (51, 1), (54, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(0, 2), (1, 1), (13, 1), (23, 1), (50, 1), (53, 1), (55, 1), (60, 1)] }, { coefficient := -2, powers := [(0, 2), (13, 1), (23, 1), (50, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (6, 1), (13, 1), (23, 1), (33, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (14, 1), (23, 1), (24, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (23, 1), (24, 1), (42, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (8, 1), (35, 1), (41, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (3, 1), (13, 1), (23, 1), (24, 1), (50, 1), (55, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (13, 1), (14, 1), (19, 1), (23, 1), (48, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(0, 1), (13, 1), (14, 1), (23, 1), (30, 1), (36, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (13, 1), (23, 1), (43, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (28, 1), (46, 1), (55, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (28, 1), (41, 1), (54, 1), (55, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (29, 1), (41, 1), (50, 2), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (24, 1), (29, 1), (41, 1), (50, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (28, 1), (41, 1), (51, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(0, 1), (59, 1)] }]
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 35,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB6_3.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB6_3
