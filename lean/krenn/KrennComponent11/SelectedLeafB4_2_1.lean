import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB4_2_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "2d785b55961302ff39d11b1447503705c88cee5cefe612435239a92ad389297b"
def certificateSHA256 : String := "941a6e0b548c996ddb349c4d7ab2a5eac84da5e549955628e804989b4ff62db3"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 672 := ![
  6,
  12,
  20,
  160,
  179,
  186,
  262,
  322,
  328,
  329,
  330,
  341,
  346,
  446,
  448,
  453,
  462,
  589,
  614,
  616,
  650,
  662,
  665,
  668,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(0, 2), (33, 1), (38, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 2), (36, 1), (38, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (36, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (37, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (33, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (23, 1), (38, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (23, 1), (46, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (41, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (46, 1), (54, 1)] }, { coefficient := -2, powers := [(23, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (23, 1), (46, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (23, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (30, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (36, 1), (38, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (30, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (36, 1), (39, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (39, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (41, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (38, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (38, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(3, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (30, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (30, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (41, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (17, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (41, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (23, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (23, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (41, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (44, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(25, 1), (44, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(0, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 2), (38, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (38, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (39, 1), (46, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (46, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (8, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (17, 1), (30, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (46, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (36, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (30, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (30, 1), (41, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := -1, powers := [(17, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (12, 1), (18, 1), (30, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (12, 1), (18, 1), (36, 1), (38, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (12, 1), (18, 1), (30, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (12, 1), (18, 1), (36, 1), (39, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (18, 1), (30, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (18, 1), (36, 1), (39, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (25, 1), (44, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (18, 1), (30, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (18, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (25, 1), (33, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (44, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB4_2_1.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB4_2_1
