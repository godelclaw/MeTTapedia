import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB6_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "03b6b180c3e8e4629dc14335156986c735d2dafe4f9e14fe3f79720350453f96"
def certificateSHA256 : String := "cbfaaed3b196a99eac35e93999db22dc5b166d8a6d812979c53a6b612474f51a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 672 := ![
  6,
  12,
  19,
  20,
  160,
  161,
  179,
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
  664,
  665,
  668,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1), (52, 1)] }],
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
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 2), (33, 1), (38, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 2), (36, 1), (38, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (3, 1), (36, 1), (46, 1), (54, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (37, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (33, 1), (47, 1)] }, { coefficient := -1, powers := [(3, 1), (33, 1), (57, 1)] }, { coefficient := -2, powers := [(3, 1), (36, 1), (54, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (33, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (23, 1), (38, 1), (47, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (23, 1), (46, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (23, 1), (41, 1), (47, 1)] }, { coefficient := 1, powers := [(3, 1), (23, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(23, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (20, 1), (23, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (52, 1), (54, 1)] }],
  [{ coefficient := 2, powers := [(17, 1), (23, 1), (52, 1)] }],
  [{ coefficient := -2, powers := [(17, 1), (23, 1), (62, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (23, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (30, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (36, 1), (38, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (30, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (36, 1), (39, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (30, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(0, 1), (36, 1), (39, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (30, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (41, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (38, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (38, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(3, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (30, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (30, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (30, 1), (41, 1)] }, { coefficient := -1, powers := [(3, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (17, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (41, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (33, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (23, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (23, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (41, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(52, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (44, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(25, 1), (44, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := -1, powers := [(0, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(17, 1), (23, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (38, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 2), (38, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (39, 1), (46, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (46, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (41, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(3, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(39, 1), (60, 1)] }, { coefficient := -1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (8, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (17, 1), (30, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (2, 1), (3, 1), (46, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (2, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (36, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (30, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (30, 1), (41, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (30, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := -1, powers := [(17, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (12, 1), (18, 1), (30, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 2), (12, 1), (18, 1), (36, 1), (38, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 2), (41, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (12, 1), (18, 1), (30, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (12, 1), (18, 1), (36, 1), (39, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (18, 1), (30, 1), (41, 1), (49, 1)] }, { coefficient := -1, powers := [(0, 1), (12, 1), (18, 1), (36, 1), (39, 1), (41, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (25, 1), (44, 1), (46, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (46, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := -1, powers := [(3, 1), (12, 1), (18, 1), (30, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (12, 1), (18, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (18, 1), (25, 1), (33, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (30, 1), (49, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (44, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1)] }],
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB6_6_1.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB6_6_1
