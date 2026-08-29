import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB6_6_5_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d49fd5683d65633486664a2799366c15c5328fecf27f97f393d4174dfa683302"
def certificateSHA256 : String := "dc3c949db322e8a1e0350caa6b6636e3cc844f77d3fd28c4ea50f1668f6e1596"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 675 := ![
  6,
  8,
  16,
  28,
  29,
  183,
  262,
  286,
  328,
  329,
  341,
  453,
  500,
  507,
  557,
  611,
  661,
  662,
  665,
  668,
  670,
  672,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(5, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(30, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(1, 1), (33, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (33, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (41, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (23, 1), (25, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (25, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (23, 1), (25, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (23, 1), (25, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (25, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (25, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (16, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (11, 1), (35, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (12, 1), (38, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (35, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (44, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (21, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (35, 1), (41, 1), (44, 1)] }, { coefficient := -1, powers := [(11, 1), (12, 1), (35, 1), (38, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (23, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (35, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (23, 1), (46, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (23, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (23, 1), (35, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (23, 1), (35, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(1, 1), (23, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (35, 1), (52, 1), (54, 1)] }, { coefficient := 2, powers := [(7, 1), (20, 1), (23, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (21, 1), (23, 1), (54, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (23, 1), (35, 1), (41, 1), (54, 1)] }, { coefficient := -2, powers := [(11, 1), (23, 1), (35, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (54, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (17, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (35, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (20, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (17, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (35, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (23, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (23, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (12, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (35, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (12, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(1, 1), (38, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := -1, powers := [(11, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(1, 1), (38, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (39, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (39, 1), (46, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (46, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (21, 1), (39, 1), (59, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (49, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (39, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (35, 1), (41, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1), (39, 1), (60, 1)] }, { coefficient := -1, powers := [(11, 1), (35, 1), (38, 1), (49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (2, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (8, 1), (36, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (4, 1), (35, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (7, 1), (20, 1), (46, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (21, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (7, 1), (35, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (11, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (8, 1), (35, 1), (36, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (8, 1), (20, 1), (36, 1), (46, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (21, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (35, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (35, 1), (36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (12, 1), (18, 1), (23, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (18, 1), (23, 1), (35, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (18, 1), (20, 1), (23, 1), (46, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (18, 1), (21, 1), (23, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (18, 1), (23, 1), (35, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (12, 1), (18, 1), (23, 1), (35, 1), (38, 1), (57, 1)] }, { coefficient := -1, powers := [(11, 1), (20, 1), (46, 1)] }, { coefficient := 1, powers := [(11, 1), (21, 1)] }],
  [{ coefficient := 2, powers := [(1, 1), (17, 1), (23, 1), (38, 1), (41, 1), (54, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (17, 1), (23, 1), (35, 1), (41, 1), (52, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (46, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (21, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (32, 1), (38, 1), (59, 1)] }, { coefficient := -2, powers := [(7, 1), (17, 1), (20, 1), (23, 1), (41, 1), (46, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(7, 1), (17, 1), (21, 1), (23, 1), (41, 1), (54, 1), (59, 1)] }, { coefficient := 2, powers := [(7, 1), (17, 1), (23, 1), (35, 1), (41, 2), (54, 1)] }, { coefficient := 2, powers := [(11, 1), (17, 1), (23, 1), (35, 1), (38, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(11, 1), (20, 1), (46, 2), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (21, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (38, 1), (46, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1), (41, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (21, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (38, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (38, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(1, 1), (12, 1), (38, 1), (44, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (12, 1), (38, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (12, 1), (35, 1), (44, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(4, 1), (12, 1), (35, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(5, 1), (7, 1), (20, 1), (46, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (21, 1), (59, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (35, 1), (41, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (35, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (20, 1), (44, 1), (46, 1), (48, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (20, 1), (46, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (21, 1), (44, 1), (48, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (21, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (12, 1), (35, 1), (41, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (12, 1), (35, 1), (41, 1), (49, 1)] }, { coefficient := 1, powers := [(11, 1), (12, 1), (35, 1), (38, 1), (44, 1), (48, 1)] }, { coefficient := -1, powers := [(11, 1), (12, 1), (35, 1), (38, 1), (49, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB6_6_5_0.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB6_6_5_0
