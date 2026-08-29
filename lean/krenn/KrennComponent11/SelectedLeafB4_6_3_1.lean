import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB4_6_3_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "89d34151a17935072553ab1caeb2cc9fdf3176b9bd2adbeca9beba5ffe63e5ca"
def certificateSHA256 : String := "cb6a8c1e77ba6d7f46dd8bf3872706d73201713930b4d4c5a9a821eda3fcd914"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 26 → Fin 675 := ![
  10,
  16,
  262,
  286,
  322,
  323,
  328,
  329,
  330,
  340,
  341,
  346,
  350,
  453,
  462,
  489,
  588,
  614,
  662,
  663,
  665,
  668,
  670,
  671,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(33, 1), (36, 1), (37, 1), (39, 1), (57, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (57, 1)] }, { coefficient := -1, powers := [(29, 1), (48, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1), (25, 1), (52, 2), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (52, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (36, 1), (39, 1), (46, 1), (52, 1), (57, 1), (65, 2)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1), (46, 1), (53, 1), (57, 1), (65, 2)] }],
  [{ coefficient := 1, powers := [(12, 1), (30, 1), (52, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (37, 1), (39, 1), (57, 1), (59, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (25, 1), (52, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (36, 1), (39, 1), (46, 1), (57, 1), (65, 2)] }],
  [{ coefficient := -1, powers := [(12, 1), (30, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (23, 1), (52, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1), (46, 1), (57, 1), (65, 2)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (18, 1), (36, 1), (39, 1), (57, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (36, 1), (39, 1), (57, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (36, 1), (39, 1), (46, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (37, 1), (39, 1), (57, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (37, 1), (39, 1), (54, 1), (57, 1), (59, 1), (65, 1), (66, 1)] }, { coefficient := 1, powers := [(39, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(49, 1), (54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (56, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (57, 2), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (30, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (29, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (23, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(12, 1), (18, 1), (36, 1), (39, 1), (46, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (12, 1), (36, 1), (39, 1), (57, 1), (59, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (36, 1), (39, 1), (41, 1), (57, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (18, 1), (36, 1), (39, 1), (46, 1), (57, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (25, 1), (44, 1), (52, 2), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (44, 1), (52, 1), (53, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (25, 1), (36, 1), (39, 1), (44, 1), (46, 1), (52, 1), (57, 1), (65, 2)] }, { coefficient := -1, powers := [(12, 1), (30, 1), (49, 1), (52, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1), (44, 1), (46, 1), (53, 1), (57, 1), (65, 2)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1), (57, 1), (61, 1), (65, 1)] }, { coefficient := 2, powers := [(17, 1), (23, 1), (41, 1), (54, 1), (57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (36, 1), (37, 1), (39, 1), (57, 1), (59, 1), (65, 1)] }]
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
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB4_6_3_1.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB4_6_3_1
