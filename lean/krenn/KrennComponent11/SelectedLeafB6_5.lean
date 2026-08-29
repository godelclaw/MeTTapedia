import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB6_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "363d33ba2c5733eb101d10bce808361366a07d9c7fe3092b9fa3037c882404c8"
def certificateSHA256 : String := "2a80d463d2815ebb096c959029addbbe73aff33a2a583a1c3dd9bfe3bcfd0c5a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 30 → Fin 669 := ![
  7,
  11,
  16,
  20,
  25,
  30,
  162,
  166,
  175,
  184,
  283,
  286,
  323,
  328,
  329,
  330,
  341,
  350,
  446,
  453,
  517,
  588,
  606,
  616,
  662,
  663,
  665,
  666,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 30 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(12, 1), (25, 1), (47, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (25, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (25, 1), (51, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 30 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (39, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (39, 1), (42, 1), (46, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := 2, powers := [(30, 1), (42, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (25, 1), (33, 1), (47, 1), (61, 1), (64, 1)] }, { coefficient := 2, powers := [(5, 1), (33, 1), (47, 1), (53, 1), (64, 1)] }, { coefficient := -2, powers := [(12, 1), (30, 1), (49, 1), (52, 1), (64, 1)] }, { coefficient := -1, powers := [(12, 1), (33, 1), (37, 1), (39, 1), (49, 1), (52, 1), (59, 1), (64, 2)] }],
  [{ coefficient := 2, powers := [(5, 1), (25, 1), (33, 1), (61, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (39, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (42, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (39, 1), (49, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (39, 1), (42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (36, 1), (39, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(30, 1), (42, 1), (63, 1)] }],
  [{ coefficient := -4, powers := [(23, 1), (54, 1)] }, { coefficient := -2, powers := [(30, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (37, 1), (39, 1), (52, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(54, 1)] }],
  [{ coefficient := 2, powers := [(49, 1)] }],
  [{ coefficient := 2, powers := [(30, 1)] }],
  [{ coefficient := 2, powers := [(17, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (30, 1)] }, { coefficient := -1, powers := [(12, 1), (33, 1), (37, 1), (39, 1), (59, 1), (64, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (25, 1), (33, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (39, 1), (59, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (36, 1), (39, 1), (42, 1), (64, 1)] }],
  [{ coefficient := 2, powers := [(42, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(5, 1), (25, 1), (33, 1), (47, 1)] }],
  [{ coefficient := 2, powers := [(39, 1), (60, 1)] }, { coefficient := -2, powers := [(40, 1), (42, 1), (57, 1), (63, 1)] }, { coefficient := 2, powers := [(42, 1), (57, 1)] }, { coefficient := -2, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (33, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (24, 1), (25, 1), (33, 1), (44, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (24, 1), (33, 1), (44, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (33, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (36, 1), (39, 1), (42, 1), (64, 1)] }, { coefficient := 4, powers := [(17, 1), (23, 1), (24, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (24, 1), (25, 1), (33, 1), (47, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (24, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (33, 1), (44, 1), (61, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (33, 1), (37, 1), (39, 1), (49, 1), (52, 1), (59, 1), (64, 1)] }, { coefficient := -2, powers := [(12, 1), (36, 1), (39, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 30,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB6_5.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB6_5
