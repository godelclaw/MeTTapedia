import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component11.SelectedLeafB6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "addd1381367ac776b96ad3d8620be7e388e4b870d987d501eac22deb9a736ba5"
def certificateSHA256 : String := "7cbf1357a553548f0a844c16a31c158dc926fbb49753e42d35de3a7cafef1b36"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 669 := ![
  7,
  10,
  11,
  16,
  25,
  30,
  166,
  175,
  184,
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
  589,
  614,
  616,
  662,
  663,
  665,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(6, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
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
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(12, 1), (23, 1), (39, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (37, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (37, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (36, 1), (42, 1), (52, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (36, 1), (42, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (39, 1), (42, 1), (46, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (36, 1), (42, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (36, 1), (42, 1), (59, 1), (61, 1), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (25, 1), (33, 1), (47, 1), (61, 1), (63, 1)] }, { coefficient := 2, powers := [(5, 1), (33, 1), (47, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1), (61, 1), (63, 1)] }, { coefficient := -2, powers := [(12, 1), (30, 1), (49, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (33, 1), (37, 1), (39, 1), (49, 1), (52, 1), (59, 1), (63, 2)] }],
  [{ coefficient := 2, powers := [(5, 1), (25, 1), (33, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (39, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (39, 1), (49, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (39, 1), (42, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (18, 1), (36, 1), (42, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1), (63, 1)] }],
  [{ coefficient := -4, powers := [(23, 1), (54, 1)] }, { coefficient := -2, powers := [(30, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(12, 1), (30, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (33, 1), (37, 1), (39, 1), (52, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(54, 1)] }],
  [{ coefficient := 2, powers := [(49, 1)] }],
  [{ coefficient := 2, powers := [(30, 1)] }],
  [{ coefficient := 2, powers := [(17, 1)] }],
  [{ coefficient := -2, powers := [(12, 1), (30, 1)] }, { coefficient := -1, powers := [(12, 1), (33, 1), (37, 1), (39, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (25, 1), (33, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(12, 1), (39, 1), (59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (36, 1), (39, 1), (42, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (36, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (33, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 2, powers := [(5, 1), (25, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (36, 1), (42, 2), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(39, 1), (60, 1)] }, { coefficient := 2, powers := [(42, 1), (57, 1)] }, { coefficient := -2, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (33, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (24, 1), (25, 1), (33, 1), (44, 1), (61, 1)] }, { coefficient := 2, powers := [(5, 1), (24, 1), (33, 1), (44, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (33, 1), (44, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (36, 1), (39, 1), (42, 1), (63, 1)] }, { coefficient := 4, powers := [(17, 1), (23, 1), (24, 1), (54, 1)] }, { coefficient := 2, powers := [(17, 1), (24, 1), (30, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (8, 1), (24, 1), (36, 1), (42, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (24, 1), (36, 1), (42, 1), (59, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (24, 1), (25, 1), (33, 1), (47, 1), (61, 1)] }, { coefficient := -2, powers := [(5, 1), (24, 1), (33, 1), (47, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (25, 1), (33, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (36, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (18, 1), (36, 1), (42, 1), (61, 1)] }, { coefficient := -1, powers := [(8, 1), (24, 1), (36, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (36, 1), (42, 1), (61, 1)] }, { coefficient := 2, powers := [(12, 1), (24, 1), (30, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (33, 1), (37, 1), (39, 1), (49, 1), (52, 1), (59, 1), (63, 1)] }, { coefficient := -2, powers := [(12, 1), (36, 1), (39, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component11.SelectedLeafB6_1.selectedHasNoCommonZero

end Krenn.Component11.SelectedLeafB6_1
