import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_0_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "7c16536c2809c69b3bc08ac71379922034bf9891a9419501181cba8d2f2fed3b"
def certificateSHA256 : String := "ddb4e8f58be675e889cf6142f45e966c1248f2c90413e5f2850dc403390a1032"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 673 := ![
  304,
  305,
  318,
  396,
  416,
  422,
  439,
  441,
  482,
  511,
  515,
  529,
  580,
  602,
  603,
  649,
  659,
  662,
  663,
  668,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (14, 1), (20, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (26, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (27, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (33, 1), (35, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (33, 1), (35, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (33, 1), (35, 1), (44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (26, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (16, 1), (33, 1), (35, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (39, 1), (51, 1)] }, { coefficient := -2, powers := [(0, 1), (20, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (51, 2)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (36, 1), (51, 1)] }, { coefficient := -1, powers := [(20, 1), (39, 1)] }, { coefficient := -1, powers := [(20, 1), (44, 1)] }, { coefficient := -2, powers := [(20, 1), (51, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(20, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (28, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(20, 1), (28, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (44, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 2, powers := [(0, 1), (36, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (36, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (20, 1), (28, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (20, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (20, 1), (44, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (26, 1), (62, 1)] }, { coefficient := 1, powers := [(2, 1), (10, 1), (33, 1), (35, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (21, 1), (33, 1), (35, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (28, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (20, 1), (36, 1), (59, 2)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (20, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := 2, powers := [(0, 1), (4, 1), (20, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (20, 1), (51, 2), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (36, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (33, 1), (36, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (20, 1), (36, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (20, 1), (39, 1), (44, 1), (51, 1)] }, { coefficient := 2, powers := [(0, 1), (10, 1), (20, 1), (44, 2), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (20, 1), (44, 1), (51, 2)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (33, 1), (36, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (33, 1), (36, 1), (44, 2)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (33, 1), (36, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (20, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (20, 1), (39, 2), (51, 1)] }, { coefficient := 2, powers := [(0, 1), (14, 1), (20, 1), (39, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (20, 1), (39, 1), (51, 2)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (33, 1), (36, 1), (39, 2)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (33, 1), (36, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(0, 1), (14, 1), (33, 1), (36, 1), (39, 1), (51, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (26, 1), (39, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (16, 1), (26, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (39, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (44, 1), (59, 1)] }, { coefficient := 2, powers := [(4, 1), (20, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (39, 1), (44, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (44, 2)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 2)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (21, 1), (33, 1), (35, 1), (39, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (21, 1), (33, 1), (35, 1), (44, 2), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (21, 1), (33, 1), (36, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (21, 1), (33, 1), (36, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (26, 1), (33, 1), (36, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (26, 1), (33, 1), (36, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (27, 1), (33, 1), (35, 1), (39, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (27, 1), (33, 1), (35, 1), (44, 2), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (44, 2)] }, { coefficient := 2, powers := [(10, 1), (20, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 2)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 1), (44, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (39, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (44, 2)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (44, 2)] }, { coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (20, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (20, 1), (39, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (20, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(0, 1), (14, 1), (20, 1), (51, 2)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (39, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (51, 1)] }]
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
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_0_1.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_0_1
