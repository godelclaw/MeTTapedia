import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_0_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3bd6e455a7aa36f7056acd95e8236fb02701da4a076fb293c442fb300bf1c2f0"
def certificateSHA256 : String := "d0a7e52710edb2234880de2ce09711d27bd5cb02c23e6e5b342e0dd4539bb949"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 673 := ![
  22,
  173,
  304,
  305,
  318,
  416,
  439,
  441,
  482,
  511,
  515,
  537,
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
def selectedEquations : Fin 22 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(16, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(7, 1), (21, 1), (33, 1), (39, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (33, 1), (39, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (33, 1), (36, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (26, 1), (33, 1), (35, 1), (51, 2), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (26, 1), (33, 1), (36, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (33, 1), (35, 1), (51, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (18, 1), (25, 1), (44, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (35, 1), (39, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (33, 1), (35, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (26, 1), (33, 1), (35, 1), (51, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (16, 1), (33, 1), (35, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (25, 1), (39, 1), (44, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (44, 2)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(20, 1), (39, 1)] }, { coefficient := -1, powers := [(20, 1), (44, 1)] }, { coefficient := -2, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (39, 2)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (39, 1), (51, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (25, 1), (44, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (39, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (44, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (28, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (28, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1)] }, { coefficient := -1, powers := [(28, 1), (33, 1), (35, 1), (39, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (35, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (10, 1), (33, 1), (35, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (26, 1), (33, 1), (35, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (18, 1), (25, 1), (28, 1), (44, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (25, 1), (44, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (28, 1), (65, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (28, 1), (65, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (33, 1), (35, 1), (39, 1), (65, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (18, 1), (25, 1), (39, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (25, 1), (44, 2), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (18, 1), (25, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (44, 1), (59, 1)] }, { coefficient := 2, powers := [(4, 1), (20, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (35, 1), (39, 2), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (35, 1), (39, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (35, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (25, 1), (39, 1), (44, 2)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (25, 1), (44, 3)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (25, 1), (44, 2), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (44, 2)] }, { coefficient := 2, powers := [(10, 1), (20, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (39, 2), (44, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (39, 1), (44, 2)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (39, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (25, 1), (39, 2), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (25, 1), (39, 1), (44, 2)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (25, 1), (39, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 2)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 1), (44, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (39, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (35, 1), (39, 3)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (35, 1), (39, 2), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (35, 1), (39, 2), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (16, 1), (21, 1), (33, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (26, 1), (33, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (21, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (26, 1), (33, 1), (35, 1), (51, 2), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (26, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (27, 1), (33, 1), (35, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (18, 1), (25, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (35, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (25, 1), (39, 1), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (25, 1), (44, 2)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (25, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (39, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (44, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (35, 1), (39, 2)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (35, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (35, 1), (39, 1), (51, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_0_3.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_0_3
