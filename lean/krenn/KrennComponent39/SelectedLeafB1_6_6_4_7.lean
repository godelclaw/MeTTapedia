import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_6_6_4_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "83e8b4503ffa2f44cd4237836ffe1ab1e82a5f0322257c36fe615436b6a71ab6"
def certificateSHA256 : String := "e0e297af30acf078905ac2b3588bc72d36471db4a43eb2b012f562b23dd45b5e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 676 := ![
  65,
  82,
  171,
  173,
  187,
  304,
  305,
  396,
  416,
  422,
  439,
  441,
  473,
  476,
  505,
  511,
  532,
  537,
  580,
  581,
  602,
  603,
  644,
  659,
  661,
  662,
  663,
  664,
  671,
  673,
  675
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(1, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (18, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (18, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1), (69, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(33, 1), (36, 1), (59, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (36, 1), (59, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (33, 1), (36, 1), (59, 1), (69, 1)] }, { coefficient := -1, powers := [(20, 1), (59, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (33, 1), (36, 1), (59, 1), (69, 1)] }, { coefficient := 1, powers := [(30, 1), (56, 1), (69, 1)] }, { coefficient := -1, powers := [(33, 1), (44, 1), (69, 1)] }, { coefficient := 1, powers := [(33, 1), (51, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (51, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (23, 1), (27, 1), (33, 1), (36, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (27, 1), (33, 1), (36, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (27, 1), (33, 1), (36, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (27, 1), (33, 1), (36, 1), (56, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }, { coefficient := -1, powers := [(56, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (18, 1), (27, 1), (33, 1), (36, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (27, 1), (61, 1)] }, { coefficient := -2, powers := [(10, 1), (23, 1), (27, 1), (33, 1), (36, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (27, 1), (33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (18, 1), (33, 1), (36, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1), (33, 1), (36, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 1), (33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (18, 1), (23, 1), (27, 1), (33, 1), (36, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (23, 1), (27, 1), (61, 1)] }, { coefficient := 2, powers := [(10, 1), (23, 2), (27, 1), (33, 1), (36, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (23, 2), (27, 1), (33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (16, 1), (18, 1), (23, 1), (33, 1), (36, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (20, 1), (23, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (23, 2), (33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(59, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(51, 1), (62, 1)] }, { coefficient := -1, powers := [(56, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (16, 1), (23, 1), (33, 1), (36, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (23, 1), (33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (16, 1), (18, 1), (33, 1), (36, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (20, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (23, 1), (33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (16, 1), (18, 1), (27, 1), (33, 1), (36, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (20, 1), (27, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (23, 1), (27, 1), (33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (16, 1), (23, 1), (27, 1), (33, 1), (36, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (16, 1), (23, 1), (27, 1), (33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(23, 1), (33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (18, 1), (27, 1), (33, 1), (36, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (20, 1), (27, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (23, 1), (27, 1), (33, 1), (36, 1), (44, 1), (61, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (23, 1), (27, 1), (33, 1), (36, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (16, 1), (23, 1), (27, 1), (33, 1), (36, 1), (51, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (33, 1), (36, 2), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (18, 1), (33, 1), (36, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (44, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := 2, powers := [(38, 1), (51, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(38, 1), (56, 2), (62, 1)] }, { coefficient := 1, powers := [(39, 1), (56, 1)] }, { coefficient := -1, powers := [(43, 1), (50, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(44, 2)] }, { coefficient := 2, powers := [(50, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(50, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (18, 1), (33, 1), (36, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (44, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (33, 1), (36, 1), (44, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (33, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (33, 1), (36, 1), (51, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (58, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 2, powers := [(14, 1), (38, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (38, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(14, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (20, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (18, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (20, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (44, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (33, 1), (36, 1), (59, 1)] }, { coefficient := -1, powers := [(7, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (44, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (51, 1)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_6_6_4_7.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_6_6_4_7
