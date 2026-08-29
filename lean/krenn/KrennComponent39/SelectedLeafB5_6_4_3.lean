import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_6_4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "decca61c9b3ed8ba0564d69817e24e64c58a63e73ce3716c033cad55227f4cb1"
def certificateSHA256 : String := "068d682d0ad578220dc7c3c3b24afeb713a97b9d172c1de68e2e540c16232897"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 673 := ![
  26,
  173,
  174,
  176,
  304,
  305,
  318,
  476,
  511,
  512,
  515,
  539,
  602,
  603,
  659,
  662,
  664,
  668,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (23, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1)] }, { coefficient := 1, powers := [(14, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (28, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (50, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (38, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1)] }, { coefficient := 1, powers := [(14, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(14, 1), (27, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (27, 1), (44, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(27, 1), (33, 1), (36, 1), (53, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (27, 1), (44, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (33, 1), (36, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (44, 1), (67, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (51, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (44, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (53, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(28, 1), (44, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -2, powers := [(20, 1), (28, 1), (51, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (27, 1), (38, 1), (53, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (27, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (38, 1), (44, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (28, 1), (39, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (28, 1), (44, 1), (67, 1)] }, { coefficient := -1, powers := [(28, 1), (33, 1), (36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (25, 1), (44, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (33, 1), (36, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (25, 1), (44, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (28, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1), (25, 1), (44, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (33, 1), (36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (28, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1), (53, 1), (56, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (50, 1), (53, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1), (44, 1), (56, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1), (50, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(28, 1), (44, 1), (51, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (27, 1), (33, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (28, 1), (33, 1), (44, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (30, 1), (67, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (28, 1), (67, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (20, 1), (28, 1), (51, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (27, 1), (38, 1), (53, 1), (59, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (27, 1), (53, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(4, 1), (25, 1), (28, 1), (38, 1), (44, 1), (59, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (28, 1), (39, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (28, 1), (44, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (33, 1), (36, 1), (59, 1), (67, 1)] }, { coefficient := 2, powers := [(10, 1), (20, 1), (28, 1), (44, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (27, 1), (38, 1), (44, 1), (53, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(10, 1), (25, 1), (28, 1), (38, 1), (44, 2), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (28, 1), (39, 1), (44, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (28, 1), (44, 2), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (27, 1), (33, 1), (36, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (33, 1), (36, 1), (44, 1), (67, 1)] }, { coefficient := 2, powers := [(14, 1), (20, 1), (28, 1), (39, 1), (51, 1), (67, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (27, 1), (38, 1), (39, 1), (53, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (27, 1), (39, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(14, 1), (25, 1), (28, 1), (38, 1), (39, 1), (44, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (28, 1), (39, 2), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (28, 1), (39, 1), (44, 1), (67, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (33, 1), (36, 1), (39, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_6_4_3.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_6_4_3
