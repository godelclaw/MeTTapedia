import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_2_3_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "76548e83f7a507c97c4f30c35fd6efa782ff64dfd56990a2a09bacb27893cfad"
def certificateSHA256 : String := "86e00def1ee51c5fc509fecdf2f17310c138b091266df3b274171dcce36876d1"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 673 := ![
  14,
  26,
  232,
  280,
  304,
  305,
  318,
  396,
  422,
  441,
  482,
  511,
  515,
  602,
  603,
  649,
  659,
  662,
  663,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(10, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(10, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (44, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (35, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (23, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(14, 1), (27, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(4, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (33, 1), (51, 1)] }, { coefficient := 1, powers := [(7, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(7, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (39, 1)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (36, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(20, 1), (24, 1), (35, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (30, 1), (35, 1), (44, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (30, 1), (35, 1), (56, 2), (65, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (35, 1), (39, 1), (44, 1), (65, 1)] }, { coefficient := -2, powers := [(24, 1), (33, 1), (35, 1), (39, 1), (56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (35, 1), (42, 1), (56, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (35, 1), (56, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1), (44, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1), (56, 2), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (39, 1), (44, 1), (65, 1)] }, { coefficient := 2, powers := [(33, 1), (35, 1), (39, 1), (56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (35, 1), (56, 1), (59, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (51, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(35, 1), (56, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (20, 1), (35, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (21, 1), (33, 1), (35, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (33, 1), (35, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (27, 1), (33, 1), (35, 1), (44, 1), (62, 1)] }, { coefficient := -1, powers := [(21, 1), (62, 1)] }, { coefficient := -1, powers := [(26, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (33, 1), (35, 1), (44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (16, 1), (33, 1), (35, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (35, 1), (44, 1), (59, 1)] }, { coefficient := 2, powers := [(20, 1), (35, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (39, 2)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (39, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (35, 1), (59, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (28, 1), (35, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(30, 1), (35, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (35, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(35, 1), (36, 1), (59, 2)] }, { coefficient := -1, powers := [(35, 1), (39, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (39, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(35, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(35, 1), (51, 1), (56, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (33, 1), (35, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (33, 1), (35, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(35, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(10, 1), (30, 1), (35, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (30, 1), (35, 1), (56, 2)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (39, 1), (44, 1)] }, { coefficient := -2, powers := [(10, 1), (33, 1), (35, 1), (39, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (20, 1), (35, 1), (44, 1), (59, 2)] }, { coefficient := -2, powers := [(4, 1), (20, 1), (35, 1), (51, 1), (59, 2)] }, { coefficient := -1, powers := [(4, 1), (20, 1), (35, 1), (56, 1), (59, 2)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (35, 1), (39, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (30, 1), (35, 1), (51, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (35, 1), (36, 1), (59, 2)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (35, 1), (39, 2), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (33, 1), (35, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (21, 1), (33, 1), (35, 1), (39, 1), (44, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (21, 1), (33, 1), (35, 1), (39, 1), (44, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (21, 1), (33, 1), (35, 1), (44, 2), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (21, 1), (33, 1), (35, 1), (44, 2), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (27, 1), (33, 1), (35, 1), (39, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(10, 1), (16, 1), (27, 1), (33, 1), (35, 1), (44, 2), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (35, 1), (44, 2), (59, 1)] }, { coefficient := -2, powers := [(10, 1), (20, 1), (35, 1), (44, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (20, 1), (35, 1), (44, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (30, 1), (35, 1), (39, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (30, 1), (35, 1), (44, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (36, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (39, 2), (44, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (35, 1), (39, 1), (44, 1), (51, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (35, 1), (39, 1), (44, 1), (59, 1)] }, { coefficient := -2, powers := [(14, 1), (20, 1), (35, 1), (39, 1), (51, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (35, 1), (39, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (35, 1), (39, 2), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (30, 1), (35, 1), (39, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (35, 1), (36, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (35, 1), (39, 3)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (35, 1), (39, 2), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (35, 1), (59, 2)] }, { coefficient := -1, powers := [(10, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (35, 1), (44, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (35, 1), (59, 2)] }, { coefficient := 1, powers := [(10, 1), (20, 1), (35, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (35, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (35, 1), (44, 1), (59, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (35, 1), (51, 1), (59, 1)] }]
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
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_2_3_1.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_2_3_1
