import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB5_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1aa6f0beb6b9e85d7d9643b5400e6327de78f0834cac00c72cfd8feb3fd4dc5c"
def certificateSHA256 : String := "74f25472dbe8b4f8340ca0c0a2fa295cefa030ae1215470f46f7a3c163833f07"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 670 := ![
  187,
  188,
  300,
  318,
  342,
  394,
  396,
  416,
  422,
  439,
  441,
  458,
  487,
  505,
  532,
  580,
  581,
  644,
  649,
  663,
  665,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(16, 1), (18, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (18, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (42, 1)] }, { coefficient := 1, powers := [(17, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(23, 1), (27, 1), (42, 1), (44, 1), (53, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (27, 1), (51, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (27, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (27, 1), (53, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (23, 1), (27, 1), (44, 1), (53, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (23, 1), (42, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (27, 1), (51, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (27, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (27, 1), (62, 1)] }, { coefficient := 2, powers := [(27, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (62, 1)] }, { coefficient := -1, powers := [(62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (27, 1), (62, 1)] }, { coefficient := 1, powers := [(23, 2), (27, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 2), (27, 1), (62, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (27, 1), (42, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(23, 1), (27, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(23, 1), (28, 1), (42, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (16, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (27, 1), (42, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (51, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (27, 1), (62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (23, 1), (27, 1), (62, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (64, 1)] }, { coefficient := 1, powers := [(51, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (39, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (23, 1), (27, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (27, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (39, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (23, 1), (27, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (18, 1), (27, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (21, 1), (23, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 2), (27, 1), (57, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 2), (27, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (24, 1), (27, 1), (42, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (27, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (28, 1), (42, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(64, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (23, 1), (51, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB5_6_1.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB5_6_1
