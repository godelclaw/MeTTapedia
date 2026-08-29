import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_2_7_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0c14c104dfbcfd4d263d0498a2656434fa3339b4bb2b2b854295e45776df734c"
def certificateSHA256 : String := "4fbb8760253ebc2db9a71fb301ec950c0397e87fbd9757961bf6af32998f091a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 12 → Fin 673 := ![
  318,
  422,
  424,
  433,
  439,
  462,
  570,
  607,
  661,
  663,
  669,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 12 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(27, 1), (57, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 12 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (42, 2), (61, 1), (65, 2)] }],
  [{ coefficient := 1, powers := [(24, 1), (42, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (61, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (42, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (24, 1), (42, 1), (61, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (24, 1), (42, 1), (61, 1), (65, 2)] }],
  [{ coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (45, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(39, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(45, 1), (53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (42, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (27, 1), (42, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(16, 1), (24, 1), (42, 2), (44, 1), (61, 1), (65, 2)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (42, 1), (45, 1), (61, 1), (65, 2)] }, { coefficient := 1, powers := [(16, 1), (42, 1), (61, 1), (65, 1)] }]
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
    ¬ ∀ index : Fin 12,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_2_7_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_2_7_4
