import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_3_2_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "fb912eef6a0d098de200e06b3ad02ff6865ad3aabbd5c98dbeb304b1ea38dd9f"
def certificateSHA256 : String := "3ab65d252bf9880c658ec15dba3952649c07250eb1310eb8ceac2bef04661e35"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 14 → Fin 673 := ![
  321,
  396,
  416,
  439,
  441,
  457,
  465,
  532,
  580,
  608,
  661,
  663,
  666,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 14 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (26, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (39, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (51, 1)] }, { coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (39, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1), (51, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (27, 1), (59, 1)] }, { coefficient := 1, powers := [(26, 1), (39, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 14 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(19, 1), (23, 1), (44, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (56, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (46, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (27, 1), (40, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (40, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 2), (27, 1), (40, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 2), (40, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (23, 1), (44, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 2), (46, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (46, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (56, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (40, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (23, 1), (27, 1), (40, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (23, 1), (27, 1), (40, 1), (44, 1), (61, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (44, 2), (49, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (44, 2), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (44, 1), (49, 1), (56, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (44, 1), (52, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (44, 1), (52, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 2), (44, 1), (46, 1), (52, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (40, 1), (44, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (40, 1), (56, 2), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (40, 1), (56, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (46, 1), (49, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1), (56, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (46, 1), (52, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (46, 1), (52, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (40, 1), (44, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(19, 1), (23, 1), (44, 2), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (44, 1), (49, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(40, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 14,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_3_2_4.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_3_2_4
