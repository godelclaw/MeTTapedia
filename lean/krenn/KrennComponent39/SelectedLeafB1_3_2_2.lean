import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_3_2_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "ae6d8555fd073fcc35d0dd25438b634ea3d3899aef069c23085d6536902edafc"
def certificateSHA256 : String := "a24c158deb91538332e4371bc99783e84ca872ec9d8e6b99773237b0be74078f"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 9 → Fin 673 := ![
  30,
  321,
  457,
  465,
  608,
  661,
  666,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 9 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 9 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(49, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (44, 2), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (44, 1), (49, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(40, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(19, 1), (44, 2), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (44, 1), (49, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(40, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1), (56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (49, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 9,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_3_2_2.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_3_2_2
