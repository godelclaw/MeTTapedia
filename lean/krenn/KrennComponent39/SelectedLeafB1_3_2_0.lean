import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB1_3_2_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c83bf8ebb1db7d73ed821f2c5595781b6c1e91be783d0b915e58ec9c47e10da9"
def certificateSHA256 : String := "658807a3e139863e1ade96abcdbb886547c698e9d7e073a4e43febaea826c2f2"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 7 → Fin 673 := ![
  321,
  457,
  465,
  608,
  661,
  666,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 7 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }, { coefficient := 1, powers := [(23, 1), (40, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 7 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(19, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(46, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(56, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (44, 2), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (44, 1), (49, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (52, 1), (63, 1)] }, { coefficient := -1, powers := [(40, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(44, 1), (46, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(19, 1), (44, 2), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(19, 1), (44, 1), (49, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(40, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(44, 1), (46, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1), (56, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 7,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB1_3_2_0.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB1_3_2_0
