import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_3_6_5_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b22f9c0c0797d1e7b9c34ee9711e11bfaabfee425eaa3c8f873ea7fb5a0d6a79"
def certificateSHA256 : String := "c919f34ff7af9827fb2f86bd221d88d9cc839cef5c66bd4e0885135c17f5eef6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 4 → Fin 673 := ![
  487,
  499,
  660,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 4 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (28, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 4 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (18, 1), (28, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (23, 1), (63, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 4,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_3_6_5_4.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_3_6_5_4
