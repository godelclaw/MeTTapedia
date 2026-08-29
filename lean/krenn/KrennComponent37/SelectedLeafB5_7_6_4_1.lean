import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_7_6_4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d6328e3d36d5f82b63fde7042de58c37870f97aba0e0009737b1ee6405848aed"
def certificateSHA256 : String := "a3b5d3e0f8d79ca801cc854c0bf7f61aee06849905d0a4debbaac590ff31e797"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 5 → Fin 673 := ![
  16,
  487,
  660,
  661,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 5 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(60, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 5 → SparsePoly (Fin 71) := ![
  [{ coefficient := -1, powers := [(23, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(28, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(18, 1), (23, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (37, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 5,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_7_6_4_1.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_7_6_4_1
