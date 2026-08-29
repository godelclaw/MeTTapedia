import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component36.SelectedLeafB4_1_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b5b0cfced3891114b6709d14976ed55aa4be1d53c900f6b54c9125218474f260"
def certificateSHA256 : String := "80a86771ae3368effcf8b995b44f9a5db39d8803406655bcc7efa5870fc27200"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 9 → Fin 672 := ![
  320,
  443,
  465,
  475,
  584,
  612,
  667,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 9 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(19, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (54, 1)] }, { coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 9 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(46, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (52, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (25, 1), (43, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (43, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (25, 1), (46, 1), (65, 1)] }],
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 9,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component36.SelectedLeafB4_1_5.selectedHasNoCommonZero

end Krenn.Component36.SelectedLeafB4_1_5
