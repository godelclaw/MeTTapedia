import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB1_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cf14b2571768e253a3702f682ad4ec6b42b015148ee6fd9c0712d124f476c5cb"
def certificateSHA256 : String := "b150e58be4513c434c89febc23ace6047f8572ecceb5e2e24610eb76c8341b73"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 10 → Fin 664 := ![
  16,
  196,
  430,
  435,
  453,
  645,
  658,
  660,
  661,
  662
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 10 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 10 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(23, 1), (52, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(28, 1), (52, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(28, 1), (57, 1), (62, 1), (63, 1), (64, 1)] }, { coefficient := 3, powers := [(29, 1), (62, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(62, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(62, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (62, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(41, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (57, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(46, 1), (64, 1)] }, { coefficient := 1, powers := [(52, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (23, 1), (52, 1), (62, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (23, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (52, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (57, 1), (62, 1), (64, 1)] }, { coefficient := -2, powers := [(18, 1), (29, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(57, 1), (64, 1)] }],
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
    ¬ ∀ index : Fin 10,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB1_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB1_7
