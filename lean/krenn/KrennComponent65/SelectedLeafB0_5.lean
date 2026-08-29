import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component65.SelectedLeafB0_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "dac7fdf908c8d7cc01a204570dbc49a07311d77bbc6d2561e1a291e386a6d23a"
def certificateSHA256 : String := "68d3e556957cfed9b8f9483a820a12a4761372075a368fcd566dea9e0c117bfe"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 7 → Fin 668 := ![
  439,
  449,
  611,
  645,
  662,
  666,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 7 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1), (56, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(40, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(44, 1)] }, { coefficient := 1, powers := [(51, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 7 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(20, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(49, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (49, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (36, 1), (49, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (39, 1), (49, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (44, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(40, 1), (56, 1), (62, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1), (51, 1), (62, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (49, 1), (62, 1)] }],
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
    (values : Fin 63 → R) :
    ¬ ∀ index : Fin 7,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component65.SelectedLeafB0_5.selectedHasNoCommonZero

end Krenn.Component65.SelectedLeafB0_5
