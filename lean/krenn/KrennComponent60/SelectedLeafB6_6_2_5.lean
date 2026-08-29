import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB6_6_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3813b5f93c50fd7ed634349c0376bded2506a3e3a5c2c8f06f31c157b4641d84"
def certificateSHA256 : String := "7986aaf9edad5dc15698ef4697210d35f9b19cc1e7aa0f9bfe2d547a21748c33"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 6 → Fin 668 := ![
  75,
  151,
  179,
  659,
  660,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 6 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(9, 1), (29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1)] }, { coefficient := 1, powers := [(29, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (40, 1)] }, { coefficient := 1, powers := [(29, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(29, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 6 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(63, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (63, 1), (67, 2)] }],
  [{ coefficient := -1, powers := [(9, 1), (63, 1), (64, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (29, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (29, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(29, 1), (39, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 6,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB6_6_2_5.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB6_6_2_5
