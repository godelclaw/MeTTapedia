import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB6_3_6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "6384cc22da0d7428efa3bd6e2fa4a12a07ff9a2da5f4fe3603efdfe92c920df4"
def certificateSHA256 : String := "c5d8b63e9c68039cf57fe852846b8c7a784db9fc96258fd21f213f080ce5e7fa"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 6 → Fin 625 := ![
  39,
  335,
  488,
  618,
  622,
  624
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 6 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(28, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(28, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 6 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(20, 1), (45, 1), (62, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (62, 1), (65, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(45, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(40, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (45, 1), (48, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (62, 1), (65, 1)] }]
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

#print axioms Krenn.Component58.SelectedLeafB6_3_6_7.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB6_3_6_7
