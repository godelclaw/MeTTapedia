import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b6c2737c4b781eef4ee03c34055298e259c682b364ed8084b182374a851898de"
def certificateSHA256 : String := "313b615249f0f068f7d3c8a0d1cc3764dff2f56cd93d360aed51f03d5f908831"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 9 → Fin 664 := ![
  15,
  16,
  131,
  132,
  480,
  610,
  658,
  659,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 9 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(14, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (51, 1)] }, { coefficient := 1, powers := [(14, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(39, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 9 → SparsePoly (Fin 63) := ![
  [{ coefficient := -1, powers := [(19, 1), (20, 1), (50, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1), (60, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (50, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(45, 1), (48, 1), (50, 1), (62, 1)] }, { coefficient := -1, powers := [(45, 1), (51, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (48, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (51, 1), (62, 1)] }],
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
    ¬ ∀ index : Fin 9,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB2_5.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB2_5
