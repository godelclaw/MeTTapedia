import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component20.SelectedLeafB4_0_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "e4562d9205aedc83cab7b18ca06b6ee8b1d2ac77712a048a305a521fb5664f3a"
def certificateSHA256 : String := "15949dce7cc70e7e6b42fa8194bd61d0736bc7e90ff2a895d6c56567999c46f5"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 5 → Fin 645 := ![
  196,
  364,
  484,
  640,
  644
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 5 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(43, 1), (52, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 5 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(52, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (43, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(26, 1), (43, 1), (62, 1)] }],
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
    ¬ ∀ index : Fin 5,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component20.SelectedLeafB4_0_5.selectedHasNoCommonZero

end Krenn.Component20.SelectedLeafB4_0_5
