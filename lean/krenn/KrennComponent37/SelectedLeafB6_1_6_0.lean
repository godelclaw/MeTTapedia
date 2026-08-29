import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB6_1_6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cae2b38e95ee373e7ebd2a50ab8cf9756636326806fe18eab4b75347e98ae8c6"
def certificateSHA256 : String := "34ef1168143cf8f926afd8ba1e0566ff30c5790dabc700aa7df2165dd740748c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 5 → Fin 670 := ![
  29,
  287,
  659,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 5 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(1, 1), (21, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (21, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 5 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(51, 1), (63, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(63, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(1, 1), (42, 1), (63, 1), (64, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 5,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB6_1_6_0.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB6_1_6_0
