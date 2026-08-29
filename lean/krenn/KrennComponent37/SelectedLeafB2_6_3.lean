import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB2_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "90050df36bcc9d080a3650bb2f6f8b3da522f6596cebb9eec08c266ac3d37cf5"
def certificateSHA256 : String := "dcf8f03fcfde6969c371f038356ceabda4f8a54b356ef6c21b5e99c74c8ac1bc"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 4 → Fin 667 := ![
  31,
  659,
  661,
  666
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 4 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(1, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 4 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(62, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(40, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(1, 1), (40, 1), (62, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 4,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB2_6_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB2_6_3
