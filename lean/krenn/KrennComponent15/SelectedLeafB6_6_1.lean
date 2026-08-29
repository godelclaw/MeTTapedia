import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component15.SelectedLeafB6_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4076c753d4e5090698650d1eacecde14ae3931b52fbf24a4e4cb768ab33e9baf"
def certificateSHA256 : String := "f3af4d35e482aba0d3b7af8704965b1f8073e8b7cbc70c723a87bc3f299022ea"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 5 → Fin 595 := ![
  0,
  350,
  587,
  589,
  594
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 5 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(1, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (23, 1), (40, 1), (47, 1)] }, { coefficient := 1, powers := [(1, 1), (36, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(36, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 5 → SparsePoly (Fin 62) := ![
  [{ coefficient := -1, powers := [(23, 1), (47, 1), (58, 1), (59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(58, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (53, 1), (59, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(53, 1), (61, 1)] }],
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 5,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component15.SelectedLeafB6_6_1.selectedHasNoCommonZero

end Krenn.Component15.SelectedLeafB6_6_1
