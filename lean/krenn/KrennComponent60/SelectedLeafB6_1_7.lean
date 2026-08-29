import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB6_1_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "b266cec6d4f068e7e04ec9c4b939474e55bb7198b9b315d64fc950e475f90ae6"
def certificateSHA256 : String := "9750ec2863e2d27cd9f3fbb6ec8ac5846932f6b397917c7e2963815b4870fe69"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 11 → Fin 665 := ![
  314,
  315,
  422,
  423,
  466,
  468,
  578,
  608,
  660,
  661,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 11 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (59, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (43, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(43, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 11 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(21, 1), (46, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (47, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (46, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (46, 1), (47, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(53, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(46, 1), (50, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(46, 1), (54, 1), (63, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (45, 1), (46, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(46, 1), (53, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (45, 1), (46, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(46, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (46, 1), (50, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (46, 1), (54, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (46, 1), (50, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (46, 1), (54, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(26, 1), (43, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (46, 1), (53, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1), (66, 1)] }],
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 11,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB6_1_7.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB6_1_7
