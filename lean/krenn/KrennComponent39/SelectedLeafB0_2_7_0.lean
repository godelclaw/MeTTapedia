import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component39.SelectedLeafB0_2_7_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "26d35de5de598ef9ea0bea6ec6d843bce51828192cbd18eb40c000ade2c0dbb0"
def certificateSHA256 : String := "186772714daedc13363edd5c6a8dd32444688ea529f3766caaa3f97ae215e66a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 7 → Fin 673 := ![
  410,
  458,
  462,
  607,
  661,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 7 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 7 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(24, 1), (39, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (39, 1), (45, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (45, 1), (64, 1)] }, { coefficient := -1, powers := [(39, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(42, 1), (44, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(45, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(24, 1), (39, 2), (42, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (39, 1), (42, 1), (44, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (39, 1), (42, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (39, 1), (45, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (45, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (45, 1), (51, 1), (64, 1)] }]
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
    (values : Fin 65 → R) :
    ¬ ∀ index : Fin 7,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component39.SelectedLeafB0_2_7_0.selectedHasNoCommonZero

end Krenn.Component39.SelectedLeafB0_2_7_0
