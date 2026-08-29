import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_1_2_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4a3bbdbf59b0314d6507f34708bc35e18f3de1464d0e5cec45c0065f734551f7"
def certificateSHA256 : String := "c673055eb4768dd57a6957306a30ad0e3b9d4698d0d38f459503873fba941ece"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 7 → Fin 670 := ![
  315,
  436,
  478,
  578,
  662,
  663,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 7 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (38, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(38, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (63, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 7 → SparsePoly (Fin 64) := ![
  [{ coefficient := -1, powers := [(19, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(48, 1), (61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(61, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (48, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (23, 1), (48, 1), (61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(39, 1), (61, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 7,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_1_2_4.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_1_2_4
