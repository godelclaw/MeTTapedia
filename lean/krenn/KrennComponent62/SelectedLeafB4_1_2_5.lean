import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component62.SelectedLeafB4_1_2_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "3f9a95ecdcc7db216d315235588d6528f18d480084ed2d006fb1bc27b823aeed"
def certificateSHA256 : String := "036fdfb916381ae1318f7814d4b1c727204b46fa486286820f42b6c5a5f5d990"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 5 → Fin 670 := ![
  21,
  478,
  663,
  667,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 5 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (48, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(23, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 5 → SparsePoly (Fin 65) := ![
  [{ coefficient := -1, powers := [(0, 1), (45, 1), (61, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(19, 1), (61, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (45, 1), (61, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(61, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (48, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (45, 1), (48, 1), (61, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 5,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component62.SelectedLeafB4_1_2_5.selectedHasNoCommonZero

end Krenn.Component62.SelectedLeafB4_1_2_5
