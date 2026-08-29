import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component58.SelectedLeafB6_3_6_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "89cae80b41c72e4f382958a416cfa1a755711df1ccefa50552c024a6d6690b4e"
def certificateSHA256 : String := "342936c3a5464f65d67c5b3f837c553d5501a683577e4d056a58df2c7aba2d67"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 10 → Fin 625 := ![
  148,
  218,
  225,
  566,
  567,
  617,
  618,
  619,
  622,
  624
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 10 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(15, 1), (28, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (48, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (39, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (39, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (53, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (40, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(21, 1), (48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (61, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 10 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(61, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (43, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (53, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (43, 1), (53, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (32, 1), (43, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(15, 1), (39, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (40, 1), (43, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (53, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (39, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (32, 1), (43, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (39, 1), (61, 1), (63, 1)] }]
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 10,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component58.SelectedLeafB6_3_6_1.selectedHasNoCommonZero

end Krenn.Component58.SelectedLeafB6_3_6_1
