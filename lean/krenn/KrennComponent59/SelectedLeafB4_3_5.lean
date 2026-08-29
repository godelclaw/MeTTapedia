import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component59.SelectedLeafB4_3_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "805823e08896297d8c3a5f49b71fd0d43a8ff2f5e3cb7cbe782d74ef5e82c826"
def certificateSHA256 : String := "79af2b44faa458724d3bc4efad58e880883572dd9ef4eebedae9a4ba51bcd619"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 7 → Fin 620 := ![
  26,
  27,
  458,
  583,
  616,
  618,
  619
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 7 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (50, 1)] }, { coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(38, 1)] }, { coefficient := 1, powers := [(44, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (62, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 7 → SparsePoly (Fin 63) := ![
  [{ coefficient := 1, powers := [(44, 1), (50, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(50, 1), (60, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(44, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(60, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (44, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(19, 1), (47, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (44, 1), (50, 1), (60, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (60, 1)] }]
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
    ¬ ∀ index : Fin 7,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component59.SelectedLeafB4_3_5.selectedHasNoCommonZero

end Krenn.Component59.SelectedLeafB4_3_5
