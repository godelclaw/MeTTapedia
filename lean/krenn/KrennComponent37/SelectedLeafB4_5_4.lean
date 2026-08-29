import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB4_5_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "8d0c3f061c7f3e0a3d8e30fe5e13ad284c4b609ad08ba73a2b85328303f6fa41"
def certificateSHA256 : String := "5d087e90cc265c28976beabd62aff24e4fbfafd9e7b191c688415358c79214f9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 12 → Fin 667 := ![
  219,
  315,
  425,
  471,
  478,
  580,
  583,
  609,
  661,
  662,
  663,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 12 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(9, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 12 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(25, 1), (53, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (48, 1), (53, 1), (64, 2)] }, { coefficient := -1, powers := [(48, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(48, 1), (51, 1), (53, 1), (64, 2)] }, { coefficient := -1, powers := [(53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (64, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1), (64, 2)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1), (51, 1), (53, 1), (64, 2)] }, { coefficient := 1, powers := [(21, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (48, 1), (53, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (48, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (25, 1), (48, 1), (51, 1), (53, 1), (64, 2)] }, { coefficient := -1, powers := [(21, 1), (25, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (48, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (40, 1), (48, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (42, 1), (46, 1), (64, 1)] }, { coefficient := -1, powers := [(0, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (31, 1), (48, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (25, 1), (48, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(9, 1), (21, 1), (25, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (25, 1), (46, 1), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(25, 1), (48, 1), (51, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 12,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB4_5_4.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB4_5_4
