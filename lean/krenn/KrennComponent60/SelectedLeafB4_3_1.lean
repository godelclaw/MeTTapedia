import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component60.SelectedLeafB4_3_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "21817c7d2ee0445b2500b6771eb72b9d4ea4a79bbaaf289a13436e529303d36c"
def certificateSHA256 : String := "e4169d82c00d0df1590727fa6e746717b35d376a1093dcdb1b617e2472d3b639"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 11 → Fin 665 := ![
  312,
  316,
  424,
  425,
  454,
  471,
  579,
  609,
  661,
  663,
  664
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 11 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (51, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (26, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (64, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 11 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(21, 1), (52, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (47, 1), (52, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (52, 1), (53, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(26, 1), (52, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(47, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(43, 1), (47, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(48, 1), (52, 1), (63, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (51, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(47, 1), (52, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (51, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(52, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (43, 1), (47, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (48, 1), (52, 1), (63, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (26, 1), (43, 1), (47, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (26, 1), (48, 1), (52, 1), (63, 1), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (50, 1), (63, 1)] }, { coefficient := -1, powers := [(21, 1), (50, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (47, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 11,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component60.SelectedLeafB4_3_1.selectedHasNoCommonZero

end Krenn.Component60.SelectedLeafB4_3_1
