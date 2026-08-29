import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component65.SelectedLeafB4_5_3_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "03d91a4836fbf36c32bbe8b83efac1e6641740a3dcd5bc59f99e1ae2fc42df1e"
def certificateSHA256 : String := "c69df60ec6b51060da2a509ce04924179b4180871d3ad927d0f79bdfb93a96b7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 6 → Fin 674 := ![
  411,
  444,
  610,
  666,
  670,
  671
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 6 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (51, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1)] }, { coefficient := 1, powers := [(42, 1), (51, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(42, 1), (53, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(24, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 6 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(25, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(53, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (57, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(25, 1), (39, 1), (42, 1), (51, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (45, 1), (51, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (42, 1), (53, 1), (65, 1)] }, { coefficient := 1, powers := [(45, 1), (53, 1), (65, 1)] }]
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
    ¬ ∀ index : Fin 6,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component65.SelectedLeafB4_5_3_0.selectedHasNoCommonZero

end Krenn.Component65.SelectedLeafB4_5_3_0
