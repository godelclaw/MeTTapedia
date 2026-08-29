import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB1_3_6_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "0aad1175fee56c03a75a218361729bb23b6a126da4354dda3bc53d96a9d64158"
def certificateSHA256 : String := "00caea38f0097821372ab8d70a03e885201b90f275e8481aa9c39d06efff6ff7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 9 → Fin 670 := ![
  27,
  315,
  471,
  478,
  609,
  658,
  663,
  667,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 9 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(27, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 9 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(51, 1), (64, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (46, 2), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (46, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(42, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(48, 1), (53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(21, 1), (46, 2), (51, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (46, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(42, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (51, 1), (64, 1)] }]
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
    (values : Fin 69 → R) :
    ¬ ∀ index : Fin 9,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB1_3_6_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB1_3_6_3
