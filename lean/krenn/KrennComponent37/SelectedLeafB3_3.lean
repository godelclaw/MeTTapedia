import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB3_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "342d1a59926bf5a7e86a1eba1e56ccf94b62ebbfe829ad2dc8dc057256f0d5f6"
def certificateSHA256 : String := "072b3ae95863d5da55c910a4a108d8c103f85013ef621df8a5eed1a6fc2075a7"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 14 → Fin 664 := ![
  307,
  311,
  342,
  410,
  425,
  453,
  471,
  496,
  555,
  580,
  609,
  658,
  660,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 14 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(12, 1), (46, 1)] }, { coefficient := 1, powers := [(12, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 14 → SparsePoly (Fin 66) := ![
  [{ coefficient := -1, powers := [(21, 1), (28, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (51, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1), (51, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (29, 1), (51, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (51, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (29, 1), (51, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (46, 1), (53, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (42, 1), (57, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (48, 1), (53, 1), (63, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (21, 1), (29, 1), (46, 1), (51, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (48, 1), (51, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (65, 1)] }],
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
    (values : Fin 66 → R) :
    ¬ ∀ index : Fin 14,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB3_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB3_3
