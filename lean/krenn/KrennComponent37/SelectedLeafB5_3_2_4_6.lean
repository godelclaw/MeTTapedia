import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_3_2_4_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "49dd5735f398b6d6f9a7363779ea397d5d6a23ab1210a4f178251f33099811f8"
def certificateSHA256 : String := "7a337eab2d26714dca8b3182d43bfd47849be1a7e2b98502f8314dd138b75c20"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 673 := ![
  13,
  17,
  175,
  296,
  300,
  410,
  478,
  487,
  591,
  658,
  660,
  661,
  663,
  667,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(20, 1), (23, 1), (60, 1), (62, 1), (63, 1), (68, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (60, 1), (62, 1), (63, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (23, 1), (43, 1), (60, 1), (62, 1), (63, 1), (68, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (43, 1), (60, 1), (62, 1), (63, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1), (41, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (28, 1), (41, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (28, 1), (46, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (48, 1), (62, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(21, 1), (62, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (48, 1), (62, 1), (65, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (43, 1), (60, 1), (62, 1), (63, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (60, 1), (62, 1), (63, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (23, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (28, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (62, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (62, 1), (65, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (60, 1), (62, 1), (63, 1), (68, 1)] }, { coefficient := 1, powers := [(25, 1), (60, 1), (62, 1), (63, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(20, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (56, 1), (60, 1), (62, 1), (63, 1), (68, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (56, 1), (60, 1), (62, 1), (63, 1), (68, 1)] }, { coefficient := -1, powers := [(17, 1), (20, 1), (28, 1), (60, 1), (62, 1), (63, 1), (68, 1)] }, { coefficient := -1, powers := [(17, 1), (25, 1), (28, 1), (60, 1), (62, 1), (63, 1), (68, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (43, 1), (60, 1), (62, 1), (63, 1), (68, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (28, 1), (43, 1), (60, 1), (62, 1), (63, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (42, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (42, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (42, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (37, 1), (60, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (25, 1), (37, 1), (60, 1), (62, 1), (63, 1)] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_3_2_4_6.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_3_2_4_6
