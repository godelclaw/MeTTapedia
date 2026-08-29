import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_0_6_7

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "87b296fcb5a54adc9468b4503782077e4ffb664d078e79be2d8f939a2013f92a"
def certificateSHA256 : String := "b445cc25be3f0949196b0b0bec5153973d322ebe89b2f3c428800815e6e1a426"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 23 → Fin 670 := ![
  15,
  17,
  25,
  150,
  267,
  300,
  301,
  302,
  308,
  349,
  487,
  581,
  583,
  591,
  602,
  603,
  655,
  660,
  661,
  664,
  665,
  668,
  669
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 23 → SparsePoly (Fin 69) := ![
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (28, 1)] }, { coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1)] }, { coefficient := 1, powers := [(23, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1), (68, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 23 → SparsePoly (Fin 69) := ![
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (37, 1), (59, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (37, 1), (59, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (23, 1), (59, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (28, 1), (59, 1), (63, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (23, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (23, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (50, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (31, 1), (37, 1), (54, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(13, 1), (30, 1), (31, 1), (37, 1), (64, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (50, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (50, 1), (67, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (17, 1), (28, 1), (37, 1), (60, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (20, 1), (28, 1), (60, 1), (63, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (37, 1), (57, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (57, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (67, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (67, 1)] }, { coefficient := -1, powers := [(56, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (64, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (17, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (20, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (31, 1), (37, 1), (54, 1), (64, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (31, 1), (37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (30, 1), (31, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (37, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (2, 1), (37, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (13, 1), (37, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (27, 1), (28, 1), (37, 1), (60, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (28, 1), (37, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (20, 1), (56, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (20, 1), (27, 1), (28, 1), (60, 1), (63, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (28, 1), (43, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1)] }, { coefficient := -1, powers := [(13, 1), (20, 1), (27, 1), (37, 1), (57, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(13, 1), (27, 1), (37, 1), (60, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (28, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1), (56, 1), (57, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (27, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (27, 1), (43, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1)] }, { coefficient := -1, powers := [(27, 1), (34, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(56, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (23, 1), (31, 1), (37, 1), (54, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (13, 1), (31, 1), (37, 1), (60, 1)] }, { coefficient := -1, powers := [(3, 1), (31, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (9, 1), (17, 1), (28, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (23, 1), (37, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (28, 1), (37, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (9, 1), (17, 1), (20, 1), (28, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (23, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (28, 1), (59, 1), (63, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (20, 1), (37, 1), (57, 1), (60, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (13, 1), (37, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(13, 1), (28, 1), (31, 1), (37, 1), (43, 1), (54, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (31, 1), (37, 1), (43, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (31, 1), (37, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (31, 1), (37, 1), (57, 1)] }]
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
    ¬ ∀ index : Fin 23,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_0_6_7.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_0_6_7
