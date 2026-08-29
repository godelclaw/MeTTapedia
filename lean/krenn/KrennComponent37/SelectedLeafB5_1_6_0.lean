import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_1_6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "09916135c6bcce3b0a3993141da49f3cf7f6516bac7af0bc3e500ba229a0bec1"
def certificateSHA256 : String := "1a61cc9272686c67ae967572c60986d4e40eb68e94ef16c9d1317705fd003456"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 670 := ![
  315,
  410,
  425,
  430,
  435,
  453,
  455,
  471,
  478,
  487,
  580,
  606,
  609,
  645,
  648,
  658,
  660,
  662,
  663,
  667
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(25, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(48, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (23, 1), (37, 1), (46, 2), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (29, 1), (37, 1), (46, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (23, 1), (46, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (23, 1), (52, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (28, 1), (52, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (29, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (23, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (37, 1), (46, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (57, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (29, 1), (37, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(53, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (37, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (37, 1), (46, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (23, 1), (37, 1), (46, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (23, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (18, 1), (37, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (6, 1), (52, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (57, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (20, 1), (38, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (38, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 2), (37, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (20, 1), (38, 1), (46, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 2), (37, 1), (38, 1), (60, 2)] }, { coefficient := -1, powers := [(0, 2), (38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (37, 1), (38, 1), (60, 2)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (37, 1), (52, 1), (60, 2)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (2, 1), (37, 1), (57, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (18, 1), (23, 1), (37, 1), (46, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (37, 1), (57, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (18, 1), (23, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (28, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (37, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 2), (3, 1), (38, 1), (60, 2), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (18, 1), (23, 1), (37, 1), (41, 1), (46, 2), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 2), (18, 1), (23, 1), (37, 1), (46, 3), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (18, 1), (29, 1), (37, 1), (41, 1), (46, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (18, 1), (29, 1), (37, 1), (46, 2), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 2), (20, 1), (38, 1), (41, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 2), (20, 1), (38, 1), (46, 1), (60, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 2), (38, 1), (60, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (38, 1), (60, 2)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (18, 1), (23, 1), (41, 1), (46, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (18, 1), (23, 1), (41, 1), (52, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (18, 1), (23, 1), (46, 2), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (18, 1), (23, 1), (46, 1), (52, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (18, 1), (28, 1), (41, 1), (52, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (6, 1), (18, 1), (28, 1), (46, 1), (52, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (18, 1), (29, 1), (41, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (6, 1), (18, 1), (29, 1), (46, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (23, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (23, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (28, 1), (37, 1), (41, 1), (46, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (28, 1), (37, 1), (46, 2), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (28, 1), (41, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (28, 1), (46, 1), (57, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (37, 1), (41, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (29, 1), (37, 1), (46, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (38, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (38, 1), (46, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (41, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (37, 1), (46, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := -1, powers := [(21, 1), (41, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (46, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(42, 1), (46, 1), (64, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1), (64, 1)] }]
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
    (values : Fin 67 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_1_6_0.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_1_6_0
