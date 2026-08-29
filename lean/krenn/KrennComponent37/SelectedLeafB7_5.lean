import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB7_5

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "a9ce1c5842a8e061111bbedefbabffa1c228d400f9cc5fd69827f353d427d97b"
def certificateSHA256 : String := "2d7f545554d98b724e5733204c16c8c925f65d566fe3c2142515502def64e059"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 16 → Fin 664 := ![
  0,
  16,
  196,
  315,
  393,
  425,
  436,
  479,
  555,
  580,
  609,
  659,
  660,
  661,
  662,
  663
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 67) := ![
  [{ coefficient := 1, powers := [(1, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (29, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (21, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1)] }, { coefficient := 1, powers := [(42, 1)] }, { coefficient := 1, powers := [(48, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (66, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 67) := ![
  [{ coefficient := -1, powers := [(0, 1), (53, 1), (63, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (20, 1), (29, 1), (63, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (63, 1), (64, 1), (66, 1)] }, { coefficient := -1, powers := [(25, 1), (51, 1), (52, 1), (63, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (29, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (29, 1), (42, 1), (64, 1), (65, 1), (66, 1)] }, { coefficient := -1, powers := [(23, 1), (42, 1), (64, 1), (65, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (29, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (29, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (64, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (51, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1), (53, 1), (66, 1)] }, { coefficient := -1, powers := [(12, 1), (20, 1), (29, 1), (48, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (48, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (51, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(21, 1), (53, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (29, 1), (42, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (42, 1), (64, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (25, 1), (51, 1), (52, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB7_5.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB7_5
