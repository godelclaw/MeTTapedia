import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB1_2_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "424bb5beeccf0f5242e51afc964a7d774b767c28dbe845ca958c30b46ad7a5da"
def certificateSHA256 : String := "e70780a840748201a063689955c421768e82b22ec4a9c6af356bd1d2dcdc485e"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 15 → Fin 667 := ![
  175,
  410,
  430,
  435,
  453,
  455,
  500,
  526,
  580,
  581,
  645,
  658,
  660,
  662,
  665
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 15 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 15 → SparsePoly (Fin 65) := ![
  [{ coefficient := 1, powers := [(29, 1), (52, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 2, powers := [(29, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(62, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(25, 1), (29, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (29, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (29, 1), (62, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (60, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (41, 1), (57, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (46, 1), (52, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (52, 1), (62, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (29, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (29, 1), (62, 1), (63, 1)] }]
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
    ¬ ∀ index : Fin 15,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB1_2_4.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB1_2_4
