import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component24.SelectedLeafB6_1_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "d1fcdaeaaba660264b85ce0ba381099f36bbb200b82324c88f3cf53c0ec73781"
def certificateSHA256 : String := "f97c6f8151b2fb7d7f048656ad38078dd682bb9c166e73c12688f3065015f538"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 10 → Fin 673 := ![
  91,
  149,
  151,
  152,
  266,
  319,
  589,
  668,
  669,
  670
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 10 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1)] }, { coefficient := 1, powers := [(21, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (54, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (21, 1), (54, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (53, 1)] }, { coefficient := 1, powers := [(35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1), (26, 1), (42, 1)] }, { coefficient := 1, powers := [(15, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 10 → SparsePoly (Fin 66) := ![
  [{ coefficient := 1, powers := [(51, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(51, 1), (53, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (53, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (51, 1), (64, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (43, 1), (56, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (35, 1), (43, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(15, 1), (21, 1), (51, 1), (64, 1), (65, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1), (43, 1), (64, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(56, 1), (65, 1)] }],
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
    ¬ ∀ index : Fin 10,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component24.SelectedLeafB6_1_4.selectedHasNoCommonZero

end Krenn.Component24.SelectedLeafB6_1_4
