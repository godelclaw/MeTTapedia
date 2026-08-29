import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB5_6_4

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "dc71ef32ee9f5d88b531c90ff5c59ce4bfe806cea6cbd923250f11b54eea1c55"
def certificateSHA256 : String := "eee0e46558663f06bdeba9577a6e02dc89f8321ffbd7e0c232fafb3c419b03c6"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 20 → Fin 611 := ![
  5,
  7,
  19,
  27,
  32,
  183,
  311,
  325,
  327,
  434,
  468,
  486,
  550,
  601,
  602,
  604,
  607,
  608,
  609,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(3, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(6, 1), (19, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 64) := ![
  [{ coefficient := 1, powers := [(2, 1), (24, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (24, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (19, 1), (23, 1), (57, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (22, 1), (38, 1), (58, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(2, 1), (27, 1), (38, 1), (58, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (22, 1), (23, 1), (58, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (27, 1), (58, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (43, 1), (57, 1)] }, { coefficient := -1, powers := [(17, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (38, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (57, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (36, 1), (57, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (38, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (36, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (35, 1)] }, { coefficient := -1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (17, 1), (22, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (17, 1), (27, 1), (38, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (17, 1), (22, 1), (23, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(8, 1), (17, 1), (23, 1), (27, 1), (58, 1), (60, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := -1, powers := [(13, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (19, 1), (35, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (32, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1)] }]
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
    (values : Fin 64 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB5_6_4.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB5_6_4
