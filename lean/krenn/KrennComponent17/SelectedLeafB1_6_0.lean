import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component17.SelectedLeafB1_6_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "1e745a408c5f27552cd1f31c7bafdea03af1d151c97632be4306da065b1df8db"
def certificateSHA256 : String := "0e932985701c150c6ab90890140afc130ef5d0e4d5c7cc92167b2ef974ce93bb"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 22 → Fin 611 := ![
  17,
  18,
  32,
  206,
  214,
  281,
  311,
  410,
  434,
  441,
  445,
  468,
  469,
  481,
  549,
  550,
  601,
  602,
  604,
  607,
  609,
  610
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(13, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1)] }, { coefficient := 1, powers := [(17, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (47, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (19, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (19, 1), (54, 1)] }, { coefficient := 1, powers := [(17, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(13, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (40, 1)] }, { coefficient := 1, powers := [(17, 1), (44, 1)] }, { coefficient := 1, powers := [(17, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(17, 1), (22, 1)] }, { coefficient := 1, powers := [(17, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (36, 1), (58, 1)] }, { coefficient := 1, powers := [(13, 1), (27, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (27, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (57, 1)] }, { coefficient := 1, powers := [(22, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (54, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (29, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (32, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (35, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(8, 1), (32, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(13, 1), (29, 1), (47, 1)] }, { coefficient := 1, powers := [(13, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(27, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (25, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (40, 1), (59, 1)] }, { coefficient := -1, powers := [(22, 1), (44, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (35, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(29, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (59, 1)] }, { coefficient := -1, powers := [(27, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := -1, powers := [(38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(17, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (22, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (27, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (35, 1), (36, 1), (44, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(17, 1), (22, 1), (44, 1), (59, 1)] }, { coefficient := -1, powers := [(17, 1), (27, 1), (50, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (36, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (19, 1), (29, 1), (36, 1), (47, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (36, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (32, 1), (36, 1), (57, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component17.SelectedLeafB1_6_0.selectedHasNoCommonZero

end Krenn.Component17.SelectedLeafB1_6_0
