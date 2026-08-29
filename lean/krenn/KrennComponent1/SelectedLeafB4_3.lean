import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component1.SelectedLeafB4_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9cad2a29d9b2d247fd230cdec1a72eb3b592b87f5151cec4f41958f24528c330"
def certificateSHA256 : String := "a03f83b5f177bda4b989e12786a295e710b1b10490713fb6bbcb25e78cafe3af"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 31 → Fin 588 := ![
  1,
  25,
  35,
  37,
  40,
  48,
  84,
  218,
  219,
  220,
  225,
  229,
  265,
  276,
  292,
  354,
  382,
  384,
  385,
  448,
  493,
  503,
  507,
  545,
  550,
  564,
  581,
  582,
  584,
  586,
  587
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(3, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(28, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (24, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 60) := ![
  [{ coefficient := -2, powers := [(5, 1), (30, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (44, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (6, 1), (33, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (33, 1), (57, 1)] }, { coefficient := 2, powers := [(14, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (33, 1), (44, 1), (53, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (33, 1), (53, 1), (55, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (41, 1), (53, 1), (57, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (44, 1), (53, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(5, 1), (28, 1), (45, 1), (50, 1), (55, 1), (57, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (41, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (53, 1), (57, 1), (59, 1)] }, { coefficient := -2, powers := [(8, 1), (33, 1), (47, 1), (57, 1), (59, 1)] }, { coefficient := 2, powers := [(19, 1), (28, 1), (46, 1), (49, 1), (50, 1), (59, 1)] }, { coefficient := 2, powers := [(19, 1), (30, 1), (42, 1), (49, 2), (58, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (18, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (28, 1), (50, 1), (55, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (33, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(19, 1), (23, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(42, 1), (53, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (44, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (53, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (23, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (50, 1), (55, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(24, 1), (28, 1), (46, 1), (50, 1)] }, { coefficient := -2, powers := [(24, 1), (30, 1), (42, 1), (49, 1), (58, 1)] }, { coefficient := -2, powers := [(30, 1), (42, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(19, 1)] }],
  [{ coefficient := 2, powers := [(14, 1)] }],
  [{ coefficient := -2, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(28, 1), (46, 1), (50, 1)] }, { coefficient := 2, powers := [(30, 1), (42, 1), (49, 1), (58, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(50, 1)] }],
  [{ coefficient := 2, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (20, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(42, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -1, powers := [(5, 1), (20, 1), (33, 1), (44, 1), (53, 1)] }, { coefficient := -2, powers := [(5, 1), (28, 1), (45, 1), (50, 1), (55, 1), (58, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (37, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := -2, powers := [(8, 1), (33, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(6, 1), (47, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(39, 1), (56, 1)] }, { coefficient := -2, powers := [(41, 1), (42, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(42, 1), (49, 1), (53, 1), (58, 1)] }, { coefficient := 2, powers := [(42, 1), (53, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (6, 1), (36, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (5, 1), (24, 1), (33, 1), (44, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (24, 1), (33, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (24, 1), (33, 1), (41, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (24, 1), (33, 1), (44, 1), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (24, 1), (28, 1), (45, 1), (50, 1), (55, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (33, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (24, 1), (33, 1), (47, 1), (57, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (28, 1), (46, 1), (49, 1), (50, 1)] }, { coefficient := -2, powers := [(19, 1), (24, 1), (30, 1), (42, 1), (49, 2), (58, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component1.SelectedLeafB4_3.selectedHasNoCommonZero

end Krenn.Component1.SelectedLeafB4_3
