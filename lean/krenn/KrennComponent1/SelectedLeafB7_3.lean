import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component1.SelectedLeafB7_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "f2ceb4d2ffcdd64a641a899c6a0dab6fa9c1ad1f077dc9d9da5359b96e2f7aec"
def certificateSHA256 : String := "115ed66830eecd16e06e5b352f78f9e8c02f590d680691192587c592696179a9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 588 := ![
  0,
  1,
  25,
  32,
  37,
  40,
  219,
  225,
  226,
  260,
  264,
  276,
  354,
  382,
  384,
  385,
  386,
  424,
  507,
  546,
  550,
  564,
  581,
  582,
  583,
  584,
  586,
  587
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 62) := ![
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1)] }, { coefficient := 1, powers := [(19, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (36, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (49, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (53, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (45, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1), (60, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(42, 1), (61, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 62) := ![
  [{ coefficient := 2, powers := [(2, 1), (47, 1), (58, 1)] }, { coefficient := -2, powers := [(5, 1), (36, 1), (37, 1), (55, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (36, 1), (58, 1)] }, { coefficient := -2, powers := [(19, 1), (23, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (24, 1), (39, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (39, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (33, 1), (45, 1), (59, 1)] }, { coefficient := -2, powers := [(19, 1), (29, 1), (42, 1), (59, 1), (60, 1)] }, { coefficient := 2, powers := [(42, 1), (45, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (33, 1), (49, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (33, 1), (52, 1), (57, 1)] }, { coefficient := 2, powers := [(14, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (39, 1), (49, 1), (55, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (3, 1), (39, 1), (55, 1), (56, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (49, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (56, 1), (57, 1), (61, 1)] }, { coefficient := -2, powers := [(8, 1), (33, 1), (47, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (33, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (33, 1), (53, 1), (59, 1)] }, { coefficient := 2, powers := [(19, 1), (30, 1), (42, 1), (59, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (18, 1), (33, 1), (59, 1)] }, { coefficient := -2, powers := [(18, 1), (42, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (20, 1), (39, 1), (56, 1), (57, 1), (61, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(23, 1), (53, 1)] }],
  [{ coefficient := -2, powers := [(30, 1), (42, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(19, 1)] }],
  [{ coefficient := 2, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (55, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(23, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 2, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1), (56, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (33, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (39, 1), (42, 1), (52, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := -2, powers := [(3, 1), (5, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := -2, powers := [(8, 1), (33, 1), (47, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (47, 1), (50, 1)] }, { coefficient := 2, powers := [(5, 1), (36, 1), (37, 1), (50, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 2, powers := [(19, 1), (23, 1), (50, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (5, 1), (33, 1), (49, 1), (53, 1)] }, { coefficient := -2, powers := [(19, 1), (30, 1), (42, 1), (49, 1), (60, 1)] }],
  [{ coefficient := -2, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := -2, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (3, 1), (24, 1), (39, 1), (49, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (3, 1), (24, 1), (39, 1), (55, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (39, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (20, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(2, 1), (24, 1), (39, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (24, 1), (33, 1), (47, 1), (57, 1)] }]
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
    (values : Fin 62 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component1.SelectedLeafB7_3.selectedHasNoCommonZero

end Krenn.Component1.SelectedLeafB7_3
