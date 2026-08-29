import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component1.SelectedLeafB7_0

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "029ecce0d5521dc74a5b727caf4f78c5823f09396b08c78524013d9ebfbd601c"
def certificateSHA256 : String := "6c4f39870c77901d33ed92754967b50c7e819a0101a3f76c9e09994cb6dafd64"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 34 → Fin 588 := ![
  0,
  3,
  8,
  25,
  32,
  37,
  39,
  44,
  225,
  258,
  260,
  261,
  354,
  364,
  366,
  370,
  384,
  385,
  391,
  399,
  401,
  427,
  470,
  507,
  530,
  545,
  563,
  578,
  580,
  581,
  583,
  584,
  586,
  587
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 34 → SparsePoly (Fin 60) := ![
  [{ coefficient := 1, powers := [(1, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(1, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(1, 1), (47, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (56, 1)] }, { coefficient := 1, powers := [(14, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(14, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (41, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(22, 1), (49, 1)] }, { coefficient := 1, powers := [(22, 1), (52, 1)] }, { coefficient := 1, powers := [(27, 1), (41, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(2, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (44, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (49, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(4, 1), (27, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (22, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(11, 1), (22, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (27, 1), (44, 1)] }, { coefficient := 1, powers := [(11, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(16, 1), (22, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (47, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (47, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(14, 1), (23, 1), (53, 1)] }, { coefficient := 1, powers := [(14, 1), (30, 1), (47, 1)] }, { coefficient := 1, powers := [(14, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1), (58, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 34 → SparsePoly (Fin 60) := ![
  [{ coefficient := -1, powers := [(2, 1), (47, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (58, 1)] }, { coefficient := -1, powers := [(19, 1), (23, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (30, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (24, 1), (33, 1), (35, 1), (38, 1), (44, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (33, 1), (35, 1), (38, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (33, 1), (45, 1), (49, 1), (59, 1)] }, { coefficient := 1, powers := [(1, 1), (5, 1), (33, 1), (45, 1), (52, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (35, 1), (45, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (7, 1), (33, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (33, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (5, 1), (25, 1), (33, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (25, 1), (33, 1), (44, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (33, 1), (44, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(4, 1), (5, 1), (33, 1), (35, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (11, 1), (24, 1), (33, 1), (35, 1), (38, 1), (45, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (18, 1), (33, 1), (49, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (18, 1), (33, 1), (52, 1), (59, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (18, 1), (33, 1), (35, 1), (59, 1)] }],
  [{ coefficient := -2, powers := [(0, 1), (5, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (24, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (44, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := -1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(14, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (5, 1), (27, 1), (33, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (27, 1), (33, 1), (44, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1), (33, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (24, 1), (33, 1), (35, 1), (38, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (33, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (25, 1), (33, 1), (35, 1), (38, 1), (45, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (30, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (16, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (5, 1), (33, 1), (53, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (33, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (5, 1), (33, 1), (38, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (5, 1), (33, 1), (35, 1), (49, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (5, 1), (27, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (16, 1), (27, 1), (33, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (16, 1), (33, 1), (35, 1), (38, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (30, 1), (56, 1)] }, { coefficient := -1, powers := [(1, 1), (2, 1), (5, 1), (33, 1), (52, 1), (53, 1), (59, 1)] }, { coefficient := -1, powers := [(1, 1), (5, 1), (18, 1), (29, 1), (33, 1), (53, 1), (59, 1)] }, { coefficient := 1, powers := [(5, 1), (7, 1), (33, 1), (35, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (11, 1), (24, 1), (25, 1), (33, 1), (35, 1), (38, 1), (45, 1)] }, { coefficient := -1, powers := [(5, 1), (17, 1), (25, 1), (33, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (2, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1)] }]
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
    (values : Fin 60 → R) :
    ¬ ∀ index : Fin 34,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component1.SelectedLeafB7_0.selectedHasNoCommonZero

end Krenn.Component1.SelectedLeafB7_0
