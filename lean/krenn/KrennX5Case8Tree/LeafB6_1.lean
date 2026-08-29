import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case8Tree.LeafB6_1

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "3330e1f491b2a9643bcede898c34f8f2a99f3f612332d37ca8f51afaaa7ebc73"
def sourceSystemSemanticSHA256 : String := "720ded034800cf04ae46f5c07818b9d654bf2bf96b99d8a2c9b1ec4bc6cafc0e"
def certificateSHA256 : String := "6e471b1c4c66837585ea1b21953934638e7b16c843909bab91ed4a903ad8a2f1"
def sourceEquationCount : Nat := 681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 21 → Fin 681 := ![
  0,
  1,
  12,
  26,
  30,
  37,
  311,
  415,
  416,
  421,
  422,
  423,
  425,
  432,
  572,
  671,
  672,
  673,
  678,
  679,
  680
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(36, 1), (67, 1)] }, { coefficient := 1, powers := [(39, 1), (67, 1)] }, { coefficient := 1, powers := [(53, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (72, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (59, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (39, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (42, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (62, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (41, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (39, 1), (41, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (41, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(32, 1), (33, 1), (36, 1), (41, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (39, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (24, 1), (42, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (39, 1), (58, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (42, 1), (58, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (68, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (32, 1), (35, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (32, 1), (35, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (35, 1), (39, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (35, 1), (42, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(19, 1), (68, 1)] }, { coefficient := -1, powers := [(27, 1), (47, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(39, 1), (68, 1), (72, 1)] }, { coefficient := -1, powers := [(42, 1), (65, 1), (72, 1)] }, { coefficient := -1, powers := [(59, 1), (62, 1), (72, 1)] }, { coefficient := 1, powers := [(62, 1), (65, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (26, 1), (39, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (26, 1), (42, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(26, 1), (32, 1), (35, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(26, 1), (32, 1), (35, 1), (42, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (18, 1), (39, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (18, 1), (42, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (39, 1), (41, 1), (68, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (41, 1), (42, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (8, 1), (59, 1), (61, 1), (62, 1), (72, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (36, 1), (61, 1), (62, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (62, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (42, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (39, 2), (68, 1)] }, { coefficient := 1, powers := [(18, 1), (32, 1), (39, 1), (42, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (25, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(8, 1), (11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (39, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (18, 1), (42, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (35, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (35, 1), (42, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (59, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (39, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (42, 1), (64, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (62, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (38, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (38, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (38, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (39, 2), (44, 1), (68, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (39, 1), (42, 1), (44, 1), (65, 1)] }, { coefficient := 1, powers := [(32, 1), (33, 1), (36, 1), (38, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (47, 1)] }, { coefficient := -1, powers := [(19, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (44, 1), (59, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (36, 1), (44, 1), (61, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (59, 1), (62, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (1 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
      SparsePoly.toPoly, SparseTerm.toPoly]
  ring

theorem selectedHasNoCommonZero {R : Type*}
    [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 73 → R) :
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case8Tree.LeafB6_1.selectedHasNoCommonZero

end Krenn.X5Case8Tree.LeafB6_1
