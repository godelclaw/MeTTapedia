import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase385.LeafB4

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "18ff3849c023b0171f30fa39b16a8dc57420603ebbe28f8414b1a570279e3c0a"
def sourceSystemSemanticSHA256 : String := "f953ea6aa1edb2678bb65b14579e570aa3a8e9784a01463be8f4f3f205c11bc6"
def certificateSHA256 : String := "1c345c43480d01613e9c19f71af89275a22919a96a3e535ebdbd0cb5bbbaaacb"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 22 → Fin 678 := ![
  17,
  22,
  30,
  34,
  42,
  414,
  416,
  422,
  423,
  426,
  427,
  496,
  500,
  623,
  659,
  660,
  671,
  672,
  673,
  675,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 22 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(25, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(22, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 22 → SparsePoly (Fin 71) := ![
  [{ coefficient := -1, powers := [(16, 1), (33, 1), (36, 1), (39, 1), (41, 1), (58, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1), (33, 1), (36, 1), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (41, 1), (46, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (16, 1), (33, 1), (41, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (16, 1), (17, 1), (33, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1), (33, 1), (41, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (16, 1), (33, 1), (36, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (46, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (46, 1), (70, 1)] }, { coefficient := 1, powers := [(35, 1), (64, 1), (70, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1), (70, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (41, 1), (46, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (25, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (32, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (17, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (32, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (16, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (32, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (33, 1), (41, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (17, 1), (33, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (33, 1), (36, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (25, 1), (33, 1), (36, 1), (39, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (22, 1), (33, 1), (41, 1), (46, 1), (56, 1)] }, { coefficient := -2, powers := [(16, 1), (35, 1), (64, 1), (70, 1)] }, { coefficient := -1, powers := [(16, 1), (38, 1), (58, 1), (70, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (35, 1), (64, 1), (70, 1)] }, { coefficient := -1, powers := [(8, 1), (38, 1), (58, 1), (70, 1)] }, { coefficient := -1, powers := [(8, 1), (44, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (58, 1), (70, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 22,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase385.LeafB4.selectedHasNoCommonZero

end Krenn.X5ResidualCase385.LeafB4
