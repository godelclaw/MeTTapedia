import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case282Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "450c2a94573e7f39189a0cd619166b448c90980837fda3d9fa9fd6b63134d393"
def sourceSystemSemanticSHA256 : String := "87d595b31aace750dc227fa5dbb8247cafa4cf103edede587de476eb8bab4197"
def certificateSHA256 : String := "7feb5e5fa98a61fccfee3129da27ac88deaeba1315a06a0a7216f9f2afda35d2"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 20 → Fin 675 := ![
  0,
  1,
  2,
  3,
  26,
  30,
  32,
  33,
  414,
  421,
  422,
  423,
  425,
  426,
  427,
  457,
  624,
  659,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (41, 1), (65, 1)] }, { coefficient := 1, powers := [(17, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (38, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (36, 1), (38, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (38, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (38, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (33, 1), (38, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (35, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (35, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (35, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (35, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (33, 1), (35, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (28, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (33, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (28, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (33, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (46, 1), (52, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (28, 1), (46, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (17, 1), (33, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (44, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (44, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(17, 1), (33, 1), (42, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (39, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (9, 1), (46, 1), (52, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (28, 1), (46, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (9, 1), (33, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (44, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (28, 1), (44, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(9, 1), (33, 1), (42, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (46, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (36, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (39, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (46, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (42, 1), (46, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (46, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (46, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (42, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (44, 1), (52, 1), (68, 1)] }, { coefficient := -1, powers := [(28, 1), (44, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (44, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (52, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case282Selected.selectedHasNoCommonZero

end Krenn.X5Case282Selected
