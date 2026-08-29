import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case311Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "99e7f2f65cb21c76e510939c6d6c658fc54c5e391dec00c4a6663390db32e37c"
def sourceSystemSemanticSHA256 : String := "795d5baa985c48189f64e7e86091278049a636d36bc8e2a17bfd679576139aee"
def certificateSHA256 : String := "cede9603f4c6593e0948d9970b1af0d776fe94d11dac17eab90190fe305c36b1"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 31 → Fin 675 := ![
  0,
  2,
  27,
  28,
  30,
  32,
  34,
  36,
  37,
  39,
  43,
  44,
  46,
  414,
  415,
  420,
  421,
  422,
  424,
  425,
  469,
  533,
  587,
  623,
  632,
  659,
  660,
  667,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 31 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (61, 1)] }, { coefficient := 1, powers := [(27, 1), (52, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(25, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(58, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (41, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(10, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(27, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 31 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(16, 1), (33, 1), (39, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(17, 1), (33, 1), (38, 1), (47, 1), (55, 1)] }, { coefficient := -1, powers := [(17, 1), (33, 1), (41, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (39, 1), (44, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (47, 1)] }, { coefficient := 1, powers := [(0, 1), (10, 1), (16, 1), (47, 1)] }, { coefficient := 1, powers := [(2, 1), (8, 1), (16, 1), (47, 1)] }, { coefficient := -1, powers := [(2, 1), (10, 1), (16, 2), (47, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1), (19, 1), (42, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (44, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (19, 1), (42, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (17, 1), (33, 1), (36, 1), (41, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (19, 1), (27, 1), (42, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (25, 1), (33, 1), (36, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (16, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (25, 1), (33, 1), (36, 1), (37, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (16, 1), (17, 1), (33, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1), (33, 1), (41, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (33, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (33, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (36, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (27, 1), (42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (16, 1), (27, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 2), (27, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 1), (24, 1)] }, { coefficient := 1, powers := [(16, 1), (17, 1), (28, 1), (33, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (33, 1), (41, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (33, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(25, 1), (33, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (16, 1), (33, 1), (36, 1), (41, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(9, 1), (33, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (47, 1)] }, { coefficient := 1, powers := [(2, 1), (16, 2), (47, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (27, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (25, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (25, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (28, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (28, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (17, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(16, 1), (19, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }, { coefficient := -1, powers := [(10, 1), (16, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (17, 1), (33, 1), (36, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (41, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (33, 1), (36, 1), (41, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (19, 1), (42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (33, 1), (36, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }, { coefficient := -1, powers := [(2, 1), (16, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(32, 1), (41, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 31,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case311Selected.selectedHasNoCommonZero

end Krenn.X5Case311Selected
