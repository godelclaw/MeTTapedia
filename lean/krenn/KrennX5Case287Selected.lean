import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case287Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "c7db743961ce34a3b67d9c06c444c56f0914899b9518cd24de86bf7b0937b1e6"
def sourceSystemSemanticSHA256 : String := "933347bc88f08f2c56f6ee1a1c25c06757ca526f111f9a3992d886651980dfed"
def certificateSHA256 : String := "9d127a5802e06b7d9bddd685e5bf489d4fa17d0d9c5d59567b152a2afae95a11"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 20 → Fin 675 := ![
  0,
  1,
  16,
  26,
  30,
  32,
  33,
  414,
  415,
  420,
  421,
  422,
  424,
  425,
  426,
  624,
  659,
  661,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (38, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (38, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (38, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (36, 1), (38, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (38, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (38, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (33, 1), (38, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (35, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (35, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (35, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (35, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (35, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (35, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (33, 1), (35, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (47, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (47, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (42, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (44, 1), (52, 1), (68, 1)] }, { coefficient := -1, powers := [(28, 1), (44, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (17, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (28, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (17, 1), (33, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (9, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (28, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(0, 1), (9, 1), (33, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (39, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (36, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (47, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (47, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (47, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (36, 1), (47, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (39, 1), (47, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (47, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (36, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (42, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(32, 1), (39, 1), (45, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (52, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (48, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }],
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

#print axioms Krenn.X5Case287Selected.selectedHasNoCommonZero

end Krenn.X5Case287Selected
