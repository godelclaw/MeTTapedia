import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case308Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "04fc96c5510e8fffa65e3b051ee294d0f5c924e41503db338ec441a1f280a72d"
def sourceSystemSemanticSHA256 : String := "930e306893937005ce3c43a245bf8f80fe5bd8c0bfae4cb3a402f64f1ccf0a07"
def certificateSHA256 : String := "ea1683035601289867014dc8ca75a231d5a770080f1a98b5ee5720d0160d2b30"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 17 → Fin 675 := ![
  0,
  1,
  2,
  3,
  30,
  31,
  421,
  422,
  423,
  425,
  426,
  435,
  467,
  642,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(0, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1)] }, { coefficient := -1, powers := [(44, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (55, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (42, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (38, 1), (55, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (44, 1), (55, 1), (64, 1), (68, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (35, 1), (42, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (41, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (33, 1), (38, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (44, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }, { coefficient := -1, powers := [(44, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (55, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(3, 1), (44, 1), (55, 1), (59, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (35, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (36, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (33, 1), (36, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (44, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (27, 1), (47, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (41, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (32, 1), (38, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(27, 1), (44, 1), (47, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (10, 1), (47, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(10, 1), (32, 1), (38, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (44, 1), (47, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (35, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (28, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (25, 1), (35, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (25, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(28, 1), (44, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (17, 1), (35, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (17, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(19, 1), (44, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (11, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (16, 1), (35, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (44, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(44, 1), (56, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(44, 1), (47, 1), (56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (41, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1), (64, 1)] }]
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
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case308Selected.selectedHasNoCommonZero

end Krenn.X5Case308Selected
