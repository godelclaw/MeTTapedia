import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case782Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "06a755ed248771956ea5ab472d922e3310c4396dcecb8fce699b0fe57e497e7b"
def sourceSystemSemanticSHA256 : String := "c65b806c15afa523b885b8356ef0c4fa72c607dcb73e7de40df5dd335ab1f9e4"
def certificateSHA256 : String := "5fd710fec38fc80d083eaf06d60abeb36c8fc5a0e67a88e562264c23285947b5"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 19 → Fin 675 := ![
  0,
  1,
  2,
  3,
  34,
  35,
  404,
  421,
  422,
  423,
  425,
  426,
  433,
  482,
  506,
  642,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (21, 1), (25, 1), (47, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (21, 1), (25, 1), (32, 1), (41, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (21, 1), (25, 1), (44, 1), (47, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := -1, powers := [(44, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (39, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (35, 1), (39, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (38, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (33, 1), (39, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (44, 1), (52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (13, 1), (25, 1), (47, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (13, 1), (25, 1), (32, 1), (41, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (13, 1), (25, 1), (44, 1), (47, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(8, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }, { coefficient := -1, powers := [(44, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (35, 1), (36, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (33, 1), (36, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (44, 1), (52, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (19, 1), (47, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (41, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(19, 1), (44, 1), (47, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (38, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (11, 1), (47, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (41, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (44, 1), (47, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (35, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (32, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (44, 1), (53, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (25, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (25, 1), (35, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (24, 1), (25, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (32, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (44, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(28, 1), (44, 1), (52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (17, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (32, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (44, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(20, 1), (44, 1), (52, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (9, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (12, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (32, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (44, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(12, 1), (44, 1), (52, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(44, 1), (53, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1), (53, 1), (67, 1)] }, { coefficient := -1, powers := [(32, 1), (41, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(44, 1), (47, 1), (53, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (25, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (32, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (44, 1), (53, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(3, 1), (44, 1), (52, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1), (67, 1)] }]
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
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case782Selected.selectedHasNoCommonZero

end Krenn.X5Case782Selected
