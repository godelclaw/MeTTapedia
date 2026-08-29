import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase861.LeafB7

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "1f1fd312da7e9d4f0d43c71f0a854c44f345b2fd417d6e73e66f2039e6f3a413"
def sourceSystemSemanticSHA256 : String := "9f511c814eea54d7e75d4be72e3256575b0d5fc07bf330764bdf35cbf5145f09"
def certificateSHA256 : String := "ef8d3842a1b435363ec75566f793f5011fbda8093f6274304719b1e696b48b25"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 21 → Fin 678 := ![
  2,
  5,
  10,
  13,
  18,
  21,
  414,
  415,
  417,
  418,
  422,
  423,
  426,
  660,
  663,
  671,
  672,
  673,
  675,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(9, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1), (71, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1), (72, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 73) := ![
  [{ coefficient := -1, powers := [(3, 1), (39, 1), (68, 1), (72, 1)] }, { coefficient := -1, powers := [(3, 1), (42, 1), (65, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1), (72, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (36, 1), (68, 1), (71, 1)] }, { coefficient := -1, powers := [(3, 1), (42, 1), (59, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1), (71, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (36, 1), (65, 1), (70, 1)] }, { coefficient := -1, powers := [(3, 1), (39, 1), (59, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1), (70, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (33, 1), (36, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (39, 1), (47, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (33, 1), (42, 1), (47, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(32, 1), (39, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(32, 1), (42, 1), (45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(28, 1), (39, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (17, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (42, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (9, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(12, 1), (42, 1), (65, 1)] }]
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

#print axioms Krenn.X5ResidualCase861.LeafB7.selectedHasNoCommonZero

end Krenn.X5ResidualCase861.LeafB7
