import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case573Tree.LeafB2_5

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "3891c76a663fea905abc279fc7bb8ca31627dc94db4860d67110676fbec178d7"
def sourceSystemSemanticSHA256 : String := "deae362e99b75caa48f6c80a8599cccb91d4b3c9ef923527be6d9440342431b4"
def certificateSHA256 : String := "68c59051ee69c43bab51c86be39b8e4b658daae6ff7702d63e6dac1f9c1daec4"
def sourceEquationCount : Nat := 681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 28 → Fin 681 := ![
  0,
  9,
  18,
  21,
  33,
  46,
  413,
  414,
  415,
  417,
  421,
  422,
  423,
  425,
  430,
  537,
  622,
  643,
  660,
  661,
  667,
  670,
  672,
  673,
  675,
  678,
  679,
  680
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(2, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(2, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(19, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (71, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (72, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 73) := ![
  [{ coefficient := -1, powers := [(3, 1), (14, 1), (32, 1), (35, 1), (61, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (35, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (11, 1), (32, 1), (35, 1), (61, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (32, 1), (35, 1), (59, 1), (61, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (35, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(44, 1), (55, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (41, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (34, 1), (41, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (19, 1), (34, 1), (41, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (32, 1), (35, 1), (53, 1), (61, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (8, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (34, 1), (35, 1), (47, 1), (61, 1), (68, 1)] }, { coefficient := -1, powers := [(33, 1), (35, 1), (47, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (32, 1), (35, 1), (61, 1), (68, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (27, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (19, 1)] }, { coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(22, 1), (28, 1), (32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1), (32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (35, 1), (61, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (8, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (34, 1), (35, 1), (61, 1), (68, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := -1, powers := [(55, 1), (57, 1), (64, 1), (72, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (32, 1), (35, 1), (48, 1), (53, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (22, 1), (32, 1), (35, 1), (61, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (35, 1), (61, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (32, 1), (35, 1), (61, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (32, 1), (35, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (32, 1), (35, 1), (48, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (38, 1), (55, 1)] }]
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
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case573Tree.LeafB2_5.selectedHasNoCommonZero

end Krenn.X5Case573Tree.LeafB2_5
