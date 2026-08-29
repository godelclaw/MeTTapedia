import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case64Tree.LeafB1_4

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "8d8edf4e526716f8aa2d55a791d7ecf91dce5d67af815201ce8ac3a04a3a34d3"
def sourceSystemSemanticSHA256 : String := "91fb45261610227bfb3ce01945888019022038fe85b4209bfee033bd23cbc0cf"
def certificateSHA256 : String := "623917ad29e20b94865a5226fffdaa6f690439d9eac0ce7e129aa2f721074124"
def sourceEquationCount : Nat := 681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 25 → Fin 681 := ![
  0,
  16,
  26,
  34,
  43,
  46,
  397,
  420,
  421,
  422,
  423,
  425,
  427,
  518,
  554,
  619,
  620,
  638,
  665,
  672,
  673,
  675,
  676,
  678,
  679
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (39, 1), (67, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (64, 1)] }, { coefficient := 1, powers := [(42, 1), (64, 1)] }, { coefficient := 1, powers := [(56, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (71, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 72) := ![
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (33, 1), (36, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (42, 1), (53, 1), (58, 1)] }, { coefficient := 1, powers := [(14, 1), (24, 1), (25, 1), (33, 1), (35, 1), (47, 1), (53, 1)] }, { coefficient := -1, powers := [(25, 1), (32, 1), (33, 1), (35, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (33, 1), (35, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (44, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (24, 1), (25, 1), (33, 1), (35, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (33, 1), (38, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (17, 1), (40, 1), (68, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (17, 1), (42, 1), (71, 1)] }, { coefficient := 1, powers := [(11, 1), (62, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (42, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (33, 1), (36, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }, { coefficient := -1, powers := [(33, 1), (38, 1), (47, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (25, 1), (33, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (25, 1), (33, 1), (36, 1), (53, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (33, 1), (36, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (25, 1), (33, 1), (35, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (33, 1), (36, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (40, 1), (68, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (39, 1), (68, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (33, 1), (35, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (33, 1), (36, 1), (53, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(25, 1), (33, 1), (36, 1), (53, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1), (55, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (65, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (33, 1), (35, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(17, 1), (32, 1), (33, 1), (36, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(17, 1), (33, 1), (36, 1)] }, { coefficient := -1, powers := [(24, 1), (33, 1), (35, 1), (53, 1), (64, 1)] }, { coefficient := -1, powers := [(32, 1), (33, 1), (38, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }]
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
    (values : Fin 72 → R) :
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case64Tree.LeafB1_4.selectedHasNoCommonZero

end Krenn.X5Case64Tree.LeafB1_4
