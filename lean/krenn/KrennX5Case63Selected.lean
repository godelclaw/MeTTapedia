import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case63Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "c1b629be977333731a4e39b5edc06184c76e505c555052be760d3cf84f2549e6"
def sourceSystemSemanticSHA256 : String := "81818985b2bbab5670e9c54cb695d08bb7cdcfe00fda590ce7a88f543d3ede79"
def certificateSHA256 : String := "a13e81d70214468956e9f49dcbf6fc8d04b221f8dda561759901d133a17872c3"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 20 → Fin 675 := ![
  0,
  2,
  12,
  33,
  46,
  313,
  399,
  414,
  418,
  419,
  420,
  421,
  422,
  424,
  434,
  660,
  669,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (66, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (32, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (38, 1), (55, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (32, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (38, 1), (55, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (32, 1), (33, 1), (36, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (33, 1), (38, 1), (42, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (32, 1), (41, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (38, 1), (56, 1), (59, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (38, 1), (56, 1), (59, 1)] }, { coefficient := -1, powers := [(32, 1), (33, 1), (36, 1), (38, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (17, 1), (32, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (38, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (32, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (32, 1), (38, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (24, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (41, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (38, 1), (55, 1), (59, 1)] }, { coefficient := 1, powers := [(32, 1), (33, 1), (36, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (25, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (17, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case63Selected.selectedHasNoCommonZero

end Krenn.X5Case63Selected
