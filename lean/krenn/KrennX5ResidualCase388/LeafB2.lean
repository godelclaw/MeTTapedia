import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase388.LeafB2

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "c8f4c1838dca583d9170b58fdc70791057f59033e21fb1ef801ddd393e155c9a"
def sourceSystemSemanticSHA256 : String := "2729aef4ee6ad1e0fcb7883a8fb9a05a9a24054b1a95a67902a9ba729eccee24"
def certificateSHA256 : String := "8ad7c488f514c37e89b17f3791a91238b7cf85d3a3c6dad9f2feb60228f3f92c"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 20 → Fin 678 := ![
  4,
  8,
  10,
  26,
  27,
  34,
  397,
  411,
  421,
  422,
  426,
  435,
  517,
  633,
  657,
  671,
  673,
  675,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 20 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(12, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1), (62, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(36, 1), (64, 1)] }, { coefficient := 1, powers := [(36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (61, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (36, 1), (50, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (48, 1), (56, 1), (64, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (48, 1), (56, 1), (64, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (28, 1), (32, 1), (36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (20, 1), (32, 1), (36, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (56, 1), (64, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (25, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (28, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (17, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (20, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (9, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (56, 1), (64, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (33, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (32, 1), (36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(70, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (67, 1), (70, 1)] }, { coefficient := -1, powers := [(70, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (33, 1), (39, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (14, 1), (33, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(7, 1), (58, 1), (70, 1)] }, { coefficient := -1, powers := [(13, 1), (70, 1)] }]
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
    ¬ ∀ index : Fin 20,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase388.LeafB2.selectedHasNoCommonZero

end Krenn.X5ResidualCase388.LeafB2
