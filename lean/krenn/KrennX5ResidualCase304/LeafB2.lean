import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase304.LeafB2

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "db3fc9f24033fd173ae80f2c8823c460a2de52074167236e6810755517fa351d"
def sourceSystemSemanticSHA256 : String := "b188e5ed56586cf349ea92b09ade5abb1854abecbb6bbeb3e453d8af4ac91b89"
def certificateSHA256 : String := "fdc83a5398e7cbda681349d8c5ae712fe5c244e0e681c734e70b0cc2c2c4939d"
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
  482,
  633,
  651,
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
  [{ coefficient := 1, powers := [(19, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1), (62, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (55, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(36, 1), (64, 1)] }, { coefficient := 1, powers := [(36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (61, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 20 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(4, 1), (32, 1), (36, 1), (50, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (4, 1), (48, 1), (56, 1), (64, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (48, 1), (56, 1), (64, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (27, 1), (32, 1), (36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (19, 1), (32, 1), (36, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (4, 1), (56, 1), (64, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (4, 1), (25, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (27, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (4, 1), (17, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (19, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (4, 1), (9, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (11, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (56, 1), (64, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (32, 1), (36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(70, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (4, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (67, 1), (70, 1)] }, { coefficient := -1, powers := [(70, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (33, 1), (39, 1), (56, 1), (64, 1)] }, { coefficient := -1, powers := [(4, 1), (64, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (11, 1), (33, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(4, 1), (58, 1), (70, 1)] }, { coefficient := -1, powers := [(10, 1), (70, 1)] }]
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

#print axioms Krenn.X5ResidualCase304.LeafB2.selectedHasNoCommonZero

end Krenn.X5ResidualCase304.LeafB2
