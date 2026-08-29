import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase304.LeafB4

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "9df7535ced4ee49f3cf3ce90fe207276ef6c7009750931ff6582e58d9b1dfa2a"
def sourceSystemSemanticSHA256 : String := "c4c8189f28fed0b240cfe2fda670a83ce500bdfb5d132efb85f1c323e55b9ad7"
def certificateSHA256 : String := "c3c7ff92eb8f880be468295847dceb174374a04a1528939960321766590c0278"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 19 → Fin 678 := ![
  4,
  16,
  18,
  26,
  27,
  30,
  405,
  411,
  421,
  422,
  426,
  433,
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
def selectedEquations : Fin 19 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(12, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1), (62, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(4, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(4, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(10, 1), (61, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (48, 1), (53, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(48, 1), (53, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (32, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (53, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1)] }, { coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (39, 1), (56, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (39, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (39, 1), (56, 1), (64, 1), (70, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (56, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (33, 1), (39, 1), (56, 1), (58, 1), (70, 1)] }, { coefficient := -1, powers := [(10, 1), (33, 1), (39, 1), (56, 1), (70, 1)] }]
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
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase304.LeafB4.selectedHasNoCommonZero

end Krenn.X5ResidualCase304.LeafB4
