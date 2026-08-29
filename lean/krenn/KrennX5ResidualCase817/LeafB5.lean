import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase817.LeafB5

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "49ab65ac3f71a7ecd4830a09215c10a2297a330de97f2637584861ada87a903f"
def sourceSystemSemanticSHA256 : String := "e483726f83136cb9c75d65a1c44d0359409ffeab4a350db921b6f478558c18e1"
def certificateSHA256 : String := "bc39a71ede2200593b5f6c34f0c9120d91d0b050e7aea1ea888984893f48d0a2"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 18 → Fin 678 := ![
  11,
  17,
  20,
  28,
  45,
  387,
  404,
  412,
  422,
  423,
  427,
  434,
  438,
  632,
  671,
  673,
  675,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 18 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (38, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1), (71, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 18 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(34, 1), (39, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (47, 1), (53, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (38, 1), (39, 1), (59, 1), (70, 1)] }, { coefficient := -1, powers := [(47, 1), (53, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (62, 1), (71, 1)] }, { coefficient := -1, powers := [(12, 1), (62, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (62, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (53, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(53, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(62, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(28, 1), (34, 1), (38, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }]
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
    ¬ ∀ index : Fin 18,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase817.LeafB5.selectedHasNoCommonZero

end Krenn.X5ResidualCase817.LeafB5
