import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase817.LeafB1

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "4159c6d1fd02e3f42240cb47a96bce7db39bfa52ac549b420028bb3cdc03b3fe"
def sourceSystemSemanticSHA256 : String := "9196855eafe9011f63585fd61b919d94a1b99a72f5f218b4609a6c61fa313402"
def certificateSHA256 : String := "68c296eba6dcf68d588b3cc3a399f76a88b1312f2c59b5112c96862153a847ee"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 19 → Fin 678 := ![
  11,
  19,
  28,
  32,
  39,
  45,
  387,
  412,
  413,
  422,
  423,
  427,
  438,
  605,
  632,
  634,
  671,
  673,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(19, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(14, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }, { coefficient := 1, powers := [(41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (38, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (41, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(12, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(12, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(12, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(34, 1), (39, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (42, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (34, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(14, 1), (28, 1), (34, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (9, 1), (62, 1), (70, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (28, 1), (34, 1), (39, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (34, 1), (41, 1), (42, 1), (70, 1)] }, { coefficient := 1, powers := [(9, 1), (28, 1), (34, 1), (39, 1), (41, 1), (70, 1)] }, { coefficient := -1, powers := [(12, 1), (62, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (62, 1), (70, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (34, 1), (39, 1)] }, { coefficient := 1, powers := [(20, 1), (34, 1), (41, 1), (42, 1), (70, 1)] }, { coefficient := -1, powers := [(28, 1), (34, 1), (39, 1), (41, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1)] }, { coefficient := 1, powers := [(12, 1)] }],
  [{ coefficient := 1, powers := [(62, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (34, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(20, 1), (34, 1), (41, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (34, 1), (39, 1), (41, 1), (59, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }]
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

#print axioms Krenn.X5ResidualCase817.LeafB1.selectedHasNoCommonZero

end Krenn.X5ResidualCase817.LeafB1
