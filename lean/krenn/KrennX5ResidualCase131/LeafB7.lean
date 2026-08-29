import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase131.LeafB7

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "13793906a39939e7bfbe5363f108f266dab0b64ff1891afe3da3b9229154b3d7"
def sourceSystemSemanticSHA256 : String := "e14cf13b7cb325c91b56597f084e97163a49675e7aedeadee55d253eb28d879a"
def certificateSHA256 : String := "cf44129e01679c4a03f05fef43c29c1fa67958191520550d59c1c0544d3485c2"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 5 → Fin 678 := ![
  49,
  307,
  324,
  675,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 5 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(48, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (61, 1)] }, { coefficient := 1, powers := [(59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(52, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1), (72, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 5 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(1, 1), (61, 1), (70, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (61, 1), (72, 2)] }],
  [{ coefficient := 1, powers := [(72, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (48, 1), (61, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (48, 1), (61, 1), (72, 1)] }, { coefficient := 1, powers := [(1, 1), (59, 1), (61, 1), (72, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 5,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase131.LeafB7.selectedHasNoCommonZero

end Krenn.X5ResidualCase131.LeafB7
