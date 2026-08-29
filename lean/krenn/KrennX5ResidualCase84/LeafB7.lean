import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase84.LeafB7

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "77dabb8876c7ecf418edc0da459bd20e86d10e95b49101218faec1258cde6d95"
def sourceSystemSemanticSHA256 : String := "f967aa7aa5b4a031b2937174b5a004a2a07ec20b223cd2b6fc67f3361f127095"
def certificateSHA256 : String := "30f2a85537d3d54d5f3a04801c6052a742ad3a68b93361341563dac6e4aa07a1"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 5 → Fin 678 := ![
  41,
  308,
  313,
  675,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 5 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(47, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (63, 1)] }, { coefficient := 1, powers := [(59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(54, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(63, 1), (72, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 5 → SparsePoly (Fin 73) := ![
  [{ coefficient := 1, powers := [(0, 1), (63, 1), (70, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (63, 1), (72, 2)] }],
  [{ coefficient := 1, powers := [(72, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1), (63, 1), (72, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (63, 1), (72, 1)] }, { coefficient := 1, powers := [(0, 1), (59, 1), (63, 1), (72, 1)] }, { coefficient := -1, powers := [] }]
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

#print axioms Krenn.X5ResidualCase84.LeafB7.selectedHasNoCommonZero

end Krenn.X5ResidualCase84.LeafB7
