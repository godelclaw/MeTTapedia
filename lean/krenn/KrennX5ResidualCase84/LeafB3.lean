import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase84.LeafB3

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "9e56cd18e2c0fc171d4c722d12b519f7a87a553ea92ce0c5b9f14c7cdccf38c9"
def sourceSystemSemanticSHA256 : String := "5d2efff70fca0dbaf4e0fb6ff260548454aacee097b17153afb7b6b72a139a9c"
def certificateSHA256 : String := "bc36114a34b2bb96f78486ce24e6267175307c265158b6dd643bc472f4f20079"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 5 → Fin 678 := ![
  42,
  308,
  313,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 5 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(47, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (63, 1)] }, { coefficient := 1, powers := [(59, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (59, 1), (63, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(63, 1), (71, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 5 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(0, 1), (63, 1), (70, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (63, 1), (71, 2)] }],
  [{ coefficient := 1, powers := [(71, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1), (63, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (63, 1), (71, 1)] }, { coefficient := 1, powers := [(0, 1), (59, 1), (63, 1), (71, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 5,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase84.LeafB3.selectedHasNoCommonZero

end Krenn.X5ResidualCase84.LeafB3
