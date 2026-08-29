import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase429.LeafB5

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "94255bd301a53ea178e7211ae7323e6e5e67cf1963ae9e9b90d48960719b6def"
def sourceSystemSemanticSHA256 : String := "1925cb7a985a1e8f5d49096b39a369cf4beb22deb8af67487064c74b6b51d5b9"
def certificateSHA256 : String := "0aa19ec99e5f7f48f89c79fed05e50277a804781c0bb9e1bf9213386094bed5f"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 16 → Fin 678 := ![
  18,
  32,
  34,
  142,
  309,
  413,
  414,
  422,
  423,
  426,
  621,
  660,
  672,
  675,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 16 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(25, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(60, 1), (61, 1)] }, { coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(61, 1), (71, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 16 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(34, 1), (35, 1), (47, 1), (61, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (35, 1), (61, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (35, 1), (58, 1), (61, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (42, 1), (58, 1), (61, 1), (70, 1), (71, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (35, 1), (61, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (35, 1), (61, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (34, 1), (35, 1), (42, 1), (58, 1), (60, 1), (61, 1), (70, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (35, 1), (42, 1), (58, 1), (61, 1), (70, 1)] }, { coefficient := -1, powers := [(32, 1), (41, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(32, 1), (41, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 16,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase429.LeafB5.selectedHasNoCommonZero

end Krenn.X5ResidualCase429.LeafB5
