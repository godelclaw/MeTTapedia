import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case64Tree.LeafB7_3

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "bca3159c4d0bba78c7362b73e7defc4625fd9a9dcd5b71fc7fcdc047a88ca8b7"
def sourceSystemSemanticSHA256 : String := "a7c5985b6e62364de4b44ab5ec3fa03ad9f1187b9df4d4fdd46553281be78341"
def certificateSHA256 : String := "1ed0ad05feea62a951f8dbe2af2c801c8190fec0a090e0633ca003178ef765c2"
def sourceEquationCount : Nat := 681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 10 → Fin 681 := ![
  412,
  420,
  422,
  423,
  643,
  665,
  671,
  673,
  675,
  679
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 10 → SparsePoly (Fin 75) := ![
  [{ coefficient := 1, powers := [(32, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (73, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 10 → SparsePoly (Fin 75) := ![
  [{ coefficient := 1, powers := [(73, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (40, 1), (45, 1), (70, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (40, 1), (45, 1), (70, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (25, 1), (32, 1), (40, 1)] }, { coefficient := -1, powers := [(28, 1), (32, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (17, 1), (32, 1), (40, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (32, 1), (40, 1), (70, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (40, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (32, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (40, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (40, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (40, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (40, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (40, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (40, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (40, 1)] }, { coefficient := -1, powers := [] }]
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
    (values : Fin 75 → R) :
    ¬ ∀ index : Fin 10,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case64Tree.LeafB7_3.selectedHasNoCommonZero

end Krenn.X5Case64Tree.LeafB7_3
