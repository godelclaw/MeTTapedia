import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case535Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "eec8c874f0ee18256f32bdedf7f3fa9cd466183ec8dd7378bf47846f1bcedf44"
def sourceSystemSemanticSHA256 : String := "76359cddcbbfbbdfe9a2eb771f9a65d5b1991b02d179147750971acae8e2bf97"
def certificateSHA256 : String := "467710b5fe3bbb70a1f4a0bc88f09b6a080b4805b0b9b15685b2f5e3117b7906"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 7 → Fin 675 := ![
  2,
  3,
  418,
  421,
  424,
  670,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 7 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (56, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(14, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(14, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(22, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(22, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 7 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(3, 1), (22, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (22, 1), (28, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (65, 1)] }, { coefficient := -1, powers := [(22, 1), (33, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (14, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (14, 1), (28, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (59, 1)] }, { coefficient := -1, powers := [(14, 1), (33, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (68, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (68, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }, { coefficient := -1, powers := [(22, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [] }]
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
    (values : Fin 70 → R) :
    ¬ ∀ index : Fin 7,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case535Selected.selectedHasNoCommonZero

end Krenn.X5Case535Selected
