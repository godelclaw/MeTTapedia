import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case346Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "6eac60cfb2a3da4f919ab52906d3dadaa9afd9e47c1e7c2cd9cf740490a40bd9"
def sourceSystemSemanticSHA256 : String := "beee7514c0f46563b92c9fa0ad7c6015c323c21886e746bdccd75d9ac36cbd4b"
def certificateSHA256 : String := "ce7ad42a5b71058215b1da0e6787b214471d10cee6df084f3d225dfa4089a1bd"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 19 → Fin 675 := ![
  0,
  1,
  39,
  41,
  43,
  45,
  47,
  49,
  421,
  422,
  423,
  424,
  425,
  426,
  659,
  661,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(33, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (32, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (32, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (32, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1)] }, { coefficient := 1, powers := [(20, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1)] }, { coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }],
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
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case346Selected.selectedHasNoCommonZero

end Krenn.X5Case346Selected
