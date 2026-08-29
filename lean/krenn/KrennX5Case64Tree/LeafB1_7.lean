import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case64Tree.LeafB1_7

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "d98738d33d55ac99a2054ae4d3537da914650e52b1773af1003e93d7322cdd46"
def sourceSystemSemanticSHA256 : String := "562aeb60951e2689a578351f9d0bd8536a696ddeb01a2e1128e5e591b8b33296"
def certificateSHA256 : String := "6e58d08464de9dea06412dcdc71f934526f8721a419caac1b05389a9f38a3e0b"
def sourceEquationCount : Nat := 681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 17 → Fin 681 := ![
  9,
  15,
  31,
  46,
  396,
  397,
  420,
  422,
  423,
  500,
  620,
  665,
  673,
  676,
  678,
  679,
  680
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 74) := ![
  [{ coefficient := 1, powers := [(17, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (71, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(56, 1), (72, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (73, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 74) := ![
  [{ coefficient := 1, powers := [(11, 1), (40, 1), (47, 1), (68, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1), (71, 1), (72, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (71, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (17, 1), (32, 1), (40, 1), (42, 1), (71, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (40, 1), (62, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (40, 1), (68, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (32, 1), (40, 1), (42, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (40, 1), (47, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (32, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (32, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(71, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (40, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (40, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(32, 1), (40, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(32, 1), (40, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (32, 1), (40, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (32, 1), (40, 1), (48, 1), (62, 1)] }, { coefficient := -1, powers := [(32, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(23, 1), (24, 1), (55, 1), (71, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (32, 1), (39, 1), (40, 1), (68, 1)] }]
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
    (values : Fin 74 → R) :
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case64Tree.LeafB1_7.selectedHasNoCommonZero

end Krenn.X5Case64Tree.LeafB1_7
