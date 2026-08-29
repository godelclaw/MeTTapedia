import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case281Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "0136422b29f4ae279724d5105e54d7b11928578d46c0d64f581199d24d7a0454"
def sourceSystemSemanticSHA256 : String := "9c99bc4ae18f0e1c020f15cedcf4319fe11cbc9af42051d2e5835c8e6e2a43c6"
def certificateSHA256 : String := "6716567037eed87ff9b44b411e887135700e4a30a839dbadec55747fb29caa1d"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 7 → Fin 675 := ![
  2,
  3,
  416,
  420,
  424,
  669,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 7 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 7 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(0, 1), (21, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (21, 1), (24, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (64, 1)] }, { coefficient := -1, powers := [(21, 1), (32, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (24, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (58, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (41, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (24, 1), (67, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }, { coefficient := -1, powers := [(21, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }, { coefficient := -1, powers := [(13, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
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

#print axioms Krenn.X5Case281Selected.selectedHasNoCommonZero

end Krenn.X5Case281Selected
