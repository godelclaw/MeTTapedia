import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case128Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "f5d0e30a67a8e705bc696584ddd80d08acc607273d752cf9ebaca6ef671bc4c5"
def sourceSystemSemanticSHA256 : String := "7ebb408cdbb988a5a7addd83a679384829d6962abfc35afdc4b43cd75bb13a63"
def certificateSHA256 : String := "bfb5987d3e1bf2310d139f317f4f0097ce49b8236fa2456ae8a4415a563328e3"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 17 → Fin 675 := ![
  0,
  1,
  2,
  3,
  26,
  27,
  311,
  415,
  416,
  421,
  422,
  423,
  424,
  425,
  437,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (61, 1)] }, { coefficient := 1, powers := [(59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(0, 1), (67, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (58, 1), (61, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (28, 1), (47, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (42, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (35, 1), (61, 1), (68, 1)] }, { coefficient := -1, powers := [(28, 1), (32, 1), (35, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (33, 1), (35, 1), (42, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (64, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (58, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (47, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (39, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (35, 1), (61, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (32, 1), (35, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (33, 1), (35, 1), (39, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (27, 1), (39, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (42, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (27, 1), (58, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (32, 1), (35, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(27, 1), (32, 1), (35, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(27, 1), (32, 1), (35, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (19, 1), (39, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (42, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (19, 1), (58, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (35, 1), (39, 1), (68, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (35, 1), (42, 1), (65, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (35, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (11, 1), (58, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (35, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (39, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (42, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (47, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (28, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (35, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := -1, powers := [(32, 1), (35, 1), (61, 1)] }]
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
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case128Selected.selectedHasNoCommonZero

end Krenn.X5Case128Selected
