import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case55Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "e58106804643e4cd8a912f075a7ac9b4a72f8037a4cdd03ac734d4c4a06b8a95"
def sourceSystemSemanticSHA256 : String := "78ddf4678759b3a33af1326d323a6a7a8254b9c5b1ad9e78e8d6dfba187df01d"
def certificateSHA256 : String := "52db3243fb66438d0858b52ee2d16db8d92914cf89aa91a0c0c568069c78e734"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 25 → Fin 675 := ![
  0,
  28,
  32,
  39,
  40,
  41,
  42,
  43,
  45,
  47,
  48,
  398,
  405,
  421,
  422,
  423,
  424,
  425,
  531,
  534,
  659,
  662,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(41, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (46, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (46, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (46, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (11, 1), (46, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (11, 1), (46, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (11, 1), (46, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (36, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (39, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (42, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (35, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (35, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (35, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (39, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (42, 1), (45, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (35, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (35, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (35, 1), (59, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (32, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (32, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (55, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (32, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (32, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (52, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(27, 1), (32, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (32, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(27, 1), (32, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (24, 1), (32, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (32, 1), (52, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (32, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (16, 1), (32, 1), (53, 1), (55, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (32, 1), (53, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (24, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (24, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (24, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (24, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (16, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (16, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (16, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (16, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (16, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (16, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (25, 1), (32, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (32, 1), (41, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (32, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (32, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (41, 1), (53, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (41, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(28, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (17, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (53, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (52, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }],
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case55Selected.selectedHasNoCommonZero

end Krenn.X5Case55Selected
