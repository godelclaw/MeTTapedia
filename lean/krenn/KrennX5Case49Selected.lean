import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case49Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "267d43e84fa85049db2265bab966209b57873d9b38f943366aa12077a5af09c8"
def sourceSystemSemanticSHA256 : String := "8969028166936331ce9bb854aa920847347110afe1d285012b914a310022dff1"
def certificateSHA256 : String := "a63374cbe62d348241bb58336b73811de3832abdb8518ef0ab9a7f02da707b22"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 24 → Fin 675 := ![
  0,
  1,
  9,
  25,
  32,
  36,
  39,
  314,
  414,
  416,
  420,
  422,
  423,
  425,
  429,
  531,
  587,
  627,
  643,
  659,
  662,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (55, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (56, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(11, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (41, 1), (59, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (38, 1), (68, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (38, 1), (59, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (25, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (25, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (33, 1), (36, 1), (66, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (25, 1), (33, 1), (35, 1), (39, 1), (56, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (16, 1), (25, 1), (33, 1), (39, 1), (41, 1), (56, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (33, 1), (35, 1), (39, 1), (56, 1), (67, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (33, 1), (39, 1), (41, 1), (56, 1), (58, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (25, 1), (33, 1), (35, 1), (39, 1), (56, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (25, 1), (33, 1), (39, 1), (41, 1), (56, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (33, 1), (35, 1), (39, 1), (56, 1), (67, 1), (68, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (33, 1), (39, 1), (41, 1), (56, 1), (58, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (25, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (68, 1)] }, { coefficient := -1, powers := [(16, 1), (25, 1), (33, 2), (35, 1), (36, 1), (39, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (25, 1), (33, 2), (36, 1), (39, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 2), (35, 1), (39, 1), (42, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 2), (39, 1), (41, 1), (42, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(25, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (11, 1), (24, 1), (25, 1), (32, 1), (35, 1), (39, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(2, 1), (11, 1), (24, 1), (25, 1), (39, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (27, 1), (32, 1), (35, 1), (39, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(2, 1), (24, 1), (27, 1), (39, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(8, 1), (33, 1), (39, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 2), (24, 1), (25, 1), (32, 1), (35, 1), (39, 1), (45, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 2), (24, 1), (25, 1), (39, 1), (45, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (27, 1), (32, 1), (35, 1), (39, 1), (45, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (27, 1), (39, 1), (45, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (33, 1), (35, 1), (39, 1), (56, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (33, 1), (39, 1), (41, 1), (56, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (35, 1), (39, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (33, 1), (39, 1), (41, 1), (56, 1), (58, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (33, 1), (35, 1), (39, 1), (56, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (33, 1), (39, 1), (41, 1), (56, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (35, 1), (39, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(11, 1), (33, 1), (39, 1), (41, 1), (56, 1), (58, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (33, 2), (35, 1), (36, 1), (39, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(17, 1), (33, 2), (36, 1), (39, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(33, 2), (35, 1), (39, 2), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(33, 2), (39, 2), (41, 1), (56, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (33, 1), (62, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (18, 1), (24, 1), (25, 1), (32, 1), (35, 1), (39, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (18, 1), (24, 1), (25, 1), (39, 1), (58, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (27, 1), (32, 1), (35, 1), (39, 1), (66, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (27, 1), (39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1), (33, 1), (35, 1), (39, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (16, 1), (24, 1), (32, 1), (35, 1), (39, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (24, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (32, 1), (35, 1), (39, 1), (66, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (39, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (17, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (65, 1)] }, { coefficient := -1, powers := [(17, 1), (33, 1), (36, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (35, 1), (39, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (33, 1), (39, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (44, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (39, 1), (45, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (59, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (59, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (33, 1), (35, 1), (39, 1), (56, 1), (59, 1), (67, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (33, 1), (39, 1), (41, 1), (56, 1), (58, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (45, 1), (66, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (33, 1), (35, 1), (39, 1), (56, 1), (59, 1), (67, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (33, 1), (39, 1), (41, 1), (56, 1), (58, 1), (59, 1)] }, { coefficient := -1, powers := [(11, 1), (45, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 2), (35, 1), (36, 1), (39, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 2), (36, 1), (39, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (16, 1), (25, 1), (33, 1), (35, 1), (39, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (25, 1), (33, 1), (39, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (25, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (33, 1), (35, 1), (39, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (27, 1), (33, 1), (39, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(27, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (16, 1), (17, 1), (33, 1), (35, 1), (39, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (17, 1), (33, 1), (39, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [(11, 1), (17, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (33, 1), (35, 1), (39, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (19, 1), (33, 1), (39, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (33, 1), (39, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (33, 1), (35, 1), (39, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(11, 1), (24, 1), (32, 1), (35, 1), (39, 1), (66, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (24, 1), (25, 1), (32, 1), (35, 1), (39, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (24, 1), (25, 1), (39, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (32, 1), (35, 1), (39, 1), (66, 1)] }, { coefficient := -1, powers := [(24, 1), (27, 1), (39, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (32, 1), (35, 1), (39, 1), (66, 1)] }, { coefficient := 1, powers := [(24, 1), (39, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (66, 1)] }, { coefficient := 1, powers := [(11, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (33, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (16, 1), (33, 1), (35, 1), (39, 1), (56, 1), (67, 1)] }, { coefficient := 1, powers := [(11, 1), (16, 1), (33, 1), (39, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (39, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (33, 1), (35, 1), (39, 1), (56, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (33, 1), (39, 1), (41, 1), (56, 1), (58, 1)] }, { coefficient := -1, powers := [] }]
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case49Selected.selectedHasNoCommonZero

end Krenn.X5Case49Selected
