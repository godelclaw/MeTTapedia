import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case355Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "6382a94c65b27b4dc17940b799992908dd8e3265faa458be4296c8e3250f14eb"
def sourceSystemSemanticSHA256 : String := "efef391cd03db8238e4c717544f5fa21298dcf2cc188d0c267e6d86f8d048115"
def certificateSHA256 : String := "7ccb290058f8bf1946b2aa659dc669d76d8c880a721ceedbf88c385a8183c9c8"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 24 → Fin 675 := ![
  0,
  25,
  29,
  39,
  40,
  41,
  42,
  44,
  46,
  48,
  49,
  390,
  397,
  419,
  422,
  423,
  426,
  427,
  503,
  509,
  659,
  661,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(17, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (45, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (35, 1), (68, 1)] }, { coefficient := 1, powers := [(35, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (38, 1), (68, 1)] }, { coefficient := 1, powers := [(21, 1), (45, 1), (56, 1)] }, { coefficient := 1, powers := [(38, 1), (59, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(19, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(20, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (24, 1), (46, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (24, 1), (46, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (24, 1), (46, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (24, 1), (46, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (24, 1), (36, 1), (46, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (24, 1), (42, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (28, 1), (36, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (28, 1), (39, 1), (46, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (33, 1), (36, 1), (46, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (33, 1), (39, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (24, 1), (33, 1), (42, 1), (46, 1), (53, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (41, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (41, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (41, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (41, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (36, 1), (41, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (41, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(27, 1), (32, 1), (36, 1), (45, 1), (62, 1)] }, { coefficient := -1, powers := [(27, 1), (32, 1), (39, 1), (45, 1), (56, 1)] }, { coefficient := -1, powers := [(27, 1), (32, 1), (42, 1), (45, 1), (53, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (36, 1), (41, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (39, 1), (41, 1), (59, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (22, 1), (32, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (53, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (36, 1), (61, 1)] }, { coefficient := -1, powers := [(22, 1), (28, 1), (32, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (14, 1), (32, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(3, 1), (32, 1), (53, 1), (55, 1)] }, { coefficient := -1, powers := [(14, 1), (20, 1), (32, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(14, 1), (28, 1), (32, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(19, 1), (32, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(19, 1), (32, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (21, 1), (32, 1), (55, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (21, 1), (32, 1), (42, 1), (55, 1)] }, { coefficient := -1, powers := [(21, 1), (28, 1), (32, 1), (39, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(10, 1), (32, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(10, 1), (32, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (13, 1), (32, 1), (56, 1), (61, 1)] }, { coefficient := -1, powers := [(13, 1), (28, 1), (32, 1), (36, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (16, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (16, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (16, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (11, 1), (16, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (20, 1), (36, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (20, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (16, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (8, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (8, 1), (11, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (20, 1), (36, 1), (68, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (20, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(0, 1), (8, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (17, 1), (32, 1), (38, 1), (56, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (38, 1), (62, 1)] }, { coefficient := -1, powers := [(17, 1), (28, 1), (32, 1), (36, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (9, 1), (32, 1), (35, 1), (62, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (32, 1), (35, 1), (42, 1)] }, { coefficient := -1, powers := [(9, 1), (28, 1), (32, 1), (35, 1), (39, 1)] }, { coefficient := -1, powers := [(11, 1), (32, 1), (35, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (35, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (35, 1), (42, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (35, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (38, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(47, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (24, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (24, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (24, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (24, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(24, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (16, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (16, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(11, 1), (16, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(16, 1), (20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (8, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (8, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(8, 1), (11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(8, 1), (20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(8, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(11, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (56, 1), (61, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (36, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (32, 1), (55, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (32, 1), (42, 1), (55, 1)] }, { coefficient := 1, powers := [(28, 1), (32, 1), (39, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (59, 1), (62, 1)] }, { coefficient := -1, powers := [(0, 1), (11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(0, 1), (20, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(0, 1), (28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (33, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (53, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := -1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (36, 1), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (42, 1), (59, 1)] }, { coefficient := -1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := -1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := -1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := -1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := -1, powers := [(33, 1), (42, 1), (53, 1)] }],
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
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case355Selected.selectedHasNoCommonZero

end Krenn.X5Case355Selected
