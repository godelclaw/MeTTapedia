import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case64Tree.LeafB7_2

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "707887fbadf364d8e3a42fedbe7cab42a2459a7286ddd9761c56ca65ded7473c"
def sourceSystemSemanticSHA256 : String := "d46de01ba0ce8f9519882940a9e0cac3110f923d501034ac7ca1d9e861107885"
def certificateSHA256 : String := "79c4ce786d3b6a8e1d647433776e77b5edcd931f77a5bd4759516ada04f8f909"
def sourceEquationCount : Nat := 681

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 25 → Fin 681 := ![
  0,
  1,
  15,
  31,
  35,
  36,
  44,
  48,
  407,
  412,
  421,
  424,
  425,
  426,
  439,
  500,
  507,
  509,
  659,
  660,
  672,
  674,
  678,
  679,
  680
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 74) := ![
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(56, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(49, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (51, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (57, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (73, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 74) := ![
  [{ coefficient := -1, powers := [(0, 1), (8, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (26, 1), (32, 1), (41, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (32, 1), (41, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (9, 1), (24, 1), (35, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (32, 1), (41, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (35, 1), (37, 1), (64, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (37, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (35, 1), (37, 1), (64, 1), (69, 1), (73, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (43, 1), (60, 1), (64, 1), (73, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (41, 1), (52, 1), (69, 1), (73, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (43, 1), (52, 1), (60, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (24, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (34, 1), (35, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (52, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (24, 1), (52, 1), (73, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (24, 1), (26, 1), (35, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (38, 1), (58, 1), (73, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (31, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (26, 1), (32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := -1, powers := [(32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (16, 1), (47, 1)] }, { coefficient := -1, powers := [(7, 1), (21, 1), (26, 1), (32, 1), (41, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (31, 1), (32, 1), (41, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (32, 1), (38, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (24, 1), (47, 1), (52, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (35, 1), (37, 1), (64, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (24, 1), (35, 1), (43, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(23, 1), (32, 1), (37, 1), (41, 1), (52, 1), (69, 1)] }, { coefficient := -1, powers := [(23, 1), (32, 1), (41, 1), (43, 1), (52, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (32, 1), (38, 1), (40, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (24, 1), (35, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (41, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (35, 1), (51, 1), (64, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (41, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (35, 1), (40, 1), (64, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (40, 1), (41, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case64Tree.LeafB7_2.selectedHasNoCommonZero

end Krenn.X5Case64Tree.LeafB7_2
