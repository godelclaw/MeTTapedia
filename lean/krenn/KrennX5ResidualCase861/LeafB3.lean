import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase861.LeafB3

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "17b1db9a0e8886d87ab59dd5b0ebb3deaba1695002132051a2842222f4f49336"
def sourceSystemSemanticSHA256 : String := "0228e053ab82871239b8bc24df756d25bc0e8591f9f86fd1b48a67e287a98747"
def certificateSHA256 : String := "d6ec2704736a1083bb6e96a141a23cca3bc6f48298317f502406a150a5f63acc"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 26 → Fin 678 := ![
  1,
  24,
  25,
  28,
  37,
  43,
  46,
  56,
  345,
  388,
  395,
  414,
  422,
  423,
  424,
  425,
  426,
  431,
  433,
  660,
  664,
  672,
  674,
  675,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 26 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(8, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(22, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1), (71, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 26 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (47, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (44, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (15, 1), (32, 1), (43, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (57, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (32, 1), (54, 1), (60, 1), (61, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (32, 1), (40, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (32, 1), (54, 1), (55, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (32, 1), (40, 1), (55, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (32, 1), (43, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (16, 1), (55, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (32, 1), (37, 1), (61, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (40, 1), (57, 1), (61, 1), (70, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (43, 1), (54, 1), (61, 1), (70, 1)] }, { coefficient := -1, powers := [(22, 1), (32, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (32, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(22, 1), (32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (16, 1), (55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1), (71, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1), (71, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (3, 1), (7, 1), (47, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (15, 1), (40, 1), (47, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (3, 1), (15, 1), (43, 1), (47, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (47, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (47, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (37, 1), (47, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (40, 1), (47, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (34, 1), (43, 1), (47, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (24, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (24, 1), (40, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (24, 1), (43, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (16, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (16, 1), (40, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (16, 1), (43, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (8, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (15, 1), (40, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (8, 1), (15, 1), (43, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (8, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(8, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1), (61, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (3, 1), (7, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (15, 1), (40, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(0, 1), (3, 1), (15, 1), (43, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (7, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (40, 1), (60, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (43, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (32, 1), (41, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (32, 1), (40, 1), (41, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (32, 1), (41, 1), (43, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (41, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (41, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(30, 1), (32, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(30, 1), (32, 1), (40, 1), (46, 1), (57, 1)] }, { coefficient := -1, powers := [(30, 1), (32, 1), (43, 1), (46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (32, 1), (37, 1), (46, 1), (61, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (40, 1), (46, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (43, 1), (46, 1), (54, 1), (61, 1)] }, { coefficient := -1, powers := [(15, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (7, 1), (54, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (40, 1), (60, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (43, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := -1, powers := [(15, 1), (43, 1), (66, 1)] }]
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
    (values : Fin 72 → R) :
    ¬ ∀ index : Fin 26,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase861.LeafB3.selectedHasNoCommonZero

end Krenn.X5ResidualCase861.LeafB3
