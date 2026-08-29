import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase102.LeafB3

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "d559fbe768104f2c65f53e05234424fddfb0dcff2a7ff9c44a479d499c8890b6"
def sourceSystemSemanticSHA256 : String := "94eb0fa028542b75a9e06315661444ceadb5004dae6ff8437759b1515d2ef0d8"
def certificateSHA256 : String := "52b0cdb5a02a091faa8e0cdfba2f907145a3099f1f52bbf811cda25821e0ecef"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 25 → Fin 678 := ![
  8,
  26,
  31,
  35,
  43,
  49,
  50,
  51,
  394,
  403,
  414,
  416,
  422,
  424,
  425,
  427,
  496,
  659,
  660,
  661,
  672,
  674,
  675,
  676,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 25 → SparsePoly (Fin 72) := ![
  [{ coefficient := 1, powers := [(16, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1), (64, 1)] }, { coefficient := 1, powers := [(37, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(55, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1), (71, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 25 → SparsePoly (Fin 72) := ![
  [{ coefficient := -2, powers := [(8, 1), (34, 1), (40, 1), (41, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (27, 1), (34, 1), (38, 1), (63, 1)] }, { coefficient := 2, powers := [(8, 1), (34, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (34, 1), (35, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (38, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (57, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (34, 1), (41, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (24, 1), (34, 1), (38, 1), (43, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (34, 1), (35, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(26, 1), (34, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(26, 1), (34, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(8, 1), (12, 1), (34, 1), (38, 1), (63, 1)] }, { coefficient := -1, powers := [(12, 1), (16, 1), (34, 1), (35, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (34, 1), (35, 1), (57, 1), (61, 1), (71, 1)] }, { coefficient := -1, powers := [(18, 1), (34, 1), (38, 1), (55, 1), (57, 1), (71, 1)] }],
  [{ coefficient := -1, powers := [(9, 1), (34, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(9, 1), (34, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (34, 1), (40, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (38, 1), (43, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (46, 1), (70, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1), (70, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (8, 1), (38, 1), (48, 1), (67, 1)] }, { coefficient := -2, powers := [(7, 1), (8, 1), (41, 1), (48, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (35, 1), (48, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (35, 1), (48, 1), (61, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (38, 1), (48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (31, 1), (38, 1), (67, 1)] }, { coefficient := 2, powers := [(8, 1), (31, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (23, 1), (38, 1), (67, 1)] }, { coefficient := 2, powers := [(8, 1), (23, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (15, 1), (38, 1), (67, 1)] }, { coefficient := 2, powers := [(8, 1), (15, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (38, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }, { coefficient := -1, powers := [(8, 1), (41, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (8, 1), (38, 1), (67, 1)] }, { coefficient := 2, powers := [(7, 1), (8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := -2, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := -1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (41, 1), (67, 1), (70, 1)] }, { coefficient := -1, powers := [(24, 1), (41, 1), (58, 1), (70, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (41, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (34, 1), (35, 1), (49, 1), (57, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 1), (38, 1), (49, 1), (55, 1), (57, 1)] }]
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
    ¬ ∀ index : Fin 25,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase102.LeafB3.selectedHasNoCommonZero

end Krenn.X5ResidualCase102.LeafB3
