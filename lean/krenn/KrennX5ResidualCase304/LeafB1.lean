import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5ResidualCase304.LeafB1

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "bcd25e0d1047eeaf7630f297902cd551e2b4e2879050beee697a82eaf57cb36e"
def sourceSystemSemanticSHA256 : String := "97f7af8be4d4087e4a04023daf8af972c264f27263181dc36e94ae9098eea4d5"
def certificateSHA256 : String := "b7999007e011d2752f7c38d6f15b2741ed407dea168ccbed9f84c94b2a871ce3"
def sourceEquationCount : Nat := 678

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 29 → Fin 678 := ![
  4,
  5,
  26,
  27,
  46,
  47,
  48,
  49,
  55,
  56,
  308,
  325,
  411,
  414,
  421,
  422,
  423,
  424,
  426,
  633,
  642,
  660,
  664,
  665,
  666,
  671,
  673,
  674,
  677
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 29 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(12, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (61, 1)] }, { coefficient := 1, powers := [(60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (60, 1), (61, 1)] }, { coefficient := 1, powers := [(51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (37, 1), (62, 1)] }, { coefficient := 1, powers := [(62, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (50, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(27, 1), (37, 1), (65, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(32, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(32, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(32, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (49, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(49, 1), (63, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(1, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(1, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(18, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(26, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 29 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(15, 1), (32, 1), (36, 1), (50, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(33, 1), (37, 1), (49, 1), (62, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(33, 1), (40, 1), (49, 1), (57, 1), (62, 1), (70, 1)] }, { coefficient := -1, powers := [(33, 1), (43, 1), (49, 1), (54, 1), (62, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (27, 1), (32, 1), (36, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (19, 1), (32, 1), (36, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (33, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(30, 1), (33, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(30, 1), (33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (15, 1), (26, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (32, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(22, 1), (33, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(22, 1), (33, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(22, 1), (33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (15, 1), (18, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (32, 1), (37, 1)] }, { coefficient := 2, powers := [(7, 1), (32, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (42, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (39, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (15, 1), (63, 1), (70, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (57, 1), (70, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (54, 1), (70, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (37, 1), (63, 1), (70, 1)] }, { coefficient := -2, powers := [(7, 1), (32, 1), (40, 1), (57, 1), (70, 1)] }, { coefficient := -1, powers := [(7, 1), (63, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (63, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (33, 1), (36, 1), (51, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (33, 1), (37, 1), (47, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (37, 1), (47, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (7, 1), (25, 1), (32, 1), (37, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (25, 1), (32, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (25, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 2, powers := [(7, 1), (27, 1), (32, 1), (37, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (27, 1), (32, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (27, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (7, 1), (17, 1), (32, 1), (37, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (17, 1), (32, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (17, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (17, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (32, 1), (37, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (19, 1), (32, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (19, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(19, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(15, 1), (26, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (32, 1), (54, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := -2, powers := [(3, 1), (7, 1), (9, 1), (32, 1), (37, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (9, 1), (32, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (9, 1), (34, 1), (43, 1), (54, 1)] }, { coefficient := 2, powers := [(7, 1), (11, 1), (32, 1), (37, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (11, 1), (32, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(11, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (32, 1), (36, 1), (51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (60, 1)] }],
  [{ coefficient := 2, powers := [(7, 1), (33, 1), (37, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(7, 1), (33, 1), (37, 1), (60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(33, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(33, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(33, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(1, 1), (15, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (37, 1)] }, { coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 2, powers := [(3, 1), (7, 1), (32, 1), (37, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (32, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (32, 1), (37, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := -1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(1, 1), (15, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (54, 1), (60, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (37, 1), (49, 1), (63, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (37, 1), (60, 1), (63, 1)] }, { coefficient := 2, powers := [(7, 1), (32, 1), (40, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (32, 1), (40, 1), (57, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (37, 1), (49, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (40, 1), (49, 1), (57, 1), (62, 1)] }, { coefficient := 1, powers := [(14, 1), (33, 1), (43, 1), (49, 1), (54, 1), (62, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 29,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5ResidualCase304.LeafB1.selectedHasNoCommonZero

end Krenn.X5ResidualCase304.LeafB1
