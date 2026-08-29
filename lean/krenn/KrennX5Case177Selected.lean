import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case177Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "270e96811c8538c6f5075737f3410c7ec45b1f6a9a52ff1d819fc71d645e88a7"
def sourceSystemSemanticSHA256 : String := "4caa0b7ac59532d28ec39c381c43e826039f7b7c8c2fc3b9a5564c1747673e79"
def certificateSHA256 : String := "9402eafe57baac2e9e205ab072ca5c34097c9ea1c153025aa8e47d2b9a488d55"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 32 → Fin 675 := ![
  1,
  2,
  4,
  17,
  23,
  25,
  29,
  33,
  35,
  36,
  37,
  45,
  51,
  223,
  285,
  310,
  391,
  413,
  414,
  418,
  420,
  422,
  423,
  424,
  425,
  438,
  501,
  542,
  660,
  669,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 32 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (36, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (52, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(31, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (36, 1), (69, 1)] }, { coefficient := 1, powers := [(26, 1), (36, 1), (66, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(5, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(30, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 32 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(7, 1), (16, 1), (44, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (35, 1), (64, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (38, 1), (58, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (41, 1), (52, 1), (66, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (40, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (35, 1), (40, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (38, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (38, 1), (40, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (40, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (13, 1), (26, 1), (32, 1), (36, 1), (38, 1), (60, 1), (66, 1)] }, { coefficient := -1, powers := [(7, 1), (13, 1), (32, 1), (38, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(8, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (26, 1), (32, 1), (34, 1), (36, 1), (37, 1), (38, 1), (66, 1)] }, { coefficient := -1, powers := [(13, 1), (32, 1), (34, 1), (38, 1), (43, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (24, 1), (38, 1), (47, 1), (60, 1)] }, { coefficient := -1, powers := [(24, 1), (34, 1), (37, 1), (38, 1), (47, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (35, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (43, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (32, 1), (38, 1), (52, 1), (69, 1)] }, { coefficient := -1, powers := [(32, 1), (34, 1), (38, 1), (43, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (18, 1), (24, 1), (35, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (32, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (34, 1), (35, 1), (37, 1), (64, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (34, 1), (37, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (32, 1), (34, 1), (37, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (37, 1), (41, 1), (52, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (54, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (32, 1), (34, 1), (41, 1), (52, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (24, 1), (34, 1), (38, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (16, 1), (55, 1), (69, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (43, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (16, 1), (55, 1), (60, 1)] }, { coefficient := -1, powers := [(16, 1), (34, 1), (37, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (31, 1), (34, 1), (38, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (35, 1), (60, 1), (64, 1)] }, { coefficient := -1, powers := [(26, 1), (34, 1), (35, 1), (37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (26, 1), (32, 1), (38, 1), (52, 1), (60, 1)] }, { coefficient := 1, powers := [(26, 1), (32, 1), (34, 1), (37, 1), (38, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (34, 1), (36, 1), (37, 1), (41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (32, 1), (41, 1), (60, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (47, 1)] }, { coefficient := 1, powers := [(5, 1), (16, 1), (47, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (26, 1), (32, 1), (36, 1), (38, 1), (60, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (54, 1), (69, 1)] }, { coefficient := -1, powers := [(26, 1), (32, 1), (34, 1), (36, 1), (37, 1), (38, 1), (66, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (38, 1), (43, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (30, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (23, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }, { coefficient := -1, powers := [(13, 1), (16, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (34, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (35, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (35, 1), (37, 1), (64, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (37, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (37, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1)] }, { coefficient := -1, powers := [(5, 1), (16, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := -1, powers := [(32, 1), (41, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 32,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case177Selected.selectedHasNoCommonZero

end Krenn.X5Case177Selected
