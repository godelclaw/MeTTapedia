import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case16Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "1f1538e6453c4f2c24bc030feb4ea4d7f55e28a550118a49c1d8176a64560ced"
def sourceSystemSemanticSHA256 : String := "09a556d41347b8e2b2b4d9e7bc4f8059789322a8feb715a21e5234dd53e2de98"
def certificateSHA256 : String := "30c75a629acf839cb1d0f69559fe35c449b893a5476b36fe57d1250995bc2273"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 19 → Fin 675 := ![
  0,
  1,
  2,
  3,
  34,
  35,
  45,
  407,
  421,
  423,
  424,
  425,
  426,
  439,
  476,
  503,
  660,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 19 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (52, 1), (69, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(49, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(31, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(17, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 19 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (18, 1), (26, 1), (49, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (24, 1), (26, 1), (44, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (26, 1), (32, 1), (41, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (17, 1), (49, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (40, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (24, 1), (35, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (24, 1), (38, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (24, 1), (44, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (17, 1), (32, 1), (41, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (35, 1), (40, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (38, 1), (40, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (40, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (40, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (10, 1), (26, 1), (49, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (24, 1), (26, 1), (44, 1), (49, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (26, 1), (32, 1), (41, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (9, 1), (49, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (24, 1), (35, 1), (49, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (24, 1), (38, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (24, 1), (44, 1), (49, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (32, 1), (41, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (35, 1), (37, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (37, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (37, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (21, 1), (51, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (24, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(21, 1), (32, 1), (41, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (38, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (51, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (41, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (35, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (26, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (26, 1), (35, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (26, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (26, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (54, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (24, 1), (44, 1), (54, 1)] }, { coefficient := -1, powers := [(7, 1), (32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(16, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (31, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(23, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (15, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (26, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (26, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(7, 1), (26, 1), (32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (51, 1), (54, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (51, 1), (54, 1)] }, { coefficient := -1, powers := [(32, 1), (41, 1), (51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (41, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := -1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := -1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := -1, powers := [(32, 1), (41, 1), (52, 1)] }]
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
    ¬ ∀ index : Fin 19,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case16Selected.selectedHasNoCommonZero

end Krenn.X5Case16Selected
