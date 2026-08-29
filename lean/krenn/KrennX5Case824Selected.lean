import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case824Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "b2d8fe65599c88164b71ad74744cde36c4a69655b03c9eb6ba7352d302f4d0fa"
def sourceSystemSemanticSHA256 : String := "80037022084a7a23278a360003f4d222ced64e1cfcc559c1ff813f4f32d0482d"
def certificateSHA256 : String := "be19648f157ea53a8f4693f62666ead130b6f956f77af93ea1d6d5e4ebddd325"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 27 → Fin 675 := ![
  0,
  1,
  9,
  15,
  26,
  31,
  34,
  46,
  378,
  399,
  420,
  421,
  423,
  424,
  425,
  441,
  449,
  502,
  525,
  596,
  642,
  656,
  660,
  663,
  668,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 27 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (42, 1), (64, 1)] }, { coefficient := 1, powers := [(42, 1), (58, 1)] }, { coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (37, 1), (64, 1)] }, { coefficient := 1, powers := [(37, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(21, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(6, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(13, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (52, 1)] }, { coefficient := 1, powers := [(55, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(46, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(21, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(21, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(21, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(29, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(29, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(29, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 27 → SparsePoly (Fin 70) := ![
  [{ coefficient := -1, powers := [(4, 1), (10, 1), (15, 1), (29, 1), (48, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (26, 1), (48, 1)] }, { coefficient := -1, powers := [(4, 1), (16, 1), (34, 1), (35, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (29, 1), (34, 1), (37, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (29, 1), (48, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (48, 1)] }, { coefficient := -1, powers := [(16, 1), (27, 1), (34, 1), (35, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(29, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (40, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(8, 1), (34, 1), (40, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (21, 1), (34, 1), (35, 1), (49, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (44, 1), (57, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (48, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (44, 1), (48, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (34, 1), (63, 1)] }, { coefficient := 1, powers := [(16, 1), (21, 1), (30, 1), (34, 1), (35, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (34, 1), (42, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (42, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (44, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (13, 1), (34, 1), (40, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (34, 1), (40, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (40, 1), (44, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (10, 1), (15, 1), (21, 1)] }, { coefficient := 1, powers := [(4, 1), (15, 1), (18, 1)] }, { coefficient := 1, powers := [(7, 1), (10, 1), (21, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (34, 1), (37, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (44, 1), (57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (10, 1), (15, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (37, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (10, 1), (48, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (34, 1), (40, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (29, 1)] }, { coefficient := 1, powers := [(31, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (21, 1)] }, { coefficient := 1, powers := [(23, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (34, 1), (40, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(44, 1), (57, 1), (64, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (32, 1), (40, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (34, 1), (40, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(24, 1), (34, 1), (40, 1), (44, 1), (57, 1)] }, { coefficient := -1, powers := [(34, 1), (40, 1), (44, 1), (57, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(16, 1), (21, 1), (34, 1), (35, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (32, 1), (40, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (44, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(32, 1), (40, 1), (46, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (15, 1)] }, { coefficient := 1, powers := [(7, 1)] }],
  [{ coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (40, 1), (57, 1)] }],
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
    ¬ ∀ index : Fin 27,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case824Selected.selectedHasNoCommonZero

end Krenn.X5Case824Selected
