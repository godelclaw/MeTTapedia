import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case178Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "a5945bf73ad588857c78e7bfcee50f66415317bad57e306bb78c1a5d957a402c"
def sourceSystemSemanticSHA256 : String := "ca11823cd6d2988fdc4eb7f6e66bb0830ee3d3ac44228369f364ae21e6e89968"
def certificateSHA256 : String := "59ac4e4466ec91dbd38b782d9199a4e714ffc06271be8798ce243f2d051fb0be"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 17 → Fin 675 := ![
  0,
  1,
  2,
  3,
  30,
  31,
  46,
  421,
  423,
  424,
  425,
  426,
  441,
  500,
  660,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 17 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (55, 1), (66, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 17 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(0, 1), (67, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (55, 1), (64, 1), (69, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (43, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (26, 1), (35, 1), (49, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (26, 1), (41, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (44, 1), (55, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (55, 1), (69, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (43, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (41, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (43, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (38, 1), (43, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (55, 1), (60, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (16, 1), (35, 1), (49, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (16, 1), (41, 1), (49, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (44, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (55, 1), (60, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (34, 1), (37, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (30, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (30, 1), (44, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(30, 1), (32, 1), (38, 1), (51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (13, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(13, 1), (16, 1), (44, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(13, 1), (32, 1), (38, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(7, 1), (16, 1), (18, 1), (35, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (18, 1), (41, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (31, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (15, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (51, 1), (57, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (44, 1), (51, 1), (57, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (41, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (55, 1)] }]
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
    ¬ ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case178Selected.selectedHasNoCommonZero

end Krenn.X5Case178Selected
