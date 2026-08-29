import KrennSparseCertificate

/-! Selected core of a strict exact certificate over a frozen system. -/

namespace Krenn.X5Case106Selected

open Krenn.SparseCertificate
open MvPolynomial

def sourceSystemFileSHA256 : String := "0bdf321267d13838de34f6ed3ff48f57cd1d63381d9439b7cf338c9eacbcfdde"
def sourceSystemSemanticSHA256 : String := "ea1aed2ea563b87c1c22a178c606f25329c3a775224449ee6b884c142684aaf9"
def certificateSHA256 : String := "9fd165f516bb92b42f8e3b20ea33b43d08aaf12c54492b05648c1968a0f0b6d3"
def sourceEquationCount : Nat := 675

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedIndices : Fin 21 → Fin 675 := ![
  0,
  1,
  2,
  3,
  28,
  29,
  30,
  31,
  46,
  421,
  423,
  424,
  425,
  426,
  430,
  489,
  633,
  642,
  660,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 21 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(52, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(63, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (38, 1), (69, 1)] }, { coefficient := 1, powers := [(29, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(46, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (38, 1), (69, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (43, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 21 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(0, 1), (67, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (26, 1), (49, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (43, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (26, 1), (35, 1), (49, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (26, 1), (41, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (26, 1), (44, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (26, 1), (34, 1), (38, 1), (49, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (26, 1), (32, 1), (38, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (43, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (41, 1), (43, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (43, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 2), (38, 1), (43, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (34, 1), (38, 1), (55, 1)] }, { coefficient := 2, powers := [(32, 1), (34, 1), (38, 1), (43, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (9, 1), (49, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (34, 1), (37, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (16, 1), (35, 1), (49, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (16, 1), (41, 1), (49, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (16, 1), (44, 1), (49, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (18, 1), (34, 1), (38, 1), (49, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (9, 1), (32, 1), (38, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (34, 1), (37, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (34, 2), (37, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(32, 1), (34, 1), (37, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (29, 1), (34, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(18, 1), (31, 1), (34, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(21, 1), (29, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(31, 1), (32, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (18, 1), (21, 1), (34, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(12, 1), (21, 1), (32, 1), (40, 1), (55, 1)] }, { coefficient := -1, powers := [(15, 1), (18, 1), (34, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(15, 1), (32, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (34, 1), (41, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (34, 1), (35, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (7, 1), (18, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (18, 1), (35, 1), (67, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (18, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(7, 1), (16, 1), (18, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 2), (34, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(7, 1), (18, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (31, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (31, 1), (34, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (34, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(8, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (15, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(15, 1), (16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(15, 1), (18, 1), (34, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (40, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (21, 1), (34, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(21, 1), (32, 1), (40, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (34, 1), (40, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (40, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(34, 1), (38, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (7, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(7, 1), (16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (18, 1), (34, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := -1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := -1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := -1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(18, 1), (34, 1), (38, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(32, 1), (38, 1), (55, 1)] }]
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
    ¬ ∀ index : Fin 21,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.X5Case106Selected.selectedHasNoCommonZero

end Krenn.X5Case106Selected
