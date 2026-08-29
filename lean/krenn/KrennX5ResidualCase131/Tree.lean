import KrennX5ResidualCase131.LeafB0
import KrennX5ResidualCase131.LeafB1
import KrennX5ResidualCase131.LeafB2
import KrennX5ResidualCase131.LeafB3
import KrennX5ResidualCase131.LeafB4
import KrennX5ResidualCase131.LeafB5
import KrennX5ResidualCase131.LeafB6
import KrennX5ResidualCase131.LeafB7

namespace Krenn.X5ResidualCase131.Tree

open Krenn.SparseCertificate
open MvPolynomial

def rootVariableCount : Nat := 70

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def rootSelectedIndices : Fin 53 → Fin 675 := ![
  1,
  7,
  9,
  10,
  12,
  15,
  17,
  18,
  20,
  23,
  29,
  31,
  33,
  35,
  38,
  43,
  45,
  47,
  49,
  50,
  51,
  54,
  56,
  307,
  324,
  387,
  388,
  393,
  397,
  402,
  406,
  414,
  416,
  418,
  420,
  422,
  423,
  426,
  427,
  429,
  431,
  433,
  487,
  490,
  595,
  597,
  625,
  659,
  660,
  663,
  668,
  672,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def rootSelectedEquations : Fin 53 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(8, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(31, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(43, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(44, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(46, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(49, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(50, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(51, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (61, 1)] }, { coefficient := 1, powers := [(59, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (59, 1), (61, 1)] }, { coefficient := 1, powers := [(61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (63, 1)] }, { coefficient := 1, powers := [(58, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (61, 1)] }, { coefficient := 1, powers := [(60, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (47, 1), (57, 1)] }, { coefficient := 1, powers := [(57, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(55, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (47, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (49, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (69, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(15, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (54, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (57, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (58, 1), (63, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (63, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (38, 1), (69, 1)] }, { coefficient := 1, powers := [(19, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(38, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (41, 1), (66, 1)] }, { coefficient := 1, powers := [(27, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(41, 1), (60, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (54, 1), (67, 1)] }, { coefficient := 1, powers := [(12, 1), (40, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (50, 1), (54, 1)] }, { coefficient := 1, powers := [(37, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (57, 1), (64, 1)] }, { coefficient := 1, powers := [(12, 1), (43, 1), (64, 1)] }, { coefficient := 1, powers := [(19, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(37, 1), (64, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (50, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (37, 1), (67, 1)] }, { coefficient := 1, powers := [(24, 1), (37, 1), (64, 1)] }, { coefficient := 1, powers := [(32, 1), (37, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (49, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (49, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (49, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (46, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (46, 1), (55, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(34, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(4, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(4, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(12, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(12, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(12, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

def RootSelectedZero {R : Type*} [CommRing R]
    (values : Fin 70 → R) : Prop :=
  ∀ index : Fin 53,
    eval₂Hom (Int.castRingHom R) values
      (rootSelectedEquations index).toPoly = 0

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Strict contradiction for residual case 131, branch b0. -/
theorem leafB0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (branchEquation0 : values 52 = 0)
    (branchEquation1 : values 55 = 0)
    (branchEquation2 : values 61 = 0)
    : False := by
  let childValues : Fin 70 → R := values
  apply Krenn.X5ResidualCase131.LeafB0.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation0
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation1
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation2

/-- Strict contradiction for residual case 131, branch b1. -/
theorem leafB1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (branchEquation0 : values 52 = 0)
    (branchEquation1 : values 55 = 0)
    (inverse2 : R)
    (branchEquation2 : values 61 * inverse2 - 1 = 0)
    : False := by
  let childValues : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else inverse2
  apply Krenn.X5ResidualCase131.LeafB1.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨25, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨31, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨41, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨44, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨45, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨46, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨47, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨50, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation0
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation1
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation2

/-- Strict contradiction for residual case 131, branch b2. -/
theorem leafB2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (branchEquation0 : values 52 = 0)
    (inverse1 : R)
    (branchEquation1 : values 55 * inverse1 - 1 = 0)
    (branchEquation2 : values 61 = 0)
    : False := by
  let childValues : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else inverse1
  apply Krenn.X5ResidualCase131.LeafB2.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨40, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨42, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨47, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation0
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation1
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation2

/-- Strict contradiction for residual case 131, branch b3. -/
theorem leafB3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (branchEquation0 : values 52 = 0)
    (inverse1 : R)
    (branchEquation1 : values 55 * inverse1 - 1 = 0)
    (inverse2 : R)
    (branchEquation2 : values 61 * inverse2 - 1 = 0)
    : False := by
  let childValues : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      inverse1
    else inverse2
  apply Krenn.X5ResidualCase131.LeafB3.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation1
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation2

/-- Strict contradiction for residual case 131, branch b4. -/
theorem leafB4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (inverse0 : R)
    (branchEquation0 : values 52 * inverse0 - 1 = 0)
    (branchEquation1 : values 55 = 0)
    (branchEquation2 : values 61 = 0)
    : False := by
  let childValues : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else inverse0
  apply Krenn.X5ResidualCase131.LeafB4.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨43, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨47, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation0
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation1
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation2

/-- Strict contradiction for residual case 131, branch b5. -/
theorem leafB5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (inverse0 : R)
    (branchEquation0 : values 52 * inverse0 - 1 = 0)
    (branchEquation1 : values 55 = 0)
    (inverse2 : R)
    (branchEquation2 : values 61 * inverse2 - 1 = 0)
    : False := by
  let childValues : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      inverse0
    else inverse2
  apply Krenn.X5ResidualCase131.LeafB5.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation0
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation2

/-- Strict contradiction for residual case 131, branch b6. -/
theorem leafB6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (inverse0 : R)
    (branchEquation0 : values 52 * inverse0 - 1 = 0)
    (inverse1 : R)
    (branchEquation1 : values 55 * inverse1 - 1 = 0)
    (branchEquation2 : values 61 = 0)
    : False := by
  let childValues : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      inverse0
    else inverse1
  apply Krenn.X5ResidualCase131.LeafB6.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨30, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨32, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨36, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨47, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨48, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨49, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨51, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨52, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation0
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation1
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation2

/-- Strict contradiction for residual case 131, branch b7. -/
theorem leafB7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (inverse0 : R)
    (branchEquation0 : values 52 * inverse0 - 1 = 0)
    (inverse1 : R)
    (branchEquation1 : values 55 * inverse1 - 1 = 0)
    (inverse2 : R)
    (branchEquation2 : values 61 * inverse2 - 1 = 0)
    : False := by
  let childValues : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      inverse0
    else if at1 : index.val = 71 then
      inverse1
    else inverse2
  apply Krenn.X5ResidualCase131.LeafB7.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation0
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase131.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using branchEquation2

/-- The eight frozen carrier branches exhaust the residual case. -/
theorem rootImpossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values) : False := by
  by_cases zeroC0 : values 52 = 0
  ·
    by_cases zeroC1 : values 55 = 0
    ·
      by_cases zeroC2 : values 61 = 0
      ·
        exact leafB0Impossible values rootZero zeroC0 zeroC1 zeroC2
      ·
        exact leafB1Impossible values rootZero zeroC0 zeroC1 (values 61)⁻¹ (by simp [zeroC2])
    ·
      by_cases zeroC2 : values 61 = 0
      ·
        exact leafB2Impossible values rootZero zeroC0 (values 55)⁻¹ (by simp [zeroC1]) zeroC2
      ·
        exact leafB3Impossible values rootZero zeroC0 (values 55)⁻¹ (by simp [zeroC1]) (values 61)⁻¹ (by simp [zeroC2])
  ·
    by_cases zeroC1 : values 55 = 0
    ·
      by_cases zeroC2 : values 61 = 0
      ·
        exact leafB4Impossible values rootZero (values 52)⁻¹ (by simp [zeroC0]) zeroC1 zeroC2
      ·
        exact leafB5Impossible values rootZero (values 52)⁻¹ (by simp [zeroC0]) zeroC1 (values 61)⁻¹ (by simp [zeroC2])
    ·
      by_cases zeroC2 : values 61 = 0
      ·
        exact leafB6Impossible values rootZero (values 52)⁻¹ (by simp [zeroC0]) (values 55)⁻¹ (by simp [zeroC1]) zeroC2
      ·
        exact leafB7Impossible values rootZero (values 52)⁻¹ (by simp [zeroC0]) (values 55)⁻¹ (by simp [zeroC1]) (values 61)⁻¹ (by simp [zeroC2])

theorem case131SelectedHasNoCommonZero
    (values : Fin 70 → ℂ) : ¬ RootSelectedZero values := by
  intro rootZero
  exact rootImpossible values rootZero

#print axioms Krenn.X5ResidualCase131.Tree.case131SelectedHasNoCommonZero

end Krenn.X5ResidualCase131.Tree
