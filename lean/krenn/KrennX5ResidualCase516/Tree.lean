import KrennX5ResidualCase516.LeafB0
import KrennX5ResidualCase516.LeafB1
import KrennX5ResidualCase516.LeafB2
import KrennX5ResidualCase516.LeafB3
import KrennX5ResidualCase516.LeafB4
import KrennX5ResidualCase516.LeafB5
import KrennX5ResidualCase516.LeafB6
import KrennX5ResidualCase516.LeafB7

namespace Krenn.X5ResidualCase516.Tree

open Krenn.SparseCertificate
open MvPolynomial

def rootVariableCount : Nat := 70

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def rootSelectedIndices : Fin 17 → Fin 675 := ![
  42,
  43,
  44,
  45,
  46,
  47,
  421,
  422,
  423,
  424,
  425,
  426,
  660,
  664,
  671,
  673,
  674
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def rootSelectedEquations : Fin 17 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(48, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(47, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (66, 1)] }, { coefficient := 1, powers := [(40, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (60, 1)] }, { coefficient := 1, powers := [(51, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(47, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(40, 1), (69, 1)] }, { coefficient := 1, powers := [(43, 1), (66, 1)] }, { coefficient := 1, powers := [(51, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (48, 1), (63, 1)] }, { coefficient := 1, powers := [(18, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(26, 1), (48, 1), (54, 1)] }, { coefficient := 1, powers := [(54, 1), (69, 1)] }, { coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := 1, powers := [(60, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(34, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(34, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(34, 1), (42, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (47, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (47, 1), (56, 1)] }, { coefficient := 1, powers := [(27, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(27, 1), (47, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (54, 1), (69, 1)] }, { coefficient := 1, powers := [(7, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(7, 1), (60, 1), (63, 1)] }, { coefficient := 1, powers := [(15, 1), (40, 1), (69, 1)] }, { coefficient := 1, powers := [(15, 1), (43, 1), (66, 1)] }, { coefficient := 1, powers := [(15, 1), (51, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (37, 1), (69, 1)] }, { coefficient := 1, powers := [(23, 1), (43, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (66, 1)] }, { coefficient := 1, powers := [(31, 1), (40, 1), (60, 1)] }, { coefficient := 1, powers := [(31, 1), (51, 1), (54, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (63, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(34, 1), (43, 1), (54, 1)] }, { coefficient := -1, powers := [] }]
]

def RootSelectedZero {R : Type*} [CommRing R]
    (values : Fin 70 → R) : Prop :=
  ∀ index : Fin 17,
    eval₂Hom (Int.castRingHom R) values
      (rootSelectedEquations index).toPoly = 0

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Strict contradiction for residual case 516, branch b0. -/
theorem leafB0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (branchEquation0 : values 52 = 0)
    (branchEquation1 : values 55 = 0)
    (branchEquation2 : values 61 = 0)
    : False := by
  let childValues : Fin 70 → R := values
  apply Krenn.X5ResidualCase516.LeafB0.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩

/-- Strict contradiction for residual case 516, branch b1. -/
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
  apply Krenn.X5ResidualCase516.LeafB1.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩

/-- Strict contradiction for residual case 516, branch b2. -/
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
  apply Krenn.X5ResidualCase516.LeafB2.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩

/-- Strict contradiction for residual case 516, branch b3. -/
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
  apply Krenn.X5ResidualCase516.LeafB3.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩

/-- Strict contradiction for residual case 516, branch b4. -/
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
  apply Krenn.X5ResidualCase516.LeafB4.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩

/-- Strict contradiction for residual case 516, branch b5. -/
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
  apply Krenn.X5ResidualCase516.LeafB5.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩

/-- Strict contradiction for residual case 516, branch b6. -/
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
  apply Krenn.X5ResidualCase516.LeafB6.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩

/-- Strict contradiction for residual case 516, branch b7. -/
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
  apply Krenn.X5ResidualCase516.LeafB7.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootSelectedEquations, Krenn.X5ResidualCase516.LeafB7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩

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

theorem case516SelectedHasNoCommonZero
    (values : Fin 70 → ℂ) : ¬ RootSelectedZero values := by
  intro rootZero
  exact rootImpossible values rootZero

#print axioms Krenn.X5ResidualCase516.Tree.case516SelectedHasNoCommonZero

end Krenn.X5ResidualCase516.Tree
