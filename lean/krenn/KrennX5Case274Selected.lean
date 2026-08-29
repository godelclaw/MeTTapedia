import KrennX5Case274Tree.LeafB0_0
import KrennX5Case274Tree.LeafB0_1
import KrennX5Case274Tree.LeafB0_2
import KrennX5Case274Tree.LeafB0_3
import KrennX5Case274Tree.LeafB0_4
import KrennX5Case274Tree.LeafB0_5
import KrennX5Case274Tree.LeafB0_6
import KrennX5Case274Tree.LeafB0_7
import KrennX5Case274Tree.LeafB1_0
import KrennX5Case274Tree.LeafB1_1
import KrennX5Case274Tree.LeafB1_2
import KrennX5Case274Tree.LeafB1_3
import KrennX5Case274Tree.LeafB1_4
import KrennX5Case274Tree.LeafB1_5
import KrennX5Case274Tree.LeafB1_6
import KrennX5Case274Tree.LeafB1_7
import KrennX5Case274Tree.LeafB2_0
import KrennX5Case274Tree.LeafB2_1
import KrennX5Case274Tree.LeafB2_2
import KrennX5Case274Tree.LeafB2_3
import KrennX5Case274Tree.LeafB2_4
import KrennX5Case274Tree.LeafB2_5
import KrennX5Case274Tree.LeafB2_6
import KrennX5Case274Tree.LeafB2_7
import KrennX5Case274Tree.LeafB3_0
import KrennX5Case274Tree.LeafB3_1
import KrennX5Case274Tree.LeafB3_2
import KrennX5Case274Tree.LeafB3_3
import KrennX5Case274Tree.LeafB3_4
import KrennX5Case274Tree.LeafB3_5
import KrennX5Case274Tree.LeafB3_6
import KrennX5Case274Tree.LeafB3_7
import KrennX5Case274Tree.LeafB4_0
import KrennX5Case274Tree.LeafB4_1
import KrennX5Case274Tree.LeafB4_2
import KrennX5Case274Tree.LeafB4_3
import KrennX5Case274Tree.LeafB4_4
import KrennX5Case274Tree.LeafB4_5
import KrennX5Case274Tree.LeafB4_6
import KrennX5Case274Tree.LeafB4_7
import KrennX5Case274Tree.LeafB5_0
import KrennX5Case274Tree.LeafB5_1
import KrennX5Case274Tree.LeafB5_2
import KrennX5Case274Tree.LeafB5_3
import KrennX5Case274Tree.LeafB5_4
import KrennX5Case274Tree.LeafB5_5
import KrennX5Case274Tree.LeafB5_6
import KrennX5Case274Tree.LeafB5_7
import KrennX5Case274Tree.LeafB6_0
import KrennX5Case274Tree.LeafB6_1
import KrennX5Case274Tree.LeafB6_2
import KrennX5Case274Tree.LeafB6_3
import KrennX5Case274Tree.LeafB6_4
import KrennX5Case274Tree.LeafB6_5
import KrennX5Case274Tree.LeafB6_6
import KrennX5Case274Tree.LeafB6_7
import KrennX5Case274Tree.LeafB7_0
import KrennX5Case274Tree.LeafB7_1
import KrennX5Case274Tree.LeafB7_2
import KrennX5Case274Tree.LeafB7_3
import KrennX5Case274Tree.LeafB7_4
import KrennX5Case274Tree.LeafB7_5
import KrennX5Case274Tree.LeafB7_6
import KrennX5Case274Tree.LeafB7_7

namespace Krenn.X5Case274Selected

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def rootSelectedIndices : Fin 18 → Fin 675 := ![
  0,
  39,
  41,
  43,
  45,
  47,
  49,
  421,
  422,
  423,
  424,
  425,
  426,
  659,
  661,
  671,
  672,
  673
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def rootSelectedEquations : Fin 18 → SparsePoly (Fin 70) := ![
  [{ coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(45, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(47, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (64, 1)] }, { coefficient := 1, powers := [(38, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (58, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (65, 1)] }, { coefficient := 1, powers := [(39, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (59, 1)] }, { coefficient := 1, powers := [(48, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (67, 1)] }, { coefficient := 1, powers := [(41, 1), (64, 1)] }, { coefficient := 1, powers := [(44, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (68, 1)] }, { coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := 1, powers := [(48, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (47, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (47, 1), (52, 1)] }, { coefficient := 1, powers := [(52, 1), (67, 1)] }, { coefficient := 1, powers := [(55, 1), (64, 1)] }, { coefficient := 1, powers := [(58, 1), (61, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (45, 1), (61, 1)] }, { coefficient := 1, powers := [(18, 1), (45, 1), (55, 1)] }, { coefficient := 1, powers := [(27, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(33, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(33, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(33, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(9, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(17, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(17, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(17, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(25, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(53, 1), (68, 1)] }, { coefficient := 1, powers := [(56, 1), (65, 1)] }, { coefficient := 1, powers := [(59, 1), (62, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (55, 1), (64, 1)] }, { coefficient := 1, powers := [(0, 1), (58, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (38, 1), (67, 1)] }, { coefficient := 1, powers := [(8, 1), (41, 1), (64, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (61, 1)] }, { coefficient := 1, powers := [(16, 1), (35, 1), (67, 1)] }, { coefficient := 1, powers := [(16, 1), (41, 1), (58, 1)] }, { coefficient := 1, powers := [(16, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (35, 1), (64, 1)] }, { coefficient := 1, powers := [(24, 1), (38, 1), (58, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (52, 1)] }, { coefficient := 1, powers := [(32, 1), (35, 1), (61, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(32, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(3, 1), (53, 1), (68, 1)] }, { coefficient := 1, powers := [(3, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (59, 1), (62, 1)] }, { coefficient := 1, powers := [(11, 1), (39, 1), (68, 1)] }, { coefficient := 1, powers := [(11, 1), (42, 1), (65, 1)] }, { coefficient := 1, powers := [(11, 1), (48, 1), (62, 1)] }, { coefficient := 1, powers := [(19, 1), (36, 1), (68, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1), (59, 1)] }, { coefficient := 1, powers := [(19, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(28, 1), (36, 1), (65, 1)] }, { coefficient := 1, powers := [(28, 1), (39, 1), (59, 1)] }, { coefficient := 1, powers := [(28, 1), (48, 1), (53, 1)] }, { coefficient := 1, powers := [(33, 1), (36, 1), (62, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(33, 1), (42, 1), (53, 1)] }, { coefficient := -1, powers := [] }]
]

def RootSelectedZero {R : Type*} [CommRing R]
    (values : Fin 70 → R) : Prop :=
  ∀ index : Fin 18,
    eval₂Hom (Int.castRingHom R) values
      (rootSelectedEquations index).toPoly = 0

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Frozen compatibility and contradiction for terminal chart `b0.0`. -/
theorem leafB00Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 70 → R := values
  let values2 : Fin 70 → R := values1
  apply Krenn.X5Case274Tree.LeafB0_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b0.1`. -/
theorem leafB01Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 70 → R := values
  let values2 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB0_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b0.2`. -/
theorem leafB02Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 70 → R := values
  let values2 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.X5Case274Tree.LeafB0_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0

/-- Frozen compatibility and contradiction for terminal chart `b0.3`. -/
theorem leafB03Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 70 → R := values
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB0_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0

/-- Frozen compatibility and contradiction for terminal chart `b0.4`. -/
theorem leafB04Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 70 → R := values
  let values2 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.X5Case274Tree.LeafB0_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b0.5`. -/
theorem leafB05Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 70 → R := values
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB0_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b0.6`. -/
theorem leafB06Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 70 → R := values
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.X5Case274Tree.LeafB0_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1

/-- Frozen compatibility and contradiction for terminal chart `b0.7`. -/
theorem leafB07Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 70 → R := values
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d1Inverse0
    else if at1 : index.val = 71 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB0_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB0_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1

/-- Frozen compatibility and contradiction for terminal chart `b1.0`. -/
theorem leafB10Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 71 → R := values1
  apply Krenn.X5Case274Tree.LeafB1_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b1.1`. -/
theorem leafB11Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB1_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b1.2`. -/
theorem leafB12Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.X5Case274Tree.LeafB1_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0

/-- Frozen compatibility and contradiction for terminal chart `b1.3`. -/
theorem leafB13Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB1_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0

/-- Frozen compatibility and contradiction for terminal chart `b1.4`. -/
theorem leafB14Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.X5Case274Tree.LeafB1_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b1.5`. -/
theorem leafB15Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB1_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b1.6`. -/
theorem leafB16Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.X5Case274Tree.LeafB1_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1

/-- Frozen compatibility and contradiction for terminal chart `b1.7`. -/
theorem leafB17Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse2
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse0
    else if at1 : index.val = 72 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB1_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB1_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1

/-- Frozen compatibility and contradiction for terminal chart `b2.0`. -/
theorem leafB20Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 71 → R := values1
  apply Krenn.X5Case274Tree.LeafB2_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b2.1`. -/
theorem leafB21Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB2_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b2.2`. -/
theorem leafB22Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.X5Case274Tree.LeafB2_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0

/-- Frozen compatibility and contradiction for terminal chart `b2.3`. -/
theorem leafB23Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB2_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0

/-- Frozen compatibility and contradiction for terminal chart `b2.4`. -/
theorem leafB24Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.X5Case274Tree.LeafB2_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b2.5`. -/
theorem leafB25Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB2_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b2.6`. -/
theorem leafB26Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.X5Case274Tree.LeafB2_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0

/-- Frozen compatibility and contradiction for terminal chart `b2.7`. -/
theorem leafB27Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse1
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse0
    else if at1 : index.val = 72 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB2_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB2_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0

/-- Frozen compatibility and contradiction for terminal chart `b3.0`. -/
theorem leafB30Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 72 → R := values1
  apply Krenn.X5Case274Tree.LeafB3_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b3.1`. -/
theorem leafB31Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB3_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b3.2`. -/
theorem leafB32Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.X5Case274Tree.LeafB3_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0

/-- Frozen compatibility and contradiction for terminal chart `b3.3`. -/
theorem leafB33Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB3_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0

/-- Frozen compatibility and contradiction for terminal chart `b3.4`. -/
theorem leafB34Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.X5Case274Tree.LeafB3_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b3.5`. -/
theorem leafB35Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB3_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b3.6`. -/
theorem leafB36Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.X5Case274Tree.LeafB3_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0

/-- Frozen compatibility and contradiction for terminal chart `b3.7`. -/
theorem leafB37Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 75 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse0
    else if at1 : index.val = 73 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB3_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB3_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0

/-- Frozen compatibility and contradiction for terminal chart `b4.0`. -/
theorem leafB40Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 71 → R := values1
  apply Krenn.X5Case274Tree.LeafB4_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b4.1`. -/
theorem leafB41Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB4_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b4.2`. -/
theorem leafB42Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.X5Case274Tree.LeafB4_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0

/-- Frozen compatibility and contradiction for terminal chart `b4.3`. -/
theorem leafB43Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB4_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0

/-- Frozen compatibility and contradiction for terminal chart `b4.4`. -/
theorem leafB44Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 72 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.X5Case274Tree.LeafB4_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b4.5`. -/
theorem leafB45Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB4_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b4.6`. -/
theorem leafB46Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.X5Case274Tree.LeafB4_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1

/-- Frozen compatibility and contradiction for terminal chart `b4.7`. -/
theorem leafB47Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 71 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else d0Inverse0
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 71 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 71 then
      d1Inverse0
    else if at1 : index.val = 72 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB4_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB4_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1

/-- Frozen compatibility and contradiction for terminal chart `b5.0`. -/
theorem leafB50Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 72 → R := values1
  apply Krenn.X5Case274Tree.LeafB5_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b5.1`. -/
theorem leafB51Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB5_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b5.2`. -/
theorem leafB52Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.X5Case274Tree.LeafB5_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0

/-- Frozen compatibility and contradiction for terminal chart `b5.3`. -/
theorem leafB53Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB5_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0

/-- Frozen compatibility and contradiction for terminal chart `b5.4`. -/
theorem leafB54Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.X5Case274Tree.LeafB5_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b5.5`. -/
theorem leafB55Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB5_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b5.6`. -/
theorem leafB56Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.X5Case274Tree.LeafB5_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1

/-- Frozen compatibility and contradiction for terminal chart `b5.7`. -/
theorem leafB57Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse2
  let values2 : Fin 75 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse0
    else if at1 : index.val = 73 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB5_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB5_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1

/-- Frozen compatibility and contradiction for terminal chart `b6.0`. -/
theorem leafB60Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 72 → R := values1
  apply Krenn.X5Case274Tree.LeafB6_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b6.1`. -/
theorem leafB61Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB6_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b6.2`. -/
theorem leafB62Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.X5Case274Tree.LeafB6_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0

/-- Frozen compatibility and contradiction for terminal chart `b6.3`. -/
theorem leafB63Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB6_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0

/-- Frozen compatibility and contradiction for terminal chart `b6.4`. -/
theorem leafB64Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 73 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.X5Case274Tree.LeafB6_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b6.5`. -/
theorem leafB65Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB6_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b6.6`. -/
theorem leafB66Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.X5Case274Tree.LeafB6_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩

/-- Frozen compatibility and contradiction for terminal chart `b6.7`. -/
theorem leafB67Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 72 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else d0Inverse1
  let values2 : Fin 75 → R := fun index =>
    if inside : index.val < 72 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 72 then
      d1Inverse0
    else if at1 : index.val = 73 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB6_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB6_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩

/-- Frozen compatibility and contradiction for terminal chart `b7.0`. -/
theorem leafB70Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else if at1 : index.val = 71 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 73 → R := values1
  apply Krenn.X5Case274Tree.LeafB7_0.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b7.1`. -/
theorem leafB71Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else if at1 : index.val = 71 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 73 then
      values1 ⟨index.val, inside⟩
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB7_1.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_1.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b7.2`. -/
theorem leafB72Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else if at1 : index.val = 71 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 73 then
      values1 ⟨index.val, inside⟩
    else d1Inverse1
  apply Krenn.X5Case274Tree.LeafB7_2.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_2.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0

/-- Frozen compatibility and contradiction for terminal chart `b7.3`. -/
theorem leafB73Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Equation0 : values 55 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else if at1 : index.val = 71 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 75 → R := fun index =>
    if inside : index.val < 73 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 73 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB7_3.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0

/-- Frozen compatibility and contradiction for terminal chart `b7.4`. -/
theorem leafB74Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else if at1 : index.val = 71 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 74 → R := fun index =>
    if inside : index.val < 73 then
      values1 ⟨index.val, inside⟩
    else d1Inverse0
  apply Krenn.X5Case274Tree.LeafB7_4.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_4.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b7.5`. -/
theorem leafB75Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 56 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else if at1 : index.val = 71 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 75 → R := fun index =>
    if inside : index.val < 73 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 73 then
      d1Inverse0
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB7_5.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_5.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation1

/-- Frozen compatibility and contradiction for terminal chart `b7.6`. -/
theorem leafB76Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 57 = 0)
    : False := by
  let values1 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else if at1 : index.val = 71 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 75 → R := fun index =>
    if inside : index.val < 73 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 73 then
      d1Inverse0
    else d1Inverse1
  apply Krenn.X5Case274Tree.LeafB7_6.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_6.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩

/-- Frozen compatibility and contradiction for terminal chart `b7.7`. -/
theorem leafB77Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 55 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 56 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 57 * d1Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 73 → R := fun index =>
    if inside : index.val < 70 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 70 then
      d0Inverse0
    else if at1 : index.val = 71 then
      d0Inverse1
    else d0Inverse2
  let values2 : Fin 76 → R := fun index =>
    if inside : index.val < 73 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 73 then
      d1Inverse0
    else if at1 : index.val = 74 then
      d1Inverse1
    else d1Inverse2
  apply Krenn.X5Case274Tree.LeafB7_7.selectedHasNoCommonZero values2
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨0, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨1, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, rootSelectedEquations, Krenn.X5Case274Tree.LeafB7_7.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩

/-- Exhaustive reflection for carrier chart `b0`. -/
theorem nodeB0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    : False := by
  by_cases zeroD1C0 : values 55 = 0
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB00Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      ·
        exact leafB01Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB02Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB03Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB04Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      ·
        exact leafB05Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB06Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB07Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive reflection for carrier chart `b1`. -/
theorem nodeB1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD1C0 : values 55 = 0
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB10Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      ·
        exact leafB11Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB12Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB13Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB14Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      ·
        exact leafB15Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB16Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB17Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive reflection for carrier chart `b2`. -/
theorem nodeB2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    : False := by
  by_cases zeroD1C0 : values 55 = 0
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB20Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      ·
        exact leafB21Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB22Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB23Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB24Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      ·
        exact leafB25Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB26Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB27Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive reflection for carrier chart `b3`. -/
theorem nodeB3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD1C0 : values 55 = 0
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB30Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      ·
        exact leafB31Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB32Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB33Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB34Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      ·
        exact leafB35Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB36Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB37Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive reflection for carrier chart `b4`. -/
theorem nodeB4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Equation2 : values 7 = 0)
    : False := by
  by_cases zeroD1C0 : values 55 = 0
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB40Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      ·
        exact leafB41Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB42Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB43Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB44Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      ·
        exact leafB45Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB46Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB47Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive reflection for carrier chart `b5`. -/
theorem nodeB5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 3 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD1C0 : values 55 = 0
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB50Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      ·
        exact leafB51Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB52Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB53Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB54Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      ·
        exact leafB55Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB56Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB57Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive reflection for carrier chart `b6`. -/
theorem nodeB6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 7 = 0)
    : False := by
  by_cases zeroD1C0 : values 55 = 0
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB60Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      ·
        exact leafB61Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB62Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB63Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB64Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      ·
        exact leafB65Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB66Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB67Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive reflection for carrier chart `b7`. -/
theorem nodeB7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 3 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 7 * d0Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD1C0 : values 55 = 0
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB70Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      ·
        exact leafB71Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB72Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB73Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 56 = 0
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB74Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      ·
        exact leafB75Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 57)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 57 = 0
      ·
        exact leafB76Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      ·
        exact leafB77Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 55)⁻¹ (by simp [zeroD1C0]) (values 56)⁻¹ (by simp [zeroD1C1]) (values 57)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive reflection for carrier chart `root`. -/
theorem rootImpossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 70 → R)
    (rootZero : RootSelectedZero values)
    : False := by
  by_cases zeroD0C0 : values 0 = 0
  ·
    by_cases zeroD0C1 : values 3 = 0
    ·
      by_cases zeroD0C2 : values 7 = 0
      ·
        exact nodeB0Impossible values rootZero zeroD0C0 zeroD0C1 zeroD0C2
      ·
        exact nodeB1Impossible values rootZero zeroD0C0 zeroD0C1 (values 7)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 7 = 0
      ·
        exact nodeB2Impossible values rootZero zeroD0C0 (values 3)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      ·
        exact nodeB3Impossible values rootZero zeroD0C0 (values 3)⁻¹ (by simp [zeroD0C1]) (values 7)⁻¹ (by simp [zeroD0C2])
  ·
    by_cases zeroD0C1 : values 3 = 0
    ·
      by_cases zeroD0C2 : values 7 = 0
      ·
        exact nodeB4Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 zeroD0C2
      ·
        exact nodeB5Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 (values 7)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 7 = 0
      ·
        exact nodeB6Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 3)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      ·
        exact nodeB7Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 3)⁻¹ (by simp [zeroD0C1]) (values 7)⁻¹ (by simp [zeroD0C2])

theorem selectedHasNoCommonZero (values : Fin 70 → ℂ) :
    ¬ RootSelectedZero values := by
  intro rootZero
  exact rootImpossible values rootZero

#print axioms Krenn.X5Case274Selected.selectedHasNoCommonZero

end Krenn.X5Case274Selected
