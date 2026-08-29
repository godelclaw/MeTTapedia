import KrennCarrierSplitReflection
import KrennComponent46LeafB0
import KrennComponent46LeafB1
import KrennComponent46LeafB2
import KrennComponent46LeafB3
import KrennComponent46LeafB4_0
import KrennComponent46LeafB4_1
import KrennComponent46LeafB4_2
import KrennComponent46LeafB4_3
import KrennComponent46LeafB4_4
import KrennComponent46LeafB4_5
import KrennComponent46LeafB4_6
import KrennComponent46LeafB4_7
import KrennComponent46LeafB5
import KrennComponent46LeafB6
import KrennComponent46LeafB7

/-! Kernel assembly of the complete component-46 carrier tree. -/

namespace Krenn.Component46.Tree

open Krenn.SparseCertificate
open MvPolynomial

def rootEquations : Fin 640 → SparsePoly (Fin 61) :=
  fun index => LeafB0.parentEquations ⟨index.val, by omega⟩

def RootCommonZero {R : Type*} [CommRing R]
    (values : Fin 61 → R) : Prop :=
  ∀ index, eval₂Hom (Int.castRingHom R) values
    (rootEquations index).toPoly = 0

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Frozen compatibility and contradiction for leaf `b0`. -/
theorem leafB0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values)
    (rootEquation0 : values 0 = 0) (rootEquation1 : values 1 = 0) (rootEquation2 : values 2 = 0)
    : False := by
  let childValues : Fin 61 → R := values
  apply LeafB0.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB0.selectedEquations, LeafB0.selectedIndices, LeafB0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB0.selectedEquations, LeafB0.selectedIndices, LeafB0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB0.selectedEquations, LeafB0.selectedIndices, LeafB0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB0.selectedEquations, LeafB0.selectedIndices, LeafB0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB0.selectedEquations, LeafB0.selectedIndices, LeafB0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨216, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB0.selectedEquations, LeafB0.selectedIndices, LeafB0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨229, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB0.selectedEquations, LeafB0.selectedIndices, LeafB0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB0.selectedEquations, LeafB0.selectedIndices, LeafB0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB0.selectedEquations, LeafB0.selectedIndices, LeafB0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB0.selectedEquations, LeafB0.selectedIndices, LeafB0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB0.selectedEquations, LeafB0.selectedIndices, LeafB0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB0.selectedEquations, LeafB0.selectedIndices, LeafB0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB0.selectedEquations, LeafB0.selectedIndices, LeafB0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation0
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB0.selectedEquations, LeafB0.selectedIndices, LeafB0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation2

/-- Frozen compatibility and contradiction for leaf `b1`. -/
theorem leafB1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values)
    (rootEquation0 : values 0 = 0) (rootEquation1 : values 1 = 0) (rootInverse2 : R) (rootEquation2 : values 2 * rootInverse2 - 1 = 0)
    : False := by
  let childValues : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else rootInverse2
  apply LeafB1.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨216, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨220, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨229, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨485, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨494, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB1.selectedEquations, LeafB1.selectedIndices, LeafB1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation0

/-- Frozen compatibility and contradiction for leaf `b2`. -/
theorem leafB2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values)
    (rootEquation0 : values 0 = 0) (rootInverse1 : R) (rootEquation1 : values 1 * rootInverse1 - 1 = 0) (rootEquation2 : values 2 = 0)
    : False := by
  let childValues : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else rootInverse1
  apply LeafB2.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB2.selectedEquations, LeafB2.selectedIndices, LeafB2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨191, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB2.selectedEquations, LeafB2.selectedIndices, LeafB2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB2.selectedEquations, LeafB2.selectedIndices, LeafB2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB2.selectedEquations, LeafB2.selectedIndices, LeafB2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB2.selectedEquations, LeafB2.selectedIndices, LeafB2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨213, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB2.selectedEquations, LeafB2.selectedIndices, LeafB2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨216, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB2.selectedEquations, LeafB2.selectedIndices, LeafB2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB2.selectedEquations, LeafB2.selectedIndices, LeafB2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB2.selectedEquations, LeafB2.selectedIndices, LeafB2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB2.selectedEquations, LeafB2.selectedIndices, LeafB2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB2.selectedEquations, LeafB2.selectedIndices, LeafB2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB2.selectedEquations, LeafB2.selectedIndices, LeafB2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB2.selectedEquations, LeafB2.selectedIndices, LeafB2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB2.selectedEquations, LeafB2.selectedIndices, LeafB2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation0
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB2.selectedEquations, LeafB2.selectedIndices, LeafB2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation2

/-- Frozen compatibility and contradiction for leaf `b3`. -/
theorem leafB3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values)
    (rootEquation0 : values 0 = 0) (rootInverse1 : R) (rootEquation1 : values 1 * rootInverse1 - 1 = 0) (rootInverse2 : R) (rootEquation2 : values 2 * rootInverse2 - 1 = 0)
    : False := by
  let childValues : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      rootInverse1
    else rootInverse2
  apply LeafB3.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB3.selectedEquations, LeafB3.selectedIndices, LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB3.selectedEquations, LeafB3.selectedIndices, LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨43, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB3.selectedEquations, LeafB3.selectedIndices, LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB3.selectedEquations, LeafB3.selectedIndices, LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB3.selectedEquations, LeafB3.selectedIndices, LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB3.selectedEquations, LeafB3.selectedIndices, LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨216, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB3.selectedEquations, LeafB3.selectedIndices, LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨220, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB3.selectedEquations, LeafB3.selectedIndices, LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨229, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB3.selectedEquations, LeafB3.selectedIndices, LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB3.selectedEquations, LeafB3.selectedIndices, LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB3.selectedEquations, LeafB3.selectedIndices, LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB3.selectedEquations, LeafB3.selectedIndices, LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB3.selectedEquations, LeafB3.selectedIndices, LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB3.selectedEquations, LeafB3.selectedIndices, LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB3.selectedEquations, LeafB3.selectedIndices, LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation0
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB3.selectedEquations, LeafB3.selectedIndices, LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation1
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB3.selectedEquations, LeafB3.selectedIndices, LeafB3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation2

/-- Frozen compatibility and contradiction for leaf `b4.0`. -/
theorem leafB4_0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values)
    (rootInverse0 : R) (rootEquation0 : values 0 * rootInverse0 - 1 = 0) (rootEquation1 : values 1 = 0) (rootEquation2 : values 2 = 0)
    (secondEquation0 : values 41 = 0) (secondEquation1 : values 42 = 0) (secondEquation2 : values 43 = 0)
    : False := by
  let intermediateValues : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else rootInverse0
  let childValues : Fin 62 → R := intermediateValues
  apply LeafB4_0.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_0.selectedEquations, LeafB4_0.selectedIndices, LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_0.selectedEquations, LeafB4_0.selectedIndices, LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_0.selectedEquations, LeafB4_0.selectedIndices, LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_0.selectedEquations, LeafB4_0.selectedIndices, LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨204, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_0.selectedEquations, LeafB4_0.selectedIndices, LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_0.selectedEquations, LeafB4_0.selectedIndices, LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨240, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_0.selectedEquations, LeafB4_0.selectedIndices, LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_0.selectedEquations, LeafB4_0.selectedIndices, LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_0.selectedEquations, LeafB4_0.selectedIndices, LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_0.selectedEquations, LeafB4_0.selectedIndices, LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_0.selectedEquations, LeafB4_0.selectedIndices, LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨561, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_0.selectedEquations, LeafB4_0.selectedIndices, LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_0.selectedEquations, LeafB4_0.selectedIndices, LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation2
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_0.selectedEquations, LeafB4_0.selectedIndices, LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation1
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_0.selectedEquations, LeafB4_0.selectedIndices, LeafB4_0.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation2

/-- Frozen compatibility and contradiction for leaf `b4.1`. -/
theorem leafB4_1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values)
    (rootInverse0 : R) (rootEquation0 : values 0 * rootInverse0 - 1 = 0) (rootEquation1 : values 1 = 0) (rootEquation2 : values 2 = 0)
    (secondEquation0 : values 41 = 0) (secondEquation1 : values 42 = 0) (secondInverse2 : R) (secondEquation2 : values 43 * secondInverse2 - 1 = 0)
    : False := by
  let intermediateValues : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else rootInverse0
  let childValues : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      intermediateValues ⟨index.val, inside⟩
    else secondInverse2
  apply LeafB4_1.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨39, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨204, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨208, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨240, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨252, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨367, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨406, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨520, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨561, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨637, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation0
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation2
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation0
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation1
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_1.selectedEquations, LeafB4_1.selectedIndices, LeafB4_1.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation2

/-- Frozen compatibility and contradiction for leaf `b4.2`. -/
theorem leafB4_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values)
    (rootInverse0 : R) (rootEquation0 : values 0 * rootInverse0 - 1 = 0) (rootEquation1 : values 1 = 0) (rootEquation2 : values 2 = 0)
    (secondEquation0 : values 41 = 0) (secondInverse1 : R) (secondEquation1 : values 42 * secondInverse1 - 1 = 0) (secondEquation2 : values 43 = 0)
    : False := by
  let intermediateValues : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else rootInverse0
  let childValues : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      intermediateValues ⟨index.val, inside⟩
    else secondInverse1
  apply LeafB4_2.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨174, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨186, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨197, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨201, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨202, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨204, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨206, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨229, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨351, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨357, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨395, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨398, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨494, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨562, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨586, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨633, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨638, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation0
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation1
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation2
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_2.selectedEquations, LeafB4_2.selectedIndices, LeafB4_2.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation2

/-- Frozen compatibility and contradiction for leaf `b4.3`. -/
theorem leafB4_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values)
    (rootInverse0 : R) (rootEquation0 : values 0 * rootInverse0 - 1 = 0) (rootEquation1 : values 1 = 0) (rootEquation2 : values 2 = 0)
    (secondEquation0 : values 41 = 0) (secondInverse1 : R) (secondEquation1 : values 42 * secondInverse1 - 1 = 0) (secondInverse2 : R) (secondEquation2 : values 43 * secondInverse2 - 1 = 0)
    : False := by
  let intermediateValues : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else rootInverse0
  let childValues : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      intermediateValues ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      secondInverse1
    else secondInverse2
  apply LeafB4_3.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨62, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨174, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨200, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨202, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨229, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨240, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨252, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨354, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨367, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨586, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨587, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨611, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨618, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨637, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨638, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation0
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation1
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation2
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation0
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation1
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_3.selectedEquations, LeafB4_3.selectedIndices, LeafB4_3.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation2

/-- Frozen compatibility and contradiction for leaf `b4.4`. -/
theorem leafB4_4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values)
    (rootInverse0 : R) (rootEquation0 : values 0 * rootInverse0 - 1 = 0) (rootEquation1 : values 1 = 0) (rootEquation2 : values 2 = 0)
    (secondInverse0 : R) (secondEquation0 : values 41 * secondInverse0 - 1 = 0) (secondEquation1 : values 42 = 0) (secondEquation2 : values 43 = 0)
    : False := by
  let intermediateValues : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else rootInverse0
  let childValues : Fin 63 → R := fun index =>
    if inside : index.val < 62 then
      intermediateValues ⟨index.val, inside⟩
    else secondInverse0
  apply LeafB4_4.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_4.selectedEquations, LeafB4_4.selectedIndices, LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_4.selectedEquations, LeafB4_4.selectedIndices, LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_4.selectedEquations, LeafB4_4.selectedIndices, LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_4.selectedEquations, LeafB4_4.selectedIndices, LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨204, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_4.selectedEquations, LeafB4_4.selectedIndices, LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_4.selectedEquations, LeafB4_4.selectedIndices, LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨240, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_4.selectedEquations, LeafB4_4.selectedIndices, LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_4.selectedEquations, LeafB4_4.selectedIndices, LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_4.selectedEquations, LeafB4_4.selectedIndices, LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_4.selectedEquations, LeafB4_4.selectedIndices, LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_4.selectedEquations, LeafB4_4.selectedIndices, LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨561, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_4.selectedEquations, LeafB4_4.selectedIndices, LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_4.selectedEquations, LeafB4_4.selectedIndices, LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation2
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_4.selectedEquations, LeafB4_4.selectedIndices, LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation1
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_4.selectedEquations, LeafB4_4.selectedIndices, LeafB4_4.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation2

/-- Frozen compatibility and contradiction for leaf `b4.5`. -/
theorem leafB4_5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values)
    (rootInverse0 : R) (rootEquation0 : values 0 * rootInverse0 - 1 = 0) (rootEquation1 : values 1 = 0) (rootEquation2 : values 2 = 0)
    (secondInverse0 : R) (secondEquation0 : values 41 * secondInverse0 - 1 = 0) (secondEquation1 : values 42 = 0) (secondInverse2 : R) (secondEquation2 : values 43 * secondInverse2 - 1 = 0)
    : False := by
  let intermediateValues : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else rootInverse0
  let childValues : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      intermediateValues ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      secondInverse0
    else secondInverse2
  apply LeafB4_5.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨204, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨240, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨330, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨387, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨561, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation0
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation2
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation0
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation1
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_5.selectedEquations, LeafB4_5.selectedIndices, LeafB4_5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation2

/-- Frozen compatibility and contradiction for leaf `b4.6`. -/
theorem leafB4_6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values)
    (rootInverse0 : R) (rootEquation0 : values 0 * rootInverse0 - 1 = 0) (rootEquation1 : values 1 = 0) (rootEquation2 : values 2 = 0)
    (secondInverse0 : R) (secondEquation0 : values 41 * secondInverse0 - 1 = 0) (secondInverse1 : R) (secondEquation1 : values 42 * secondInverse1 - 1 = 0) (secondEquation2 : values 43 = 0)
    : False := by
  let intermediateValues : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else rootInverse0
  let childValues : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      intermediateValues ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      secondInverse0
    else secondInverse1
  apply LeafB4_6.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨6, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨26, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨167, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨174, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨175, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨186, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨197, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨201, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨202, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨204, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨229, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨330, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨351, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨357, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨395, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨562, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨586, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨633, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨638, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation0
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation1
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation2
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation0
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_6.selectedEquations, LeafB4_6.selectedIndices, LeafB4_6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation2

/-- Frozen compatibility and contradiction for leaf `b4.7`. -/
theorem leafB4_7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values)
    (rootInverse0 : R) (rootEquation0 : values 0 * rootInverse0 - 1 = 0) (rootEquation1 : values 1 = 0) (rootEquation2 : values 2 = 0)
    (secondInverse0 : R) (secondEquation0 : values 41 * secondInverse0 - 1 = 0) (secondInverse1 : R) (secondEquation1 : values 42 * secondInverse1 - 1 = 0) (secondInverse2 : R) (secondEquation2 : values 43 * secondInverse2 - 1 = 0)
    : False := by
  let intermediateValues : Fin 62 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else rootInverse0
  let childValues : Fin 65 → R := fun index =>
    if inside : index.val < 62 then
      intermediateValues ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      secondInverse0
    else if at1 : index.val = 63 then
      secondInverse1
    else secondInverse2
  apply LeafB4_7.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨7, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨14, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨174, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨200, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨202, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨211, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨229, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨240, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨252, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨354, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨367, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨410, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨478, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨586, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨587, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨611, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨618, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨637, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨638, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation0
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation1
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation2
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation0
  · simpa [sub_eq_add_neg, childValues, intermediateValues, rootEquations, LeafB0.parentEquations, LeafB4_7.selectedEquations, LeafB4_7.selectedIndices, LeafB4_7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using secondEquation2

/-- Frozen compatibility and contradiction for leaf `b5`. -/
theorem leafB5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values)
    (rootInverse0 : R) (rootEquation0 : values 0 * rootInverse0 - 1 = 0) (rootEquation1 : values 1 = 0) (rootInverse2 : R) (rootEquation2 : values 2 * rootInverse2 - 1 = 0)
    : False := by
  let childValues : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      rootInverse0
    else rootInverse2
  apply LeafB5.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨42, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨166, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨197, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨202, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨216, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨220, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨240, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨327, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨357, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨363, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨365, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨444, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨467, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨562, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨574, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨587, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation0
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB5.selectedEquations, LeafB5.selectedIndices, LeafB5.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation2

/-- Frozen compatibility and contradiction for leaf `b6`. -/
theorem leafB6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values)
    (rootInverse0 : R) (rootEquation0 : values 0 * rootInverse0 - 1 = 0) (rootInverse1 : R) (rootEquation1 : values 1 * rootInverse1 - 1 = 0) (rootEquation2 : values 2 = 0)
    : False := by
  let childValues : Fin 63 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      rootInverse0
    else rootInverse1
  apply LeafB6.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨9, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨11, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨13, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨27, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨29, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨33, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨38, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨54, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨162, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨163, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨164, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨165, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨168, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨169, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨172, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨174, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨181, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨186, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨197, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨200, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨201, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨202, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨204, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨207, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨210, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨216, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨227, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨228, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨229, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨240, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨351, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨354, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨357, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨359, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨360, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨368, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨373, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨397, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨398, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨400, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨406, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨444, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨461, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨464, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨480, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨481, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨494, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨507, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨515, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨524, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨525, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨561, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨562, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨573, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨582, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨585, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨586, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨609, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨618, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨633, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨637, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨638, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation0
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation1
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB6.selectedEquations, LeafB6.selectedIndices, LeafB6.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation2

/-- Frozen compatibility and contradiction for leaf `b7`. -/
theorem leafB7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values)
    (rootInverse0 : R) (rootEquation0 : values 0 * rootInverse0 - 1 = 0) (rootInverse1 : R) (rootEquation1 : values 1 * rootInverse1 - 1 = 0) (rootInverse2 : R) (rootEquation2 : values 2 * rootInverse2 - 1 = 0)
    : False := by
  let childValues : Fin 64 → R := fun index =>
    if inside : index.val < 61 then
      values ⟨index.val, inside⟩
    else if at0 : index.val = 61 then
      rootInverse0
    else if at1 : index.val = 62 then
      rootInverse1
    else rootInverse2
  apply LeafB7.selectedHasNoCommonZero childValues
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨12, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨15, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨21, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨23, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨24, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨37, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨40, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨165, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨197, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨220, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨350, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨352, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨357, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨361, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨362, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨365, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨434, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨494, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨639, by decide⟩
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation0
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation1
  · simpa [sub_eq_add_neg, childValues, rootEquations, LeafB0.parentEquations, LeafB7.selectedEquations, LeafB7.selectedIndices, LeafB7.parentEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootEquation2

/-- The root `b4` chart is exhausted by its second carrier cube. -/
theorem rootB4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) (rootZero : RootCommonZero values)
    (rootInverse0 : R) (rootEquation0 : values 0 * rootInverse0 - 1 = 0)
    (rootEquation1 : values 1 = 0) (rootEquation2 : values 2 = 0) : False := by
  by_cases zeroSecond0 : values 41 = 0
  ·
    by_cases zeroSecond1 : values 42 = 0
    ·
      by_cases zeroSecond2 : values 43 = 0
      · exact leafB4_0Impossible values rootZero rootInverse0 rootEquation0 rootEquation1 rootEquation2 zeroSecond0 zeroSecond1 zeroSecond2
      · exact leafB4_1Impossible values rootZero rootInverse0 rootEquation0 rootEquation1 rootEquation2 zeroSecond0 zeroSecond1 (values 43)⁻¹ (by simp [zeroSecond2])
    ·
      by_cases zeroSecond2 : values 43 = 0
      · exact leafB4_2Impossible values rootZero rootInverse0 rootEquation0 rootEquation1 rootEquation2 zeroSecond0 (values 42)⁻¹ (by simp [zeroSecond1]) zeroSecond2
      · exact leafB4_3Impossible values rootZero rootInverse0 rootEquation0 rootEquation1 rootEquation2 zeroSecond0 (values 42)⁻¹ (by simp [zeroSecond1]) (values 43)⁻¹ (by simp [zeroSecond2])
  ·
    by_cases zeroSecond1 : values 42 = 0
    ·
      by_cases zeroSecond2 : values 43 = 0
      · exact leafB4_4Impossible values rootZero rootInverse0 rootEquation0 rootEquation1 rootEquation2 (values 41)⁻¹ (by simp [zeroSecond0]) zeroSecond1 zeroSecond2
      · exact leafB4_5Impossible values rootZero rootInverse0 rootEquation0 rootEquation1 rootEquation2 (values 41)⁻¹ (by simp [zeroSecond0]) zeroSecond1 (values 43)⁻¹ (by simp [zeroSecond2])
    ·
      by_cases zeroSecond2 : values 43 = 0
      · exact leafB4_6Impossible values rootZero rootInverse0 rootEquation0 rootEquation1 rootEquation2 (values 41)⁻¹ (by simp [zeroSecond0]) (values 42)⁻¹ (by simp [zeroSecond1]) zeroSecond2
      · exact leafB4_7Impossible values rootZero rootInverse0 rootEquation0 rootEquation1 rootEquation2 (values 41)⁻¹ (by simp [zeroSecond0]) (values 42)⁻¹ (by simp [zeroSecond1]) (values 43)⁻¹ (by simp [zeroSecond2])

/-- The complete frozen component-46 root family has no common zero
over any characteristic-zero field. -/
theorem component46HasNoCommonZero {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R) : ¬ RootCommonZero values := by
  intro rootZero
  by_cases zeroRoot0 : values 0 = 0
  · by_cases zeroRoot1 : values 1 = 0
    · by_cases zeroRoot2 : values 2 = 0
      · exact leafB0Impossible values rootZero zeroRoot0 zeroRoot1 zeroRoot2
      · exact leafB1Impossible values rootZero zeroRoot0 zeroRoot1
          (values 2)⁻¹ (by simp [zeroRoot2])
    · by_cases zeroRoot2 : values 2 = 0
      · exact leafB2Impossible values rootZero zeroRoot0
          (values 1)⁻¹ (by simp [zeroRoot1]) zeroRoot2
      · exact leafB3Impossible values rootZero zeroRoot0
          (values 1)⁻¹ (by simp [zeroRoot1])
          (values 2)⁻¹ (by simp [zeroRoot2])
  · by_cases zeroRoot1 : values 1 = 0
    · by_cases zeroRoot2 : values 2 = 0
      · exact rootB4Impossible values rootZero
          (values 0)⁻¹ (by simp [zeroRoot0]) zeroRoot1 zeroRoot2
      · exact leafB5Impossible values rootZero
          (values 0)⁻¹ (by simp [zeroRoot0]) zeroRoot1
          (values 2)⁻¹ (by simp [zeroRoot2])
    · by_cases zeroRoot2 : values 2 = 0
      · exact leafB6Impossible values rootZero
          (values 0)⁻¹ (by simp [zeroRoot0])
          (values 1)⁻¹ (by simp [zeroRoot1]) zeroRoot2
      · exact leafB7Impossible values rootZero
          (values 0)⁻¹ (by simp [zeroRoot0])
          (values 1)⁻¹ (by simp [zeroRoot1])
          (values 2)⁻¹ (by simp [zeroRoot2])

#print axioms Krenn.Component46.Tree.component46HasNoCommonZero

end Krenn.Component46.Tree
