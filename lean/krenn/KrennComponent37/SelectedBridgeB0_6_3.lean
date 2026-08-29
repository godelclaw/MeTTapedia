import KrennComponent37.Root
import KrennComponent37.SelectedLeafB0_6_3

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component37.SelectedBridgeB0_6_3

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0_6_3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 62 → R)
    (rootZero : Krenn.Component37.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    (d2Equation0 : values 56 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 57 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 58 * d2Inverse2 - 1 = 0)
    : False := by
  let values1 : Fin 62 → R := values
  let values2 : Fin 64 → R := fun index =>
    if inside : index.val < 62 then
      values1 ⟨index.val, inside⟩
    else if at0 : index.val = 62 then
      d1Inverse0
    else d1Inverse1
  let values3 : Fin 66 → R := fun index =>
    if inside : index.val < 64 then
      values2 ⟨index.val, inside⟩
    else if at0 : index.val = 64 then
      d2Inverse1
    else d2Inverse2
  apply Krenn.Component37.SelectedLeafB0_6_3.selectedHasNoCommonZero values3
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨8, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨19, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨70, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨71, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨79, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨149, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨151, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨152, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨170, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨178, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨179, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨180, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨183, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨221, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨230, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨231, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨294, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨301, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨303, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨312, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨313, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨315, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨316, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨414, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨424, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨433, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨438, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨440, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨446, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨447, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨450, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨458, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨461, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨463, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨465, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨466, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨470, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨472, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨473, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨474, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨475, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨476, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨501, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨527, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨568, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨570, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨581, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨583, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨586, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨603, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨608, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨612, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨617, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨628, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨645, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨655, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨657, by decide⟩
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d1Equation2
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation0
  · simpa [sub_eq_add_neg, values1, values2, values3, Krenn.Component37.Root.rootEquations, Krenn.Component37.SelectedLeafB0_6_3.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d2Equation2

#print axioms Krenn.Component37.SelectedBridgeB0_6_3.selectedLeafB0_6_3Impossible

end Krenn.Component37.SelectedBridgeB0_6_3
