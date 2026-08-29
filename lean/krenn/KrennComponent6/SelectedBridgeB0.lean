import KrennComponent6.Root
import KrennComponent6.SelectedLeafB0

/-! A semantic root-to-leaf bridge generated from frozen carrier data. -/

namespace Krenn.Component6.SelectedBridgeB0

open Krenn.SparseCertificate
open MvPolynomial

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem selectedLeafB0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component6.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  let values1 : Fin 59 → R := values
  apply Krenn.Component6.SelectedLeafB0.selectedHasNoCommonZero values1
  intro index
  fin_cases index
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨2, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨3, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨4, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨5, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨10, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨16, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨17, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨18, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨20, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨22, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨28, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨34, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨35, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨97, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨171, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨173, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨177, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨184, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨185, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨193, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨195, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨199, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨202, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨203, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨204, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨205, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨209, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨212, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨213, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨214, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨261, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨265, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨310, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨336, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨369, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨370, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨371, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨372, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨373, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨375, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨385, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨386, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨387, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨392, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨394, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨418, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨419, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨429, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨471, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨496, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨512, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨513, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨538, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨540, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨541, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨571, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨572, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨584, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨601, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using rootZero ⟨602, by decide⟩
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation0
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation1
  · simpa [sub_eq_add_neg, values1, Krenn.Component6.Root.rootEquations, Krenn.Component6.SelectedLeafB0.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly] using d0Equation2

#print axioms Krenn.Component6.SelectedBridgeB0.selectedLeafB0Impossible

end Krenn.Component6.SelectedBridgeB0
