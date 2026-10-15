import Mettapedia.GSLT.Dynamics.ChainAggregation
import Mettapedia.GSLT.Dynamics.WeightedResumptionControls

/-! # Noncommuting weights in the path aggregate -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ChainAggregation.Controls

open WeightedResumptionControls

theorem matrix_path_keeps_product_order :
    aggregate [[⟨(0 : Nat), 1, upper⟩], [⟨1, 2, lower⟩],
      [⟨2, 3, (1 : TwoByTwo)⟩], [⟨3, 4, 1⟩]] = upper * lower := by
  simp [aggregate, finish, start, step, close, JoinAggregation.groupTable_apply,
    JoinAggregation.groupSum]

theorem swapping_path_coefficients_changes_answer :
    aggregate [[⟨(0 : Nat), 1, upper⟩], [⟨1, 2, lower⟩]] ≠
    aggregate [[⟨(0 : Nat), 1, lower⟩], [⟨1, 2, upper⟩]] := by
  simpa [aggregate, finish, start, close, JoinAggregation.groupTable_apply,
    JoinAggregation.groupSum] using matrix_composition_is_ordered

end Mettapedia.GSLT.Dynamics.ChainAggregation.Controls
