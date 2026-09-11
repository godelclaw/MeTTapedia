import Mettapedia.Analysis.TruncatedKernelMoment
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.NormNum

/-! A cap includes its boundary and saturates beyond it. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.TruncatedKernelMomentTests

open MeasureTheory TruncatedKernelMoment

example : moment 2 (fun _ : ℝ ↦ (3 : ℝ)) (Measure.dirac (1 : ℝ)) = 3 := by
  norm_num [moment]

example : moment 2 (fun _ : ℝ ↦ (3 : ℝ)) (Measure.dirac (2 : ℝ)) = 6 := by
  norm_num [moment]

example : moment 2 (fun _ : ℝ ↦ (3 : ℝ)) (Measure.dirac (20 : ℝ)) = 6 := by
  norm_num [moment]

end Mettapedia.Analysis.TruncatedKernelMomentTests

#print axioms Mettapedia.Analysis.TruncatedKernelMoment.integrable_min_mul_norm
#print axioms Mettapedia.Analysis.TruncatedKernelMoment.moment_le_min
