import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Derivatives agree at a differentiable contact point -/

set_option autoImplicit false

namespace Mettapedia.Analysis.DerivativeContact

open Filter
open scoped Topology

theorem eq_of_eventually_le_of_eq {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t)
    (hle : ∀ᶠ x in 𝓝 t, f x ≤ g x) (heq : f t = g t) : f' = g' := by
  have hm : IsLocalMax (fun x ↦ f x - g x) t := by
    filter_upwards [hle] with x hx
    simpa only [heq, sub_self] using sub_nonpos.mpr hx
  exact sub_eq_zero.mp (hm.hasDerivAt_eq_zero (hf.sub hg))

end Mettapedia.Analysis.DerivativeContact
