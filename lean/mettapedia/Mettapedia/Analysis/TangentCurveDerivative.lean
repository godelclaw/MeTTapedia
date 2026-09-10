import Mettapedia.Analysis.LocallyLipschitz

/-!
# Derivatives along tangent curves under locally Lipschitz maps

The outer map need not be differentiable. If two differentiable curves
have the same value and velocity at a point, a derivative of its
composition with either curve is also the derivative along the other.
-/

set_option autoImplicit false

open scoped Topology
open Asymptotics

namespace LocallyLipschitz

theorem hasDerivAt_comp_of_tangent {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : LocallyLipschitz f) {g h : ℝ → E} {v : E} {w : F} {t : ℝ}
    (hg : HasDerivAt g v t) (hh : HasDerivAt h v t) (heq : g t = h t)
    (hfg : HasDerivAt (fun τ ↦ f (g τ)) w t) : HasDerivAt (fun τ ↦ f (h τ)) w t := by
  obtain ⟨C, s, hs, hC⟩ := hf (g t)
  have hhs : s ∈ 𝓝 (h t) := heq ▸ hs
  have hbig : (fun τ ↦ f (g τ) - f (h τ)) =O[𝓝 t] (fun τ ↦ g τ - h τ) := by
    apply IsBigO.of_bound C
    filter_upwards [hg.continuousAt.eventually hs, hh.continuousAt.eventually hhs] with τ hgs hhs
    simpa only [dist_eq_norm] using hC.dist_le_mul (g τ) hgs (h τ) hhs
  have hlittle : (fun τ ↦ g τ - h τ) =o[𝓝 t] (fun τ ↦ τ - t) := by
    simpa only [Pi.sub_apply, heq, sub_self, smul_zero, sub_zero] using (hg.sub hh).isLittleO
  have hz : HasDerivAt (fun τ ↦ f (g τ) - f (h τ)) 0 t := by
    apply HasDerivAt.of_isLittleO
    simpa only [heq, sub_self, smul_zero, sub_zero] using hbig.trans_isLittleO hlittle
  have hd := hfg.sub hz
  simpa only [Pi.sub_def, sub_sub_cancel, sub_zero] using hd

end LocallyLipschitz
