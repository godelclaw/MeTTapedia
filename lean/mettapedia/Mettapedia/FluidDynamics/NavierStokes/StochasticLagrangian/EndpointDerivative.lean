import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Right differentiation at the initial endpoint

A continuous derivative field on a closed interval determines the
right derivative of a continuous curve satisfying the equation in the
interior. No extension of the equation to negative time is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.FluidDynamics.NavierStokes.EndpointDerivative

open scoped Topology
open Filter Set

theorem hasDerivWithinAt_Ici_of_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f df : ℝ → E} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn df (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (df t) t) :
    HasDerivWithinAt f (df a) (Ici a) a := by
  have hI : Ioo a b ∈ 𝓝[>] a := Ioo_mem_nhdsGT hab
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (s := Ioo a b) (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
    ((hf a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self) hI
  have hlim : Tendsto df (𝓝[>] a) (𝓝 (df a)) :=
    (hdf a ⟨le_rfl, hab.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGT hab)
  apply hlim.congr'
  filter_upwards [hI] with t ht
  exact (hd t ht).deriv.symm

end Mettapedia.FluidDynamics.NavierStokes.EndpointDerivative
