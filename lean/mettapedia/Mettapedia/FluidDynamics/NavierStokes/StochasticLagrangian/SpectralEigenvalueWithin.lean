import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeTopEigenvalueDerivative

/-!
# The top eigenvalue derivative within a time domain

The exact eigenpair difference identity also gives the one-sided
Hellmann–Feynman derivative. Only a positive gap at the base point and
the derivative within the specified domain are needed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralEigenvalueWithin

open scoped RealInnerProductSpace Topology
open Filter PancakeStrainSpectralFrame PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeTopEigenvalueDerivative

local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem hasDerivWithinAt_topEigenvalue (S : ℝ → SymmetricStrain)
    (Sdot : R3 →L[ℝ] R3) (domain : Set ℝ) (t : ℝ)
    (hd : HasDerivWithinAt (fun tau ↦ (S tau).1) Sdot domain t)
    (hgap : 0 < topGap (S t)) :
    HasDerivWithinAt (fun tau ↦ topEigenvalue (S tau))
      ⟪(orderedEigenframe (S t).1 (S t).2).eigenbasis 0,
        Sdot ((orderedEigenframe (S t).1 (S t).2).eigenbasis 0)⟫ domain t := by
  let e := (orderedEigenframe (S t).1 (S t).2).eigenbasis 0
  let v : ℝ → R3 := fun tau ↦ topEigenlineProjector (S tau) e
  have he : ‖e‖ = 1 := (orderedEigenframe (S t).1 (S t).2).eigenbasis.norm_eq_one 0
  have hvt : v t = e := topEigenlineProjector_fixes_topEigenvector (S t)
  have hS : ContinuousWithinAt S domain t :=
    tendsto_subtype_rng.mpr hd.continuousWithinAt
  have hv : ContinuousWithinAt v domain t :=
    ((continuousAt_topEigenlineProjector_of_topGap_pos (S t) hgap).comp_continuousWithinAt hS).clm_apply
      continuousWithinAt_const
  have hden : ContinuousWithinAt (fun tau ↦ ⟪e, v tau⟫) domain t :=
    continuousWithinAt_const.inner hv
  have hdenval : ⟪e, v t⟫ = 1 := by rw [hvt, real_inner_self_eq_norm_sq, he]; norm_num
  have hne : ∀ᶠ tau in 𝓝[domain] t, ⟪e, v tau⟫ ≠ 0 :=
    hden.tendsto.eventually_ne (by rw [hdenval]; norm_num)
  have hsub : 𝓝[domain \ {t}] t ≤ 𝓝[domain] t := nhdsWithin_mono _ Set.sdiff_subset
  have happ : Continuous (fun p : (R3 →L[ℝ] R3) × R3 ↦ p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hlim := ((tendsto_const_nhds (x := e)).inner
    (happ.tendsto (Sdot, v t) |>.comp
      ((hasDerivWithinAt_iff_tendsto_slope.mp hd).prodMk_nhds
        (hv.tendsto.mono_left hsub)))).div
      (hden.tendsto.mono_left hsub) (by rw [hdenval]; norm_num)
  rw [hdenval, hvt, div_one] at hlim
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  apply hlim.congr'
  filter_upwards [hne.filter_mono hsub] with tau hnonzero
  have hid := topEigenvalue_difference_identity (S tau) (S t)
  change (topEigenvalue (S tau) - topEigenvalue (S t)) * ⟪e, v tau⟫ =
    ⟪e, ((S tau).1 - (S t).1) (v tau)⟫ at hid
  change ⟪e, slope (fun s ↦ (S s).1) t tau (v tau)⟫ / ⟪e, v tau⟫ =
    slope (fun s ↦ topEigenvalue (S s)) t tau
  simp only [slope_def_module, smul_apply, real_inner_smul_right,
    smul_eq_mul]
  rw [← hid]
  field_simp [hnonzero]

end Mettapedia.FluidDynamics.NavierStokes.SpectralEigenvalueWithin
