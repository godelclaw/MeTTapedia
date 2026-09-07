import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralClusterDichotomy
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.BoundedVariation

/-!
# Differentiating the constructed top strain eigenvalue

On the simple-top-eigenvalue branch, continuity of the sign-invariant
spectral projector suffices to differentiate the top eigenvalue. No
differentiable choice of eigenvectors or derivative of the projector is
assumed. Projecting a fixed reference eigenvector supplies a continuous
nonzero eigenvector locally, and the exact eigenpair difference identity
identifies the difference-quotient limit.

At a collision, a variational minimum identifies the same rate whenever
the top eigenvalue is differentiable. Its global Lipschitz estimate then
gives almost-everywhere differentiability along Lipschitz strain paths.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeTopEigenvalueDerivative

open scoped RealInnerProductSpace Topology NNReal
open Filter PancakeStrainSpectralFrame PancakeEigenframePerturbation
open PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem topEigenlineProjector_eigenvector (S : SymmetricStrain) (v : R3) :
    S.1 (topEigenlineProjector S v) =
      topEigenvalue S • topEigenlineProjector S v := by
  simp only [topEigenlineProjector, lineProjector, InnerProductSpace.rankOne_apply,
    map_smul, (orderedEigenframe S.1 S.2).apply_eigenbasis, topEigenvalue]
  module

theorem topEigenlineProjector_fixes_topEigenvector (S : SymmetricStrain) :
    topEigenlineProjector S ((orderedEigenframe S.1 S.2).eigenbasis 0) =
      (orderedEigenframe S.1 S.2).eigenbasis 0 := by
  simp [topEigenlineProjector, lineProjector, InnerProductSpace.rankOne_apply,
    (orderedEigenframe S.1 S.2).eigenbasis.norm_eq_one]

/-- Exact finite difference identity, with no division by an eigenvalue gap. -/
theorem topEigenvalue_difference_identity (A B : SymmetricStrain) :
    let e := (orderedEigenframe B.1 B.2).eigenbasis 0
    (topEigenvalue A - topEigenvalue B) * ⟪e, topEigenlineProjector A e⟫ =
      ⟪e, (A.1 - B.1) (topEigenlineProjector A e)⟫ := by
  dsimp only
  exact eigenvector_overlap_identity A.1 B.1 _ _ _ _ B.2
    (topEigenlineProjector_eigenvector A _)
    ((orderedEigenframe B.1 B.2).apply_eigenbasis 0)

/-- Hellmann--Feynman derivative for the actually constructed top eigenvalue.
The positive gap is needed only at the time in question, not uniformly. -/
theorem hasDerivAt_topEigenvalue (S : ℝ → SymmetricStrain)
    (Sdot : R3 →L[ℝ] R3) (t : ℝ)
    (hd : HasDerivAt (fun tau ↦ (S tau).1) Sdot t)
    (hgap : 0 < topGap (S t)) :
    HasDerivAt (fun tau ↦ topEigenvalue (S tau))
      ⟪(orderedEigenframe (S t).1 (S t).2).eigenbasis 0,
        Sdot ((orderedEigenframe (S t).1 (S t).2).eigenbasis 0)⟫ t := by
  let e := (orderedEigenframe (S t).1 (S t).2).eigenbasis 0
  let v : ℝ → R3 := fun tau ↦ topEigenlineProjector (S tau) e
  have he : ‖e‖ = 1 := (orderedEigenframe (S t).1 (S t).2).eigenbasis.norm_eq_one 0
  have hvt : v t = e := topEigenlineProjector_fixes_topEigenvector (S t)
  have hS : ContinuousAt S t := hd.continuousAt.codRestrict _
  have hv : ContinuousAt v t :=
    (continuousAt_topEigenlineProjector_comp_of_topGap_pos S t hS hgap).clm_apply
      continuousAt_const
  have hden : ContinuousAt (fun tau ↦ ⟪e, v tau⟫) t := continuousAt_const.inner hv
  have hdenval : ⟪e, v t⟫ = 1 := by rw [hvt, real_inner_self_eq_norm_sq, he]; norm_num
  have hne : ∀ᶠ tau in 𝓝 t, ⟪e, v tau⟫ ≠ 0 :=
    hden.eventually_ne (by rw [hdenval]; norm_num)
  have happ : Continuous (fun p : (R3 →L[ℝ] R3) × R3 ↦ p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hlim := ((tendsto_const_nhds (x := e)).inner
    (happ.tendsto (Sdot, v t) |>.comp
      (hd.tendsto_slope.prodMk_nhds (hv.tendsto.mono_left nhdsWithin_le_nhds)))).div
      (hden.tendsto.mono_left nhdsWithin_le_nhds) (by rw [hdenval]; norm_num)
  rw [hdenval, hvt, div_one] at hlim
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply hlim.congr'
  filter_upwards [hne.filter_mono nhdsWithin_le_nhds] with tau hnonzero
  have hid := topEigenvalue_difference_identity (S tau) (S t)
  change (topEigenvalue (S tau) - topEigenvalue (S t)) * ⟪e, v tau⟫ =
    ⟪e, ((S tau).1 - (S t).1) (v tau)⟫ at hid
  change ⟪e, slope (fun s ↦ (S s).1) t tau (v tau)⟫ / ⟪e, v tau⟫ =
    slope (fun s ↦ topEigenvalue (S s)) t tau
  simp only [slope_def_module, smul_apply, real_inner_smul_right,
    smul_eq_mul]
  rw [← hid]
  field_simp [hnonzero]

/-- The largest eigenvalue is globally 1-Lipschitz, including collisions. -/
theorem lipschitzWith_topEigenvalue : LipschitzWith 1 topEigenvalue := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm,
    Real.norm_eq_abs, topEigenvalue]
    using PancakeTransverseEnergyFreezing.abs_constructedTopEigenvalue_sub_le A.1 B.1 A.2 B.2

/-- At a collision, every top eigenvector gives the same eigenvalue rate
whenever the largest eigenvalue is differentiable. The assertion follows
from the variational minimum, not from dividing by an eigenvalue gap. -/
theorem topEigenvalue_derivative_eq_of_hasDerivAt
    (S : ℝ → SymmetricStrain) (Sdot : R3 →L[ℝ] R3) (rate t : ℝ)
    (hS : HasDerivAt (fun tau ↦ (S tau).1) Sdot t)
    (hlambda : HasDerivAt (fun tau ↦ topEigenvalue (S tau)) rate t)
    (e : R3) (he : ‖e‖ = 1) (hpair : (S t).1 e = topEigenvalue (S t) • e) :
    rate = ⟪e, Sdot e⟫ := by
  have hq := (hasDerivAt_const t e).inner ℝ
    (hS.clm_apply (hasDerivAt_const t e))
  have hd := hlambda.sub hq
  simp only [inner_zero_left, map_zero, add_zero] at hd
  have hval : topEigenvalue (S t) - ⟪e, (S t).1 e⟫ = 0 := by
    rw [hpair, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
    ring
  have hmin : IsLocalMin (fun tau ↦ topEigenvalue (S tau) - ⟪e, (S tau).1 e⟫) t := by
    apply Filter.Eventually.of_forall
    intro tau
    dsimp only
    rw [hval]
    exact sub_nonneg.mpr
      (PancakeTransverseEnergyFreezing.rayleigh_le_constructedTopEigenvalue
        (S tau).1 (S tau).2 e he)
  exact sub_eq_zero.mp (hmin.hasDerivAt_eq_zero hd)

theorem hasDerivAt_topEigenvalue_of_differentiableAt
    (S : ℝ → SymmetricStrain) (Sdot : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun tau ↦ (S tau).1) Sdot t)
    (hlambda : DifferentiableAt ℝ (fun tau ↦ topEigenvalue (S tau)) t) :
    HasDerivAt (fun tau ↦ topEigenvalue (S tau))
      ⟪(orderedEigenframe (S t).1 (S t).2).eigenbasis 0,
        Sdot ((orderedEigenframe (S t).1 (S t).2).eigenbasis 0)⟫ t := by
  have hd := hlambda.hasDerivAt
  rw [topEigenvalue_derivative_eq_of_hasDerivAt S Sdot _ t hS hd _
    ((orderedEigenframe (S t).1 (S t).2).eigenbasis.norm_eq_one 0)
    ((orderedEigenframe (S t).1 (S t).2).apply_eigenbasis 0)] at hd
  exact hd

/-- Along a Lipschitz strain path the largest eigenvalue is differentiable
almost everywhere even if the collision set has positive measure. -/
theorem ae_differentiableAt_topEigenvalue (S : ℝ → SymmetricStrain)
    (C : ℝ≥0) (hS : LipschitzWith C S) :
    ∀ᵐ t, DifferentiableAt ℝ (fun tau ↦ topEigenvalue (S tau)) t :=
  (lipschitzWith_topEigenvalue.comp hS).ae_differentiableAt_real

theorem ae_hasDerivAt_topEigenvalue (S : ℝ → SymmetricStrain)
    (Sdot : ℝ → R3 →L[ℝ] R3) (C : ℝ≥0) (hLip : LipschitzWith C S)
    (hd : ∀ t, HasDerivAt (fun tau ↦ (S tau).1) (Sdot t) t) :
    ∀ᵐ t, HasDerivAt (fun tau ↦ topEigenvalue (S tau))
      ⟪(orderedEigenframe (S t).1 (S t).2).eigenbasis 0,
        Sdot t ((orderedEigenframe (S t).1 (S t).2).eigenbasis 0)⟫ t := by
  filter_upwards [ae_differentiableAt_topEigenvalue S C hLip] with t ht
  exact hasDerivAt_topEigenvalue_of_differentiableAt S (Sdot t) t (hd t) ht

end Mettapedia.FluidDynamics.NavierStokes.PancakeTopEigenvalueDerivative
