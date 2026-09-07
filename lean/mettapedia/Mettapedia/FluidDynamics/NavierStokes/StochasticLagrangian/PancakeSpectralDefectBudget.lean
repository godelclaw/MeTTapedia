import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralDefectEvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Integrated spectral-defect energy through eigenvalue collisions

The top eigenvalue is absolutely continuous along a continuously
differentiable strain path on a compact time interval. The exact spectral
defect identity therefore holds almost everywhere without a simple-gap
hypothesis. Its integral retains the signed anisotropic strain forcing.

Even integrability of the selected eigenvector's scalar forcing is derived
from the equations and absolute continuity, rather than assumed across
collisions. This is not an arbitrary-data bound for that forcing integral.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSpectralDefectBudget

open scoped RealInnerProductSpace NNReal
open MeasureTheory
open PancakeStrainSpectralFrame PancakeTopEigenvalueDerivative PancakeSpectralDefectEvolution
open PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def topRemainderAnisotropy (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) : ℝ :=
  remainderAnisotropy R ((orderedEigenframe S.1 S.2).eigenbasis 0) w

theorem absolutelyContinuousOnInterval_topEigenvalue (S : ℝ → SymmetricStrain)
    (a b : ℝ) (hS : ContDiffOn ℝ 1 (fun t ↦ (S t).1) (Set.uIcc a b)) :
    AbsolutelyContinuousOnInterval (fun t ↦ topEigenvalue (S t)) a b := by
  obtain ⟨K, hK⟩ := hS.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  have hKS : LipschitzOnWith K S (Set.uIcc a b) := by
    intro x hx y hy
    simpa only [Subtype.edist_eq] using hK hx hy
  exact (lipschitzWith_topEigenvalue.comp_lipschitzOnWith hKS).absolutelyContinuousOnInterval

theorem absolutelyContinuousOnInterval_topSpectralDefect
    (S : ℝ → SymmetricStrain) (w : ℝ → R3) (a b : ℝ)
    (hS : ContDiffOn ℝ 1 (fun t ↦ (S t).1) (Set.uIcc a b))
    (hw : ContDiffOn ℝ 1 w (Set.uIcc a b)) :
    AbsolutelyContinuousOnInterval (fun t ↦ topSpectralDefect (S t) (w t)) a b := by
  have hn : ContDiffOn ℝ 1 (fun t ↦ ‖w t‖ ^ 2) (Set.uIcc a b) := by
    simpa only [real_inner_self_eq_norm_sq] using hw.inner ℝ hw
  have hq : ContDiffOn ℝ 1 (fun t ↦ ⟪w t, (S t).1 (w t)⟫) (Set.uIcc a b) :=
    hw.inner ℝ (hS.clm_apply hw)
  exact ((absolutelyContinuousOnInterval_topEigenvalue S a b hS).mul
    hn.absolutelyContinuousOnInterval).sub hq.absolutelyContinuousOnInterval

theorem ae_hasDerivAt_topSpectralDefect
    (S : ℝ → SymmetricStrain) (w : ℝ → R3)
    (R : ℝ → R3 →L[ℝ] R3) (f : ℝ → R3) (a b : ℝ)
    (hS : ContDiffOn ℝ 1 (fun t ↦ (S t).1) (Set.uIcc a b))
    (hdS : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun tau ↦ (S tau).1) (-(S t).1 * (S t).1 + R t) t)
    (hdw : ∀ t ∈ Set.uIcc a b, HasDerivAt w ((S t).1 (w t) + f t) t) :
    ∀ᵐ t, t ∈ Set.uIcc a b →
      HasDerivAt (fun tau ↦ topSpectralDefect (S tau) (w tau))
        (-‖spectralResidual (S t).1 (topEigenvalue (S t)) (w t)‖ ^ 2 +
          topRemainderAnisotropy (S t) (R t) (w t) +
          2 * ⟪spectralResidual (S t).1 (topEigenvalue (S t)) (w t), f t⟫) t := by
  filter_upwards [(absolutelyContinuousOnInterval_topEigenvalue S a b hS).ae_differentiableAt]
    with t ht hmem
  exact hasDerivAt_topSpectralDefect_of_differentiableAt S w (R t) (f t) t
    (hdS t hmem) (hdw t hmem) (ht hmem)

theorem continuousOn_spectralResidual
    (S : ℝ → SymmetricStrain) (w : ℝ → R3) (a b : ℝ)
    (hS : ContDiffOn ℝ 1 (fun t ↦ (S t).1) (Set.uIcc a b))
    (hw : ContinuousOn w (Set.uIcc a b)) :
    ContinuousOn (fun t ↦ spectralResidual (S t).1 (topEigenvalue (S t)) (w t))
      (Set.uIcc a b) :=
  ((absolutelyContinuousOnInterval_topEigenvalue S a b hS).continuousOn.smul hw).sub
    (hS.continuousOn.clm_apply hw)

/-- Collision-compatible integrability and exact energy balance. No
independent regularity hypothesis on a chosen eigenframe is used. -/
theorem integrated_topSpectralDefect_identity
    (S : ℝ → SymmetricStrain) (w : ℝ → R3)
    (R : ℝ → R3 →L[ℝ] R3) (f : ℝ → R3) (a b : ℝ)
    (hS : ContDiffOn ℝ 1 (fun t ↦ (S t).1) (Set.uIcc a b))
    (hw : ContDiffOn ℝ 1 w (Set.uIcc a b))
    (hf : ContinuousOn f (Set.uIcc a b))
    (hdS : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun tau ↦ (S tau).1) (-(S t).1 * (S t).1 + R t) t)
    (hdw : ∀ t ∈ Set.uIcc a b, HasDerivAt w ((S t).1 (w t) + f t) t) :
    let z := fun t ↦ spectralResidual (S t).1 (topEigenvalue (S t)) (w t)
    let A := fun t ↦ topRemainderAnisotropy (S t) (R t) (w t)
    IntervalIntegrable A volume a b ∧
      topSpectralDefect (S b) (w b) + (∫ t in a..b, ‖z t‖ ^ 2) =
        topSpectralDefect (S a) (w a) + (∫ t in a..b, A t) +
          ∫ t in a..b, 2 * ⟪z t, f t⟫ := by
  dsimp only
  let E := fun t ↦ topSpectralDefect (S t) (w t)
  let z := fun t ↦ spectralResidual (S t).1 (topEigenvalue (S t)) (w t)
  let A := fun t ↦ topRemainderAnisotropy (S t) (R t) (w t)
  have hAC := absolutelyContinuousOnInterval_topSpectralDefect S w a b hS hw
  have hz := continuousOn_spectralResidual S w a b hS hw.continuousOn
  have hzI : IntervalIntegrable (fun t ↦ ‖z t‖ ^ 2) volume a b :=
    (hz.norm.pow 2).intervalIntegrable
  have hfI : IntervalIntegrable (fun t ↦ 2 * ⟪z t, f t⟫) volume a b :=
    (continuousOn_const.mul (hz.inner hf)).intervalIntegrable
  have hd := ae_hasDerivAt_topSpectralDefect S w R f a b hS hdS hdw
  have heq : ∀ᵐ t, t ∈ Set.uIcc a b →
      deriv E t + ‖z t‖ ^ 2 - 2 * ⟪z t, f t⟫ = A t := by
    filter_upwards [hd] with t ht hmem
    have h := (ht hmem).deriv
    change deriv E t = -‖z t‖ ^ 2 + A t + 2 * ⟪z t, f t⟫ at h
    linarith
  have hAI : IntervalIntegrable A volume a b :=
    (hAC.intervalIntegrable_deriv.add hzI |>.sub hfI).congr_ae (by
      change ∀ᵐ t ∂volume.restrict (Set.uIoc a b),
        deriv E t + ‖z t‖ ^ 2 - 2 * ⟪z t, f t⟫ = A t
      rw [ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [heq] with t ht hmem
      exact ht (Set.uIoc_subset_uIcc hmem))
  refine ⟨hAI, ?_⟩
  have hint : (∫ t in a..b, deriv E t + ‖z t‖ ^ 2 - 2 * ⟪z t, f t⟫) =
      ∫ t in a..b, A t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [heq] with t ht hmem
    exact ht (Set.uIoc_subset_uIcc hmem)
  rw [intervalIntegral.integral_sub (hAC.intervalIntegrable_deriv.add hzI) hfI,
    intervalIntegral.integral_add hAC.intervalIntegrable_deriv hzI,
    hAC.integral_deriv_eq_sub] at hint
  change E b + (∫ t in a..b, ‖z t‖ ^ 2) = E a + (∫ t in a..b, A t) +
    ∫ t in a..b, 2 * ⟪z t, f t⟫
  linarith

/-- A signed forcing budget with any positive share of squared-residual
damping allocated to vorticity forcing. Taking `theta < 1` retains positive
damping. There is no gap or inverse-gap constant. -/
theorem integrated_topSpectralDefect_budget
    (S : ℝ → SymmetricStrain) (w : ℝ → R3)
    (R : ℝ → R3 →L[ℝ] R3) (f : ℝ → R3) (a b theta : ℝ)
    (hab : a ≤ b) (htheta : 0 < theta)
    (hS : ContDiffOn ℝ 1 (fun t ↦ (S t).1) (Set.uIcc a b))
    (hw : ContDiffOn ℝ 1 w (Set.uIcc a b))
    (hf : ContinuousOn f (Set.uIcc a b))
    (hdS : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun tau ↦ (S tau).1) (-(S t).1 * (S t).1 + R t) t)
    (hdw : ∀ t ∈ Set.uIcc a b, HasDerivAt w ((S t).1 (w t) + f t) t) :
    let z := fun t ↦ spectralResidual (S t).1 (topEigenvalue (S t)) (w t)
    topSpectralDefect (S b) (w b) + (1 - theta) * (∫ t in a..b, ‖z t‖ ^ 2) ≤
      topSpectralDefect (S a) (w a) +
        (∫ t in a..b, topRemainderAnisotropy (S t) (R t) (w t)) +
        (∫ t in a..b, ‖f t‖ ^ 2) / theta := by
  dsimp only
  let z := fun t ↦ spectralResidual (S t).1 (topEigenvalue (S t)) (w t)
  have hbalance := (integrated_topSpectralDefect_identity S w R f a b hS hw hf hdS hdw).2
  have hz := continuousOn_spectralResidual S w a b hS hw.continuousOn
  have hzI : IntervalIntegrable (fun t ↦ ‖z t‖ ^ 2) volume a b :=
    (hz.norm.pow 2).intervalIntegrable
  have hforce : IntervalIntegrable (fun t ↦ ‖f t‖ ^ 2) volume a b :=
    (hf.norm.pow 2).intervalIntegrable
  have hcross : IntervalIntegrable (fun t ↦ 2 * ⟪z t, f t⟫) volume a b :=
    (continuousOn_const.mul (hz.inner hf)).intervalIntegrable
  have hbound := intervalIntegral.integral_mono_on hab hcross
    ((hzI.const_mul theta).add (hforce.div_const theta))
    (fun t _ ↦ spectralDefect_forcing_young (z t) (f t) theta htheta)
  rw [intervalIntegral.integral_add (hzI.const_mul theta) (hforce.div_const theta),
    intervalIntegral.integral_const_mul theta, intervalIntegral.integral_div theta] at hbound
  change topSpectralDefect (S b) (w b) + (1 - theta) * (∫ t in a..b, ‖z t‖ ^ 2) ≤ _
  change topSpectralDefect (S b) (w b) + (∫ t in a..b, ‖z t‖ ^ 2) =
    topSpectralDefect (S a) (w a) +
      (∫ t in a..b, topRemainderAnisotropy (S t) (R t) (w t)) +
      (∫ t in a..b, 2 * ⟪z t, f t⟫) at hbalance
  nlinarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeSpectralDefectBudget
