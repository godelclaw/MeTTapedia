import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralDefectEvolution

/-!
# A paid mixed-gradient estimate for the regularized spectral defect

Adding `delta * ‖w‖²` to the actual top spectral defect supplies coercivity
without an inverse eigenvalue gap. The mixed diffusion product-rule terms
then retain half the vorticity-gradient damping and pay an explicit
`16 / delta` strain-gradient cost. The operator derivative is constructed
from the actual top eigenvalue along differentiable strain paths.

This is the gradient algebra, not a spatial weak chain rule, an integrated
NS diffusion estimate, or a scale-uniform bound on the resulting cost.
The positive regularization parameter is explicit and is not sent to zero.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeRegularizedDiffusion

open scoped RealInnerProductSpace
open PancakeSpectralDefectEvolution PancakeStrainSpectralFrame PancakeTopEigenvalueDerivative
open PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def regularizedGap (S : SymmetricStrain) (delta : ℝ) : R3 →L[ℝ] R3 :=
  (topEigenvalue S + delta) • (1 : R3 →L[ℝ] R3) - S.1

theorem regularizedGap_energy (S : SymmetricStrain) (delta : ℝ) (w : R3) :
    ⟪w, regularizedGap S delta w⟫ = topSpectralDefect S w + delta * ‖w‖ ^ 2 := by
  simp only [regularizedGap, sub_apply, smul_apply,
    one_apply_eq_self, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, topSpectralDefect, spectralDefect]
  ring

theorem regularizedGap_coercive (S : SymmetricStrain) (delta : ℝ) (w : R3) :
    delta * ‖w‖ ^ 2 ≤ ⟪w, regularizedGap S delta w⟫ := by
  rw [regularizedGap_energy]
  linarith [topSpectralDefect_nonneg S w]

/-- The two product-rule terms involving the vorticity gradient.
Here `G` is the derivative of the gap operator, identified below. -/
def gradientProduction (S : SymmetricStrain) (delta : ℝ)
    (G : R3 →L[ℝ] R3) (w v : R3) : ℝ :=
  -2 * ⟪v, regularizedGap S delta v⟫ - 4 * ⟪v, G w⟫

theorem gradientProduction_paid (S : SymmetricStrain) (delta : ℝ)
    (G : R3 →L[ℝ] R3) (w v : R3) (hd : 0 < delta) :
    gradientProduction S delta G w v + delta * ‖v‖ ^ 2 ≤
      4 * ‖G w‖ ^ 2 / delta := by
  have hy := spectralDefect_forcing_young v ((-2 : ℝ) • G w) delta hd
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs] at hy
  norm_num at hy
  ring_nf at hy
  have hc := regularizedGap_coercive S delta v
  unfold gradientProduction
  simp only [div_eq_mul_inv]
  nlinarith

theorem gradientProduction_paid_opNorm (S : SymmetricStrain) (delta : ℝ)
    (G : R3 →L[ℝ] R3) (w v : R3) (hd : 0 < delta) :
    gradientProduction S delta G w v + delta * ‖v‖ ^ 2 ≤
      4 * ‖G‖ ^ 2 * ‖w‖ ^ 2 / delta := by
  apply (gradientProduction_paid S delta G w v hd).trans
  have hg := G.le_opNorm w
  have hs : ‖G w‖ ^ 2 ≤ ‖G‖ ^ 2 * ‖w‖ ^ 2 := by
    calc
      _ ≤ (‖G‖ * ‖w‖) ^ 2 := by gcongr
      _ = _ := mul_pow _ _ _
  apply div_le_div_of_nonneg_right ?_ hd.le
  nlinarith

def gapDerivative (S : SymmetricStrain) (Sdot : R3 →L[ℝ] R3) : R3 →L[ℝ] R3 :=
  ⟪(orderedEigenframe S.1 S.2).eigenbasis 0,
    Sdot ((orderedEigenframe S.1 S.2).eigenbasis 0)⟫ • (1 : R3 →L[ℝ] R3) - Sdot

theorem gapDerivative_norm (S : SymmetricStrain) (Sdot : R3 →L[ℝ] R3) :
    ‖gapDerivative S Sdot‖ ≤ 2 * ‖Sdot‖ := by
  have he := (orderedEigenframe S.1 S.2).eigenbasis.norm_eq_one 0
  have hr := abs_quadratic_le_opNorm Sdot ((orderedEigenframe S.1 S.2).eigenbasis 0)
  rw [he] at hr
  norm_num at hr
  unfold gapDerivative
  calc
    _ ≤ ‖⟪(orderedEigenframe S.1 S.2).eigenbasis 0,
      Sdot ((orderedEigenframe S.1 S.2).eigenbasis 0)⟫ •
        (1 : R3 →L[ℝ] R3)‖ + ‖Sdot‖ := norm_sub_le _ _
    _ ≤ 2 * ‖Sdot‖ := by simp only [norm_smul, norm_one, Real.norm_eq_abs, mul_one]; linarith

theorem hasDerivAt_regularizedGap (S : ℝ → SymmetricStrain)
    (Sdot : R3 →L[ℝ] R3) (delta t : ℝ)
    (hS : HasDerivAt (fun s ↦ (S s).1) Sdot t)
    (hlambda : DifferentiableAt ℝ (fun s ↦ topEigenvalue (S s)) t) :
    HasDerivAt (fun s ↦ regularizedGap (S s) delta) (gapDerivative (S t) Sdot) t := by
  have hl := hasDerivAt_topEigenvalue_of_differentiableAt S Sdot t hS hlambda
  exact ((hl.add_const delta).smul_const (1 : R3 →L[ℝ] R3)).sub hS

/-- No eigenvalue-gap denominator: the price is the chosen positive `delta`. -/
theorem gradientProduction_paid_strain (S : SymmetricStrain) (delta : ℝ)
    (Sdot : R3 →L[ℝ] R3) (w v : R3) (hd : 0 < delta) :
    gradientProduction S delta (gapDerivative S Sdot) w v + delta * ‖v‖ ^ 2 ≤
      16 * ‖Sdot‖ ^ 2 * ‖w‖ ^ 2 / delta := by
  apply (gradientProduction_paid_opNorm S delta (gapDerivative S Sdot) w v hd).trans
  have hg := gapDerivative_norm S Sdot
  calc
    _ ≤ 4 * (2 * ‖Sdot‖) ^ 2 * ‖w‖ ^ 2 / delta := by gcongr
    _ = _ := by ring

theorem gradientProduction_sum_paid {ι : Type*} (I : Finset ι)
    (S : SymmetricStrain) (delta nu : ℝ) (Sdot : ι → R3 →L[ℝ] R3)
    (w : R3) (v : ι → R3) (hd : 0 < delta) (hnu : 0 ≤ nu) :
    nu * ∑ i ∈ I, gradientProduction S delta (gapDerivative S (Sdot i)) w (v i) +
      nu * delta * ∑ i ∈ I, ‖v i‖ ^ 2 ≤
      (16 * nu / delta) * (∑ i ∈ I, ‖Sdot i‖ ^ 2) * ‖w‖ ^ 2 := by
  have h := Finset.sum_le_sum (fun i (_hi : i ∈ I) ↦
    gradientProduction_paid_strain S delta (Sdot i) w (v i) hd)
  have hn := mul_le_mul_of_nonneg_left h hnu
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
    ← Finset.sum_mul] at hn
  convert hn using 1 <;> first | rfl | ring

end Mettapedia.FluidDynamics.NavierStokes.PancakeRegularizedDiffusion
