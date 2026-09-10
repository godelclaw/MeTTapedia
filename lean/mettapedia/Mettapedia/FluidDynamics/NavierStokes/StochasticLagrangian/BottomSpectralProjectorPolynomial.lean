import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StrainEigenvalueRates
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralClusterAnisotropy

/-!
# A polynomial formula for the bottom spectral projector

The numerator annihilates both top eigendirections, including when their
eigenvalues coincide. Its value on the bottom line is the product of the
two gaps above that line. Division therefore requires only the bottom
gap to be positive, not simplicity of the two top eigenvalues.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.BottomSpectralProjectorPolynomial

open scoped RealInnerProductSpace
open PancakeStrainSpectralFrame PancakeEigenframePerturbation
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralClusterDichotomy.SymmetricStrain

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def bottomProjectorNumerator (S : SymmetricStrain) : R3 →L[ℝ] R3 :=
  (S.1 - topEigenvalue S • 1) * (S.1 - secondEigenvalue S • 1)

theorem bottomProjectorNumerator_eq (S : SymmetricStrain) :
    bottomProjectorNumerator S =
      (spectralWidth S * bottomGap S) • bottomEigenlineProjector S := by
  have hb (i : Fin 3) :
      bottomProjectorNumerator S ((orderedEigenframe S.1 S.2).eigenbasis i) =
        (spectralWidth S * bottomGap S) •
          bottomEigenlineProjector S ((orderedEigenframe S.1 S.2).eigenbasis i) := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;>
      simp only [bottomProjectorNumerator, mul_apply_eq_comp, sub_apply, smul_apply,
      one_apply_eq_self, map_sub, map_smul, (orderedEigenframe S.1 S.2).apply_eigenbasis,
      bottomEigenlineProjector, lineProjector, InnerProductSpace.rankOne_apply,
      (orderedEigenframe S.1 S.2).eigenbasis.inner_eq_ite] <;>
      norm_num [Fin.reduceFinMk, Fin.ext_iff, spectralWidth, bottomGap, topEigenvalue,
        secondEigenvalue, thirdEigenvalue]
    module
  ext w
  rw [← (orderedEigenframe S.1 S.2).eigenbasis.sum_repr' w]
  simp only [map_sum, map_smul, smul_apply, hb]

theorem bottomEigenlineProjector_eq_polynomial (S : SymmetricStrain) (hg : 0 < bottomGap S) :
    bottomEigenlineProjector S =
      (spectralWidth S * bottomGap S)⁻¹ • bottomProjectorNumerator S := by
  rw [bottomProjectorNumerator_eq, smul_smul, inv_mul_cancel₀, one_smul]
  exact mul_ne_zero (ne_of_gt (lt_of_lt_of_le hg (bottomGap_le_spectralWidth S))) (ne_of_gt hg)

/-- Differentiability of the bottom projector does not require a top gap.
The scalar extreme-eigenvalue hypotheses may hold at a top collision. -/
theorem differentiableAt_bottomEigenlineProjector (S : ℝ → SymmetricStrain)
    (Sdot : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) Sdot t)
    (htop : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t)
    (hbottom : DifferentiableAt ℝ (fun τ ↦ thirdEigenvalue (S τ)) t)
    (hg : 0 < bottomGap (S t)) :
    DifferentiableAt ℝ (fun τ ↦ bottomEigenlineProjector (S τ)) t := by
  have hmiddle := (StrainEigenvalueRates.hasDerivAt_secondEigenvalue S Sdot t hS htop hbottom).differentiableAt
  have hw : DifferentiableAt ℝ (fun τ ↦ spectralWidth (S τ)) t := htop.sub hbottom
  have hb : DifferentiableAt ℝ (fun τ ↦ bottomGap (S τ)) t := hmiddle.sub hbottom
  have hn : DifferentiableAt ℝ (fun τ ↦ bottomProjectorNumerator (S τ)) t :=
    (hS.differentiableAt.sub (htop.smul_const (1 : R3 →L[ℝ] R3))).mul
      (hS.differentiableAt.sub (hmiddle.smul_const (1 : R3 →L[ℝ] R3)))
  have hd : spectralWidth (S t) * bottomGap (S t) ≠ 0 :=
    mul_ne_zero (ne_of_gt (lt_of_lt_of_le hg (bottomGap_le_spectralWidth (S t)))) (ne_of_gt hg)
  apply (((hw.mul hb).inv hd).smul hn).congr_of_eventuallyEq
  filter_upwards [hb.continuousAt.eventually (lt_mem_nhds hg)] with τ hτ
  exact bottomEigenlineProjector_eq_polynomial (S τ) hτ

theorem differentiableAt_expandingPlaneProjector (S : ℝ → SymmetricStrain)
    (Sdot : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) Sdot t)
    (htop : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t)
    (hbottom : DifferentiableAt ℝ (fun τ ↦ thirdEigenvalue (S τ)) t)
    (hg : 0 < bottomGap (S t)) :
    DifferentiableAt ℝ (fun τ ↦ expandingPlaneProjector (S τ)) t :=
  differentiableAt_const _ |>.sub
    (differentiableAt_bottomEigenlineProjector S Sdot t hS htop hbottom hg)

end Mettapedia.FluidDynamics.NavierStokes.BottomSpectralProjectorPolynomial
