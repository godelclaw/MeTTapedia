import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralClusterAnisotropy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralAnisotropyLimit

/-!
# A measurable cluster-aware envelope for the joint remainder

The simple-top branch uses the top gap; an exact top collision uses the
bottom gap. At a triple collision the envelope is zero, consistent with
the differential constraint on the full eigenspace. The estimate requires
the strain equation and scalar spectral differentiability. It is not an
unconditional bound on an arbitrary remainder at a collision, nor a
uniform modulus across near-collision configurations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SpectralClusterEnvelope

open scoped Topology RealInnerProductSpace
open MeasureTheory PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralClusterDichotomy.SymmetricStrain PancakeSpectralDefectEvolution
open PancakeSpectralFiniteDifference PancakeRegularizedMaterialRate SpectralClusterAnisotropy
open SpectralAnisotropyLimit StrainEigenvalueContinuity

local notation "R3" => EuclideanSpace ℝ (Fin 3)

def resolvingGap (S : SymmetricStrain) : ℝ := if 0 < topGap S then topGap S else bottomGap S

def envelope (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) : ℝ :=
  min (2 * ‖R‖ * ‖w‖ ^ 2)
    (4 * ‖R‖ * ‖w‖ * Real.sqrt (topSpectralDefect S w / resolvingGap S))

theorem envelope_nonneg (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    0 ≤ envelope S R w := by unfold envelope; positivity

theorem envelope_le_coarse (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3) :
    envelope S R w ≤ 2 * ‖R‖ * ‖w‖ ^ 2 := min_le_left _ _

theorem envelope_eq_zero_of_defect_eq_zero (S : SymmetricStrain) (R : R3 →L[ℝ] R3)
    (w : R3) (hA : topSpectralDefect S w = 0) : envelope S R w = 0 := by
  simp only [envelope, hA, zero_div, Real.sqrt_zero, mul_zero,
    min_eq_right (by positivity : 0 ≤ 2 * ‖R‖ * ‖w‖ ^ 2)]

theorem abs_remainderAnisotropy_le_envelope (S : ℝ → SymmetricStrain)
    (R : R3 →L[ℝ] R3) (t : ℝ)
    (hS : HasDerivAt (fun τ ↦ (S τ).1) (-(S t).1 * (S t).1 + R) t)
    (hL : DifferentiableAt ℝ (fun τ ↦ topEigenvalue (S τ)) t) (w : R3) :
    |remainderAnisotropy R (topVector (S t)) w| ≤ envelope (S t) R w := by
  by_cases htop : 0 < topGap (S t)
  · simpa only [envelope, resolvingGap, limitingEnvelope, if_pos htop] using
      abs_remainderAnisotropy_le_limitingEnvelope (S t) R w
  · have ht0 : topGap (S t) = 0 := le_antisymm (le_of_not_gt htop) (topGap_nonneg (S t))
    by_cases hbottom : 0 < bottomGap (S t)
    · exact le_min (abs_remainderAnisotropy_le R _ w (topVector_norm (S t)))
        (by simpa only [resolvingGap, if_neg htop] using
          abs_remainderAnisotropy_le_of_top_collision S R t hS hL ht0 hbottom w)
    · have hb0 : bottomGap (S t) = 0 :=
        le_antisymm (le_of_not_gt hbottom) (bottomGap_nonneg (S t))
      rw [remainderAnisotropy_eq_zero_of_triple_collision S R t hS hL ht0 hb0 w, abs_zero]
      exact envelope_nonneg _ _ _

theorem measurable_envelope {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : X → SymmetricStrain) (R : X → R3 →L[ℝ] R3) (w : X → R3)
    (hS : Continuous S) (hR : Continuous R) (hw : Continuous w) :
    Measurable (fun x ↦ envelope (S x) (R x) (w x)) := by
  have htop := continuous_topGap.comp hS
  have hbottom := continuous_bottomGap.comp hS
  have hg : Measurable (fun x ↦ resolvingGap (S x)) :=
    Measurable.ite (isOpen_lt continuous_const htop).measurableSet htop.measurable hbottom.measurable
  have hA : Continuous (fun x ↦ topSpectralDefect (S x) (w x)) := by
    exact ((PancakeTopEigenvalueDerivative.lipschitzWith_topEigenvalue.continuous.comp hS).mul
      (hw.norm.pow 2)).sub (hw.inner ((continuous_subtype_val.comp hS).clm_apply hw))
  exact ((measurable_const.mul hR.measurable.norm).mul (hw.measurable.norm.pow_const 2)).min
    (((measurable_const.mul hR.measurable.norm).mul hw.measurable.norm).mul (hA.measurable.div hg).sqrt)

end Mettapedia.FluidDynamics.NavierStokes.SpectralClusterEnvelope
