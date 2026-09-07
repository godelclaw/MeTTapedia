import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeWeightVariationGradient

/-!
# Alignment depletion of the actual strain-weight transport

The anisotropic quadratic form vanishes on the reference eigenline.
Its bound therefore retains the transverse component of the vorticity,
instead of replacing both factors by its full norm. The reference line
need not be selected differentiably, and no inverse spectral gap occurs.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeAnisotropyDepletion

open scoped RealInnerProductSpace
open MeasureTheory PancakeSpectralDefectEvolution PancakeSpectralFiniteDifference
open PancakeRegularizedDiffusion PancakeWeightVariationGradient PancakePhysicalWeightedTransport
open PancakePhysicalSpectralDefect PancakeFourierStrainGradient PancakeFourierMaterialPaths
open PancakeFilteredStrainDynamics PancakePhysicalTransportCancellation PeriodicFourierTriad
open PancakeStrainSpectralFrame PancakeSpectralProjectorRegularity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def lineRemainder (e w : H) : H := w - ⟪e, w⟫ • e

theorem norm_lineRemainder_sq (e w : H) (he : ‖e‖ = 1) :
    ‖lineRemainder e w‖ ^ 2 = ‖w‖ ^ 2 - ⟪e, w⟫ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [lineRemainder, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm w e, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, he]
  ring

theorem norm_lineRemainder_le (e w : H) (he : ‖e‖ = 1) : ‖lineRemainder e w‖ ≤ ‖w‖ := by
  have h := norm_lineRemainder_sq e w he
  nlinarith [norm_nonneg (lineRemainder e w), norm_nonneg w, sq_nonneg ⟪e, w⟫]

theorem remainderAnisotropy_line_expansion (R : H →L[ℝ] H) (e w : H) (he : ‖e‖ = 1) :
    remainderAnisotropy R e w = remainderAnisotropy R e (lineRemainder e w) -
      ⟪e, w⟫ * (⟪e, R (lineRemainder e w)⟫ + ⟪lineRemainder e w, R e⟫) := by
  unfold remainderAnisotropy
  rw [norm_lineRemainder_sq e w he]
  simp only [lineRemainder,
    map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  ring

theorem abs_inner_operator_le (R : H →L[ℝ] H) (v w : H) :
    |⟪v, R w⟫| ≤ ‖R‖ * ‖v‖ * ‖w‖ := by
  calc
    _ ≤ ‖v‖ * ‖R w‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖R‖ * ‖w‖) := mul_le_mul_of_nonneg_left (R.le_opNorm w) (norm_nonneg v)
    _ = _ := by ring

theorem abs_remainderAnisotropy_depleted (R : H →L[ℝ] H) (e w : H) (he : ‖e‖ = 1) :
    |remainderAnisotropy R e w| ≤ 4 * ‖R‖ * ‖w‖ * ‖lineRemainder e w‖ := by
  have ha : |⟪e, w⟫| ≤ ‖w‖ := by simpa only [he, one_mul] using abs_real_inner_le_norm e w
  have hz := norm_lineRemainder_le e w he
  have h1 := abs_inner_operator_le R e (lineRemainder e w)
  have h2 := abs_inner_operator_le R (lineRemainder e w) e
  rw [he, mul_one] at h1 h2
  rw [remainderAnisotropy_line_expansion R e w he]
  calc
    _ ≤ |remainderAnisotropy R e (lineRemainder e w)| +
      |⟪e, w⟫| * (|⟪e, R (lineRemainder e w)⟫| + |⟪lineRemainder e w, R e⟫|) := by
        apply (abs_sub _ _).trans
        rw [abs_mul]
        gcongr
        exact abs_add_le _ _
    _ ≤ 2 * ‖R‖ * ‖lineRemainder e w‖ ^ 2 + |⟪e, w⟫| *
      (‖R‖ * ‖lineRemainder e w‖ + ‖R‖ * ‖lineRemainder e w‖) := by
        exact add_le_add (abs_remainderAnisotropy_le R e _ he)
          (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (abs_nonneg _))
    _ = 2 * ‖R‖ * ‖lineRemainder e w‖ * (‖lineRemainder e w‖ + |⟪e, w⟫|) := by ring
    _ ≤ 2 * ‖R‖ * ‖lineRemainder e w‖ * (‖w‖ + ‖w‖) := by gcongr
    _ = _ := by ring

theorem remainderAnisotropy_aligned (R : H →L[ℝ] H) (e : H) (alpha : ℝ) (he : ‖e‖ = 1) :
    remainderAnisotropy R e (alpha • e) = 0 := by
  simp only [remainderAnisotropy, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    map_smul, real_inner_smul_left, real_inner_smul_right, he]
  ring

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem gapDerivative_quadratic_eq_anisotropy (S : SymmetricStrain)
    (A : R3 →L[ℝ] R3) (w : R3) :
    ⟪w, gapDerivative S A w⟫ = remainderAnisotropy A (topVector S) w := by
  simp only [gapDerivative, remainderAnisotropy, topVector, sub_apply, smul_apply,
    one_apply_eq_self, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]

def physicalLineRemainder (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : R3 :=
  lineRemainder (topVector (spatialStrain modes (filteredVelocity chi u) x)) (spatialVorticity modes u x)

theorem abs_physicalGapGradient_depleted (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) (j : Fin 3) :
    |⟪spatialVorticity modes u x, physicalGapGradient chi modes u x j (spatialVorticity modes u x)⟫| ≤
      4 * ‖strainGradient modes (filteredVelocity chi u) x j‖ * ‖spatialVorticity modes u x‖ *
        ‖physicalLineRemainder chi modes u x‖ := by
  rw [physicalGapGradient, gapDerivative_quadratic_eq_anisotropy]
  exact abs_remainderAnisotropy_depleted _ _ _ (topVector_norm _)

theorem ae_abs_physicalWeightVariation_depleted
    (chi beta : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) (delta : ℝ) :
    ∀ᵐ x : T3, |physicalWeightVariation chi beta modes u delta x| ≤
      4 * (∑ j : Fin 3, |velocityComponent beta modes u j x| *
        ‖strainGradient modes (filteredVelocity chi u) x j‖) *
          ‖spatialVorticity modes u x‖ * ‖physicalLineRemainder chi modes u x‖ := by
  filter_upwards [ae_physicalWeightVariation_eq chi beta modes u delta] with x hx
  rw [hx]
  calc
    _ ≤ ∑ j : Fin 3, |velocityComponent beta modes u j x *
      ⟪spatialVorticity modes u x, physicalGapGradient chi modes u x j (spatialVorticity modes u x)⟫| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, |velocityComponent beta modes u j x| *
      (4 * ‖strainGradient modes (filteredVelocity chi u) x j‖ * ‖spatialVorticity modes u x‖ *
        ‖physicalLineRemainder chi modes u x‖) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_physicalGapGradient_depleted chi modes u x j) (abs_nonneg _)
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]; congr 1; ext j; ring

theorem ae_physicalWeightVariation_zero_of_aligned
    (chi beta : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) (delta : ℝ) :
    ∀ᵐ x : T3, physicalLineRemainder chi modes u x = 0 →
      physicalWeightVariation chi beta modes u delta x = 0 := by
  filter_upwards [ae_abs_physicalWeightVariation_depleted chi beta modes u delta] with x hx ha
  rw [ha, norm_zero, mul_zero] at hx
  exact abs_nonpos_iff.mp hx

end Mettapedia.FluidDynamics.NavierStokes.PancakeAnisotropyDepletion
