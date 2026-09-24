import Mettapedia.Analysis.AngularCurlRadialVariation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteAngularInviscidWork

/-!
# Radial and transverse strain work for the actual angular correction

The angular variational gradient has an explicit pointwise radial component.
Its remainder pairs only with the departure of strain from any chosen scalar
multiple of vorticity. The scalar is arbitrary: neither its derivatives nor
division by vorticity are needed. The resulting identities do not bound the
scalar growth rate or the signed transverse and subgrid work.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteAngularRadialWork

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalVorticityEighthMoment
open LocalAlignmentForcing LocalJointDiffusionBudget
open FiniteAngularSourceWork FiniteAngularCurlVariation FiniteAngularInviscidWork FourierFiniteSupport
open PancakeLocalInfiniteVelocity PancakeFilteredStrainDynamics FilteredAngularSourceBalance
open FiniteAngularTransport

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def transverseGradient (u : FourierVelocity) (x : T3) : R3 :=
  AngularCurlDecomposition.transverseGradient (fullVorticity u x)
    (fun j ↦ fullCurlGradient u j x) (fun j k ↦ FiniteVorticityMixedJets.mixed u k j x)

theorem inner_angularGradient_vorticity (u : FourierVelocity) (x : T3) :
    ⟪angularGradient u x, fullVorticity u x⟫ =
      8 * LocalAngularCurlBudget.angularCurlDensity u x :=
  AngularCurlDecomposition.inner_variationalGradient_value _ _ _

theorem inner_transverseGradient_vorticity (u : FourierVelocity) (x : T3) :
    ⟪transverseGradient u x, fullVorticity u x⟫ = 0 :=
  AngularCurlDecomposition.inner_transverseGradient_value _ _ _

theorem inner_angularGradient_source (u : FourierVelocity) (x : T3) (f : R3) (c : ℝ) :
    ⟪angularGradient u x, f⟫ =
      8 * ‖LocalAngularCurlBudget.angularCurl u x‖ ^ 2 * ⟪fullVorticity u x, f⟫ +
        ⟪transverseGradient u x, f - c • fullVorticity u x⟫ :=
  AngularCurlDecomposition.inner_variationalGradient_source _ _ _ f c

theorem inner_correctedGradient_vorticity (κ : ℝ) (u : FourierVelocity) (x : T3) :
    ⟪correctedGradient κ u x, fullVorticity u x⟫ = 8 * correctedDensity κ u x := by
  simp only [correctedGradient, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, inner_angularGradient_vorticity, correctedDensity, energy]
  ring

/-- A scalar reference rate may vary in space without creating a derivative cost. -/
theorem inner_correctedGradient_source (κ : ℝ) (u : FourierVelocity) (x : T3) (f : R3) (c : ℝ) :
    ⟪correctedGradient κ u x, f⟫ = 8 * c * correctedDensity κ u x +
      ⟪correctedGradient κ u x, f - c • fullVorticity u x⟫ := by
  rw [inner_sub_right, real_inner_smul_right, inner_correctedGradient_vorticity]
  ring

theorem inner_correctedGradient_strain_transverse (κ : ℝ) (u : FourierVelocity) (x : T3) (c : ℝ) :
    ⟪correctedGradient κ u x, fullStrainOperator u x (fullVorticity u x)⟫ =
      (‖fullVorticity u x‖ ^ 6 - (24 / κ) * ‖LocalAngularCurlBudget.angularCurl u x‖ ^ 2) *
        ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫ -
      (3 / κ) * ⟪transverseGradient u x,
        fullStrainOperator u x (fullVorticity u x) - c • fullVorticity u x⟫ := by
  simp only [correctedGradient, inner_sub_left, real_inner_smul_left]
  rw [inner_angularGradient_source u x _ c]
  ring

/-- Exact alignment removes the transverse defect, but does not give the
remaining scalar growth a favorable sign. -/
theorem inner_correctedGradient_strain_of_parallel (κ : ℝ) (u : FourierVelocity) (x : T3) (c : ℝ)
    (h : fullStrainOperator u x (fullVorticity u x) = c • fullVorticity u x) :
    ⟪correctedGradient κ u x, fullStrainOperator u x (fullVorticity u x)⟫ =
      8 * c * correctedDensity κ u x := by
  rw [h, real_inner_smul_right, inner_correctedGradient_vorticity]
  ring

/-- The residual contains the complete strain defect, paired before norms.
This definition does not assert that its time integral is affordable. -/
def strainDefectWork (κ : ℝ) (u : FourierVelocity) (c : T3 → ℝ) : ℝ :=
  ∫ x : T3, ⟪correctedGradient κ u x,
    fullStrainOperator u x (fullVorticity u x) - c x • fullVorticity u x⟫

theorem integral_correctedGradient_strain_eq_radial_add_defect (κ : ℝ) (P : Finset Wavevector)
    (u : FourierVelocity) (hs : ∀ q, q ∉ P → u q = 0) (c : T3 → ℝ) (hc : Continuous c) :
    (∫ x : T3, ⟪correctedGradient κ u x, fullStrainOperator u x (fullVorticity u x)⟫) =
      8 * (∫ x : T3, c x * correctedDensity κ u x) + strainDefectWork κ u c := by
  have ha := continuous_fullVorticity u (summable_fourierMoment P u hs 1)
  have hJ := continuous_correctedGradient κ P u hs
  have hC : Continuous (correctedDensity κ u) := by
    unfold correctedDensity energy
    exact (((ha.norm.pow 2).pow 4).div_const 8).sub
      ((LocalAngularCurlBudget.continuous_angularCurlDensity u
        (summable_fourierMoment P u hs 1)).const_mul _)
  have hf := ((continuous_fullStrainOperator u (summable_fourierMoment P u hs 1)).clm_apply ha).sub (hc.smul ha)
  have hiC : Integrable (fun x : T3 ↦ 8 * (c x * correctedDensity κ u x)) :=
    ((hc.mul hC).const_mul 8).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiF : Integrable (fun x : T3 ↦ ⟪correctedGradient κ u x,
      fullStrainOperator u x (fullVorticity u x) - c x • fullVorticity u x⟫) :=
    (hJ.inner hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ x : T3, 8 * (c x * correctedDensity κ u x) +
        ⟪correctedGradient κ u x,
          fullStrainOperator u x (fullVorticity u x) - c x • fullVorticity u x⟫ := by
      apply integral_congr_ae
      filter_upwards with x
      simpa only [mul_assoc] using inner_correctedGradient_source κ u x _ (c x)
    _ = _ := by rw [integral_add hiC hiF, integral_const_mul]; rfl

/-- This is the actual all-input source. Mean coercivity does not by itself
bound the spatially weighted corrected density appearing on the right. -/
theorem sourceWork_solution_eq_radial_defect {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (κ : ℝ) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (hχr : ∀ q, χ (-q) = conj (χ q))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (c : T3 → ℝ) (hc : Continuous c) :
    sourceWork κ χ (s.coefficients t) =
      8 * (∫ x : T3, c x * correctedDensity κ (filteredVelocity χ (s.coefficients t)) x) +
      strainDefectWork κ (filteredVelocity χ (s.coefficients t)) c +
      (3 / κ) * deformationIntegral (filteredVelocity χ (s.coefficients t))
        (filteredVelocity χ (s.coefficients t)) + fullSubgridWork κ χ (s.coefficients t) := by
  have hs (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ (s.coefficients t) q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have he := integral_correctedGradient_strain_eq_radial_add_defect κ P _ hs c hc
  rw [integral_correctedGradient_strain κ P _ hs] at he
  rw [sourceWork_solution_eq s κ P χ hcut C hχ hχr t ht, he]

end Mettapedia.FluidDynamics.NavierStokes.FiniteAngularRadialWork
