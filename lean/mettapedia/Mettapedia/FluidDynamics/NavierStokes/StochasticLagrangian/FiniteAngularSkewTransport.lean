import Mettapedia.Analysis.AngularCurlSkewDeformation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteAngularTransportBound
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteAngularInviscidWork

/-!
# Actual rotational transport and the longitudinal-helicity channel

The antisymmetric part of the reconstructed velocity gradient is fixed by
its actual vorticity. Its angular deformation work equals the negative
longitudinal-helicity integral already present in the weighted curl identity.
The symmetric deformation and helicity retain their signs; neither is
declared dissipative or bounded independently of the output cutoff.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteAngularSkewTransport

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeInfiniteSpatialCurl
open PancakeTransverseEnergyFreezing PancakeDyadicDirectionEvolution
open PancakeLocalInfiniteVelocity PancakeFilteredStrainDynamics
open LocalLowDiffusionBudget LocalSpatialVorticityJets FourierFiniteSupport
open FiniteAngularTransport FiniteAngularInviscidWork FilteredAngularSourceBalance
open AngularCurlDecomposition

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def symmetricDerivative (u : FourierVelocity) (j k : Fin 3) (x : T3) : ℝ :=
  (velocityDerivative u j k x + velocityDerivative u k j x) / 2

theorem symmetricDerivative_comm (u : FourierVelocity) (j k : Fin 3) (x : T3) :
    symmetricDerivative u j k x = symmetricDerivative u k j x := by
  unfold symmetricDerivative
  ring

theorem velocityDerivative_eq_symmetric_add_skew (P : Finset Wavevector) (u : FourierVelocity)
    (hu : ∀ q, q ∉ P → u q = 0) (j k : Fin 3) (x : T3) :
    velocityDerivative u j k x = symmetricDerivative u j k x +
      skewDeformation (fullVorticity u x) j k := by
  simp only [symmetricDerivative, velocityDerivative_eq P u hu]
  fin_cases j <;> fin_cases k <;>
    simp [skewDeformation, fullVorticity, spatialCurl, complexRealPartEuclideanCLM_apply,
      complexRealPartEuclidean, Matrix.cons_val_two] <;> ring

def symmetricDeformationDensity (u : FourierVelocity) (x : T3) : ℝ :=
  deformationWork (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)
    (fun j k ↦ symmetricDerivative u j k x)

def symmetricDeformationIntegral (u : FourierVelocity) : ℝ :=
  ∫ x : T3, symmetricDeformationDensity u x

theorem deformationDensity_eq_symmetric_sub_helicity (P : Finset Wavevector) (u : FourierVelocity)
    (hu : ∀ q, q ∉ P → u q = 0) (x : T3) :
    deformationDensity u u x = symmetricDeformationDensity u x -
      longitudinalHelicityDensity (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) := by
  have he : (fun j k ↦ velocityDerivative u j k x) =
      fun j k ↦ symmetricDerivative u j k x + skewDeformation (fullVorticity u x) j k :=
    funext (fun j ↦ funext (fun k ↦ velocityDerivative_eq_symmetric_add_skew P u hu j k x))
  unfold deformationDensity
  rw [he, deformationWork_add, deformationWork_skew_eq_neg_helicity _ _
    (LocalWeightedCurlCancellation.sum_fullCurlGradient_diagonal_eq_zero u
      (summable_fourierMoment P u hu 3) x)]
  rfl

theorem continuous_symmetricDeformationDensity (P : Finset Wavevector) (u : FourierVelocity)
    (hu : ∀ q, q ∉ P → u q = 0) : Continuous (symmetricDeformationDensity u) := by
  have ha := continuous_fullVorticity u (summable_fourierMoment P u hu 1)
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient u
  unfold symmetricDeformationDensity deformationWork deformationStress
  exact continuous_finsetSum Finset.univ (fun j _ ↦ continuous_finsetSum Finset.univ (fun k _ ↦
    (((continuous_velocityDerivative u j k).add (continuous_velocityDerivative u k j)).div_const 2).mul
      ((continuous_jetGradient _ _ ha hD j).inner (hD k))))

theorem deformationIntegral_eq_symmetric_sub_helicity (P : Finset Wavevector) (u : FourierVelocity)
    (hu : ∀ q, q ∉ P → u q = 0) :
    deformationIntegral u u = symmetricDeformationIntegral u - LocalAngularCurlBudget.angularHelicityIntegral u := by
  have ha := continuous_fullVorticity u (summable_fourierMoment P u hu 1)
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient u
  have hH := continuous_angularCurl _ _ ha hD
  have hc : Continuous (fun x : T3 ↦ longitudinalHelicityDensity (fullVorticity u x)
      (fun j ↦ fullCurlGradient u j x)) := by
    unfold longitudinalHelicityDensity
    exact ((ha.norm.pow 2).mul (continuous_finsetSum Finset.univ (fun j _ ↦
      ((PiLp.continuous_apply 2 _ j).comp ha).mul (ha.inner (hD j))))).mul (ha.inner hH)
  have hiS : Integrable (symmetricDeformationDensity u) :=
    (continuous_symmetricDeformationDensity P u hu).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hiH : Integrable (fun x : T3 ↦ longitudinalHelicityDensity (fullVorticity u x)
      (fun j ↦ fullCurlGradient u j x)) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold deformationIntegral
  simp_rw [deformationDensity_eq_symmetric_sub_helicity P u hu]
  rw [integral_sub hiS hiH]
  rfl

theorem sourceWork_solution_eq_symmetric_helicity {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (κ : ℝ) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (hχr : ∀ q, χ (-q) = conj (χ q))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    sourceWork κ χ (s.coefficients t) = LocalVorticityEighthMoment.stretching (filteredVelocity χ (s.coefficients t)) +
      (3 / κ) * (symmetricDeformationIntegral (filteredVelocity χ (s.coefficients t)) -
        angularStrainWork (filteredVelocity χ (s.coefficients t)) -
        LocalAngularCurlBudget.angularHelicityIntegral (filteredVelocity χ (s.coefficients t))) +
      fullSubgridWork κ χ (s.coefficients t) := by
  have hs (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ (s.coefficients t) q = 0 := by
    simp [filteredVelocity, hcut q hq]
  rw [sourceWork_solution_eq s κ P χ hcut C hχ hχr t ht,
    deformationIntegral_eq_symmetric_sub_helicity P _ hs]
  ring

/-- Recombine the exact rotational contribution with the existing weighted
curl identity. The spectral defect and signed helicity are retained. -/
theorem sourceWork_solution_spectral_identity {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (κ : ℝ) (hκ : κ ≠ 0) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (hχr : ∀ q, χ (-q) = conj (χ q))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    κ * sourceWork κ χ (s.coefficients t) =
      3 * symmetricDeformationIntegral (filteredVelocity χ (s.coefficients t)) -
      3 * angularStrainWork (filteredVelocity χ (s.coefficients t)) -
      9 * LocalAngularCurlBudget.angularHelicityIntegral (filteredVelocity χ (s.coefficients t)) -
      LocalWeightedCurlCancellation.weightedStrainSpectralDefect κ (filteredVelocity χ (s.coefficients t)) +
      κ * fullSubgridWork κ χ (s.coefficients t) := by
  have hs (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ (s.coefficients t) q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have hd (q : Wavevector) : modeDot q (filteredVelocity χ (s.coefficients t) q) = 0 := by
    simp only [filteredVelocity, PancakePeriodicCoherentSplit.modeDot_smul, s.transverse t, mul_zero]
  have he := LocalAngularCurlBudget.stretching_spectral_identity _
    (summable_fourierMoment P _ hs 4) hd κ
  calc
    _ = κ * LocalVorticityEighthMoment.stretching (filteredVelocity χ (s.coefficients t)) +
        3 * (symmetricDeformationIntegral (filteredVelocity χ (s.coefficients t)) -
          angularStrainWork (filteredVelocity χ (s.coefficients t)) -
          LocalAngularCurlBudget.angularHelicityIntegral (filteredVelocity χ (s.coefficients t))) +
        κ * fullSubgridWork κ χ (s.coefficients t) := by
      rw [sourceWork_solution_eq_symmetric_helicity s κ P χ hcut C hχ hχr t ht]
      field_simp
    _ = _ := by rw [he]; ring

end Mettapedia.FluidDynamics.NavierStokes.FiniteAngularSkewTransport
