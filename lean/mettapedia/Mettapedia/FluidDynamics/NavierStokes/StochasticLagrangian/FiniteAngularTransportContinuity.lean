import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteAngularTransport

/-!
# Joint continuity of actual finite-output angular transport

The finite coefficients construct the velocity-gradient matrix and all
vorticity first jets jointly in parameter and space. No uniform bound on
derivatives of the full unfiltered input is required for this continuity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteAngularTransportContinuity

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeInfiniteFourierDerivative
open PancakeTransverseEnergyFreezing PancakeDyadicDirectionEvolution
open LocalLowDiffusionBudget LocalSpatialVorticityJets FourierFiniteSupport
open FiniteAngularTransport InfiniteFourierDiffusion
open PancakeLocalInfiniteVelocity PancakeFilteredStrainDynamics

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {Y : Type*} [TopologicalSpace Y]

theorem continuous_velocityDerivative (P : Finset Wavevector) (u : Y → FourierVelocity)
    (hs : ∀ y q, q ∉ P → u y q = 0)
    (hu : ∀ q ∈ P, ∀ i, Continuous (fun y ↦ u y q i)) (j k : Fin 3) :
    Continuous (fun z : Y × T3 ↦ velocityDerivative (u z.1) j k z.2) := by
  have hz (y : Y) (q : Wavevector) (hq : q ∉ P) : indexedDerivativeCoeff id j (u y) q = 0 := by
    simp [indexedDerivativeCoeff, hs y q hq]
  change Continuous (fun z : Y × T3 ↦
    (fullFourierField id (indexedDerivativeCoeff id j (u z.1)) z.2 k).re)
  simp_rw [fullFourierField_eq_sum P _ (hz _)]
  simp only [Finset.sum_apply, Pi.smul_apply, indexedDerivativeCoeff, smul_eq_mul,
    id_eq, Complex.re_sum]
  apply continuous_finsetSum
  intro q hq
  have hqχ := (UnitAddTorus.mFourier q).continuous.comp (continuous_snd : Continuous (fun z : Y × T3 ↦ z.2))
  have hqU := (hu q hq k).comp (continuous_fst : Continuous (fun z : Y × T3 ↦ z.1))
  exact Complex.continuous_re.comp (hqχ.mul (hqU.const_mul
    (PancakePeriodicVorticityEquation.unitTorusDerivativePhase * (q j : ℂ))))

theorem continuous_deformationDensity (P Q : Finset Wavevector) (u v : Y → FourierVelocity)
    (hs : ∀ y q, q ∉ P → u y q = 0) (ht : ∀ y q, q ∉ Q → v y q = 0)
    (hu : ∀ q ∈ P, ∀ i, Continuous (fun y ↦ u y q i))
    (hv : ∀ q ∈ Q, ∀ i, Continuous (fun y ↦ v y q i)) :
    Continuous (fun z : Y × T3 ↦ deformationDensity (u z.1) (v z.1) z.2) := by
  have ha := FilteredProjectionMean.continuous_fullVorticity Q v ht hv
  have hD := FiniteAngularCurlVariation.continuous_fullCurlGradient Q v ht hv
  unfold deformationDensity AngularCurlDecomposition.deformationWork AngularCurlDecomposition.deformationStress
  exact continuous_finsetSum Finset.univ (fun j _ ↦ continuous_finsetSum Finset.univ (fun k _ ↦
    (continuous_velocityDerivative P u hs hu j k).mul
      ((AngularCurlDecomposition.continuous_jetGradient _ _ ha hD j).inner (hD k))))

theorem continuousOn_deformationIntegral {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (P : Finset Wavevector) (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0) :
    ContinuousOn (fun t ↦ deformationIntegral (filteredVelocity χ (s.coefficients t))
      (filteredVelocity χ (s.coefficients t))) (Set.Icc (0 : ℝ) T) := by
  have hs (t : Set.Icc (0 : ℝ) T) (q : Wavevector) (hq : q ∉ P) :
      filteredVelocity χ (s.coefficients t) q = 0 := by simp [filteredVelocity, hcut q hq]
  have hc (q : Wavevector) (_hq : q ∈ P) (i : Fin 3) :
      Continuous (fun t : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients t) q i) :=
    continuous_const.mul ((s.continuous q i).comp continuous_subtype_val)
  have hD : Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      deformationDensity (filteredVelocity χ (s.coefficients z.1))
        (filteredVelocity χ (s.coefficients z.1)) z.2) :=
    continuous_deformationDensity P P
      (fun t : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients t))
      (fun t : Set.Icc (0 : ℝ) T ↦ filteredVelocity χ (s.coefficients t)) hs hs hc hc
  exact LocalAlignmentContinuity.continuousOn_spatialIntegral
    (fun t x ↦ deformationDensity (filteredVelocity χ (s.coefficients t))
      (filteredVelocity χ (s.coefficients t)) x) hD

end Mettapedia.FluidDynamics.NavierStokes.FiniteAngularTransportContinuity
