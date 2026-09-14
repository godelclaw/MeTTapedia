import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxProjectedDiffusion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalStretchingFluxBalance

/-!
# Dissipative balance from the actual periodic initial data

The local solution supplies continuity and integrability of the projected
gradient dissipation. The accumulated signed work still contains the
pressure, deformation-residual, and mixed derivative contributions.
This exact balance does not assert a global estimate for that work.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalStretchingFluxDissipation

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis ContinuousFieldBilinear UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakeHigherDerivativeMoments
open LocalVorticityDiffusion
open PancakeCurlOutputTail PancakeDyadicDirectionEvolution PancakeLocalInfiniteVelocity
open PancakeHigherLocalVelocity PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks
open LongitudinalVorticityTime LongitudinalGradientFlux LocalStretchingFluxTime
open StretchingFluxMaterialRate StretchingFluxProjectedEvolution StretchingFluxSpatialDiffusion
open StretchingFluxProjectedDiffusion LocalStretchingFluxBalance

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- All signed contributions other than the extracted negative dissipation. -/
def drivingWork (ν : ℝ) (u : FourierVelocity) : ℝ :=
  materialWork 0 u - transportWork u + 2 * ν * mixedWork u

theorem drivingWork_eq (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) :
    drivingWork ν u = materialWork ν u - transportWork u + ν * dissipation u := by
  have he := materialWork_add_dissipation ν u hu hd hr
  unfold drivingWork
  linarith

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B) (hB : 0 ≤ B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hSum hu

theorem continuousOn_vorticityGradientField (k : Fin 3) :
    ContinuousOn (fun t ↦ LongitudinalVorticityTime.gradientField (s.coefficients t) k)
      (Set.Icc (0 : ℝ) T) := by
  rw [continuousOn_iff_continuous_restrict]
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact LocalVorticityEighthMoment.continuous_fullCurlGradient_spaceTime s g hSum hu k

theorem continuousOn_velocitySecondDerivativeField (j k : Fin 3) :
    ContinuousOn (fun t ↦ velocitySecondDerivativeField (s.coefficients t) j k)
      (Set.Icc (0 : ℝ) T) := by
  rw [continuousOn_iff_continuous_restrict]
  apply (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).continuous.comp
  refine continuous_fullFourierField_of_norm_le _ ?_ (fun q ↦ (2 * Real.pi) ^ 2 * g q)
    (hSum.mul_left _) ?_
  · intro q i
    have hc : Continuous (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t q i) :=
      (s.continuous q i).comp continuous_subtype_val
    simp only [indexedDerivativeCoeff, Pi.smul_apply, smul_eq_mul]
    fun_prop
  · intro t q
    calc
      _ ≤ fourierMoment 0 (indexedDerivativeCoeff id k
          (indexedDerivativeCoeff id j (s.coefficients t))) q := by
        simpa only [fourierMoment, pow_zero, one_mul] using norm_coefficient_sup_le_euclidean
          (indexedDerivativeCoeff id k (indexedDerivativeCoeff id j (s.coefficients t)) q)
      _ ≤ (2 * Real.pi) * fourierMoment 1 (indexedDerivativeCoeff id j (s.coefficients t)) q :=
        fourierMoment_derivative_le 0 _ k q
      _ ≤ (2 * Real.pi) * ((2 * Real.pi) * fourierMoment 2 (s.coefficients t) q) :=
        mul_le_mul_of_nonneg_left (fourierMoment_derivative_le 1 _ j q) (by positivity)
      _ ≤ (2 * Real.pi) * ((2 * Real.pi) * g q) := by
        gcongr
        exact (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t t.2 q)
      _ = _ := by ring

theorem continuousOn_stretchingGradientField (k : Fin 3) :
    ContinuousOn (fun t ↦ stretchingGradientField (s.coefficients t) k)
      (Set.Icc (0 : ℝ) T) := by
  apply continuousOn_finsetSum
  intro j _
  apply ContinuousOn.add
  · exact ((pointwiseCLM (ContinuousLinearMap.lsmul ℝ ℝ)).continuous.comp_continuousOn
      ((componentField j).continuous.comp_continuousOn
        (continuousOn_vorticityField s g hSum hu))).clm_apply
          (continuousOn_velocitySecondDerivativeField s g hSum hu j k)
  · exact ((pointwiseCLM (ContinuousLinearMap.lsmul ℝ ℝ)).continuous.comp_continuousOn
      ((componentField j).continuous.comp_continuousOn
        (continuousOn_vorticityGradientField s g hSum hu k))).clm_apply
          (continuousOn_velocityDerivativeField s g hSum hu j)

theorem continuousOn_fluxGradientField (j k : Fin 3) :
    ContinuousOn (fun t ↦ fluxGradientField (s.coefficients t) j k)
      (Set.Icc (0 : ℝ) T) := by
  apply ContinuousOn.neg
  apply ContinuousOn.add
  · exact ((pointwiseCLM (ContinuousLinearMap.lsmul ℝ ℝ)).continuous.comp_continuousOn
      ((componentField j).continuous.comp_continuousOn
        (continuousOn_vorticityField s g hSum hu))).clm_apply
          (continuousOn_stretchingGradientField s g hSum hu k)
  · exact ((pointwiseCLM (ContinuousLinearMap.lsmul ℝ ℝ)).continuous.comp_continuousOn
      ((componentField j).continuous.comp_continuousOn
        (continuousOn_vorticityGradientField s g hSum hu k))).clm_apply
          (continuousOn_stretchingField s g hSum hu)

theorem continuousOn_dissipation :
    ContinuousOn (fun t ↦ dissipation (s.coefficients t)) (Set.Icc (0 : ℝ) T) := by
  apply continuousOn_finsetSum
  intro k _
  exact ((((gradientProjectionCLM (d := Fin 3) (E := R3)).comp
    (tensorEmbedding (d := Fin 3) (E := R3))).continuous.comp_continuousOn
      (continuousOn_pi.mpr (fun j ↦ continuousOn_fluxGradientField s g hSum hu j k))).norm).pow 2

theorem intervalIntegrable_dissipation {a b : ℝ} (hab : a ≤ b)
    (hI : Set.Icc a b ⊆ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun t ↦ dissipation (s.coefficients t)) volume a b :=
  ContinuousOn.intervalIntegrable_of_Icc hab ((continuousOn_dissipation s g hSum hu).mono hI)

include hg in
theorem hasDerivAt_projectedFluxSquare (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ projectedFluxSquare 0 (s.coefficients τ))
      (2 * (drivingWork ν (s.coefficients t) - ν * dissipation (s.coefficients t))) t := by
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  rw [drivingWork_eq ν _ hm (s.transverse t) (s.reality t), add_sub_cancel_right]
  exact StretchingFluxProjectedEvolution.hasDerivAt_projectedFluxSquare s g hg hSum hu t ht

include hB hg

theorem continuousOn_drivingWork :
    ContinuousOn (fun t ↦ drivingWork ν (s.coefficients t)) (Set.Icc (0 : ℝ) T) := by
  apply ((continuousOn_signed_work s hB g hg hSum hu).add
    ((continuousOn_dissipation s g hSum hu).const_mul ν)).congr
  intro t ht
  exact drivingWork_eq ν _
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht))
      (s.transverse t) (s.reality t)

theorem intervalIntegrable_drivingWork {a b : ℝ} (hab : a ≤ b)
    (hI : Set.Icc a b ⊆ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (fun t ↦ drivingWork ν (s.coefficients t)) volume a b :=
  ContinuousOn.intervalIntegrable_of_Icc hab ((continuousOn_drivingWork s hB g hg hSum hu).mono hI)

/-- The full dissipation is placed on the left, with no unsigned replacement
of the pressure, projection-transport, or mixed work on the right. -/
theorem energy_identity {a b : ℝ} (hab : a ≤ b)
    (hI : Set.Icc a b ⊆ Set.Icc (0 : ℝ) T) :
    projectedFluxSquare 0 (s.coefficients b) +
        2 * ν * ∫ t in a..b, dissipation (s.coefficients t) =
      projectedFluxSquare 0 (s.coefficients a) +
        2 * ∫ t in a..b, drivingWork ν (s.coefficients t) := by
  have he := LocalStretchingFluxBalance.energy_identity s hB g hg hSum hu hab hI
  have hi : (∫ t in a..b, drivingWork ν (s.coefficients t)) =
      (∫ t in a..b, materialWork ν (s.coefficients t) - transportWork (s.coefficients t)) +
        ν * ∫ t in a..b, dissipation (s.coefficients t) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add
        (intervalIntegrable_signed_work s hB g hg hSum hu hab hI)
        ((intervalIntegrable_dissipation s g hSum hu hab hI).const_mul ν)]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' := hI (show t ∈ Set.Icc a b from by simpa only [Set.uIcc_of_le hab] using ht)
    exact drivingWork_eq ν _ (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht'))
      (s.transverse t) (s.reality t)
  linarith

theorem energy_identity_from_initial (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    projectedFluxSquare 0 (s.coefficients t) +
        2 * ν * ∫ τ in (0 : ℝ)..t, dissipation (s.coefficients τ) =
      projectedFluxSquare 0 u₀ + 2 * ∫ τ in (0 : ℝ)..t, drivingWork ν (s.coefficients τ) := by
  simpa only [s.initial] using energy_identity s hB g hg hSum hu ht.1
    (fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩)

omit hB hg hSum hu in
/-- The physical initial field constructs the local solution, its spatial
derivatives, and the integrals in the dissipative identity. -/
theorem exists_physical_local_dissipative_balance (ν : ℝ) (hν : 0 < ν)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution ν (torusFourierVelocity f) T B,
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          projectedFluxSquare 0 (s.coefficients t) +
              2 * ν * ∫ τ in (0 : ℝ)..t, dissipation (s.coefficients τ) =
            projectedFluxSquare 0 (torusFourierVelocity f) +
              2 * ∫ τ in (0 : ℝ)..t, drivingWork ν (s.coefficients τ) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 3 ν hν f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, fun t ht ↦ energy_identity_from_initial s hB g hg hSum hu t ht⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalStretchingFluxDissipation
