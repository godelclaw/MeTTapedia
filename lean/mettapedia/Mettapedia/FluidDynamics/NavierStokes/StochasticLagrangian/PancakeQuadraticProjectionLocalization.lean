import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCutoffBoundarySupport
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeAdaptiveFourierFreezing

/-!
# Adaptive quadratic localization of the projection pairing

The nonnegative Fourier weights are the previously constructed squared
polynomials. Their frozen contributions are exact exterior Fourier fields.
Coverage error is kept as a separate term; approximate partition weights
are not treated as an exact partition of unity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeQuadraticProjectionLocalization

open MeasureTheory
open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeMisalignmentEnergyBridge
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing PancakeBlockReality
open PancakeFiniteFourierLocalization PancakeLocalizedProjectionBoundary PancakeCutoffBoundarySupport
open PancakeQuadraticFourierSupport PancakeAdaptiveFourierFreezing PancakeRetainedProjectionDefect
open PancakePhysicalSpectralDefect PancakeGalerkinKineticEnergy PancakeMaterialDiffusionBudget

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def quadraticWeight (c : FourierCoeff (Fin 3)) (x : T3) : ℝ :=
  Complex.normSq (fourierPolynomial c x)

def quadraticBoundaryField (c : FourierCoeff (Fin 3)) (modes : Finset Wavevector)
    (w : FourierVelocity) : T3 → R3 :=
  localizedBoundaryField (quadraticFourierCoeff c).support modes (quadraticFourierCoeff c) w

theorem continuous_quadraticWeight (c : FourierCoeff (Fin 3)) : Continuous (quadraticWeight c) :=
  Complex.continuous_normSq.comp (fourierPolynomial c).continuous

theorem scalarReconstruction_eq_fourierPolynomial (c : FourierCoeff (Fin 3)) (x : T3) :
    finiteScalarFourierReconstruction c.support c x = fourierPolynomial c x := by
  simp only [finiteScalarFourierReconstruction, fourierPolynomial_apply, Finsupp.sum, mul_comm]

theorem scalarReconstruction_quadratic (c : FourierCoeff (Fin 3)) (x : T3) :
    finiteScalarFourierReconstruction (quadraticFourierCoeff c).support (quadraticFourierCoeff c) x =
      (quadraticWeight c x : ℂ) := by
  rw [scalarReconstruction_eq_fourierPolynomial, fourierPolynomial_quadraticFourierCoeff]
  rfl

theorem integral_quadratic_pairing_eq_boundary (c : FourierCoeff (Fin 3))
    (modes outputs : Finset Wavevector) (w : FourierVelocity) (u : FourierVelocity)
    (A : R3 →L[ℝ] R3) (hs : ∀ q, -q ∈ modes ↔ q ∈ modes) :
    (∫ x : T3, ⟪A (quadraticWeight c x • complexRealPartEuclidean (finiteFourierReconstruction modes w x)),
      discardedNonlinearField modes outputs u x⟫) =
      ∫ x : T3, ⟪A (quadraticBoundaryField c modes w x), discardedNonlinearField modes outputs u x⟫ := by
  have h := integral_localized_pairing_eq_boundary (quadraticFourierCoeff c).support modes outputs
    (quadraticFourierCoeff c) w u A (fun x ↦ by rw [scalarReconstruction_quadratic]; rfl) hs
  simpa only [scalarReconstruction_quadratic, Complex.ofReal_re, quadraticBoundaryField] using h

theorem quadraticBoundaryField_zero_of_candidate_buffer (c : FourierCoeff (Fin 3))
    (modes : Finset Wavevector) (w : FourierVelocity)
    (hbuffer : ∀ k ∈ modes, w k ≠ 0 → ∀ p ∈ quadraticFrequencySet c, p + k ∈ modes) (x : T3) :
    quadraticBoundaryField c modes w x = 0 := by
  apply localizedBoundaryField_eq_zero_of_buffered_support
  intro k hk hw p hp
  exact hbuffer k hk hw p (quadraticFourierCoeff_support_subset c hp)

theorem weighted_freezing_decomposition {ι : Type*} [Fintype ι]
    (rho : ι → ℝ) (A : ι → R3 →L[ℝ] R3) (K : R3 →L[ℝ] R3) (w d : R3) :
    ⟪K w,d⟫ = (∑ i : ι, rho i * ⟪(K - A i) w,d⟫) +
      (∑ i : ι, ⟪A i (rho i • w),d⟫) + (1 - ∑ i : ι, rho i) * ⟪K w,d⟫ := by
  simp only [sub_apply, inner_sub_left, mul_sub, map_smul, real_inner_smul_left,
    Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

theorem integral_quadratic_freezing_decomposition {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (modes outputs : Finset Wavevector) (u : FourierVelocity)
    (K : T3 → R3 →L[ℝ] R3) (A : ι → R3 →L[ℝ] R3)
    (hK : Continuous K) (hs : ∀ q, -q ∈ modes ↔ q ∈ modes) :
    (∫ x : T3, ⟪K x (spatialVorticity modes u x), discardedNonlinearField modes outputs u x⟫) =
      (∫ x : T3, ∑ i : ι, quadraticWeight (c i) x *
        ⟪(K x - A i) (spatialVorticity modes u x), discardedNonlinearField modes outputs u x⟫) +
      (∑ i : ι, ∫ x : T3, ⟪A i (quadraticBoundaryField (c i) modes (fourierCurl u) x),
        discardedNonlinearField modes outputs u x⟫) +
      ∫ x : T3, (1 - ∑ i : ι, quadraticWeight (c i) x) *
        ⟪K x (spatialVorticity modes u x), discardedNonlinearField modes outputs u x⟫ := by
  have hw := continuous_vorticity modes u
  have hd := continuous_discardedNonlinearField modes outputs u
  let F := fun (x : T3) ↦ ∑ i : ι, quadraticWeight (c i) x *
    ⟪(K x - A i) (spatialVorticity modes u x), discardedNonlinearField modes outputs u x⟫
  let G := fun (i : ι) (x : T3) ↦ ⟪A i (quadraticWeight (c i) x • spatialVorticity modes u x),
    discardedNonlinearField modes outputs u x⟫
  let H := fun (x : T3) ↦ (1 - ∑ i : ι, quadraticWeight (c i) x) *
    ⟪K x (spatialVorticity modes u x), discardedNonlinearField modes outputs u x⟫
  have hFc : Continuous F := continuous_finsetSum _ (fun i _ ↦
    (continuous_quadraticWeight (c i)).mul (((hK.sub continuous_const).clm_apply hw).inner hd))
  have hGc : ∀ i, Continuous (G i) := fun i ↦
    (A i).continuous.comp ((continuous_quadraticWeight (c i)).smul hw) |>.inner hd
  have hHc : Continuous H :=
    (continuous_const.sub (continuous_finsetSum _ (fun i _ ↦ continuous_quadraticWeight (c i)))).mul
      ((hK.clm_apply hw).inner hd)
  have hF := hFc.integrable_of_hasCompactSupport (μ := volume) (HasCompactSupport.of_compactSpace _)
  have hG : ∀ i, Integrable (G i) := fun i ↦ (hGc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hGsum : Integrable (fun x : T3 ↦ ∑ i : ι, G i x) := integrable_finsetSum _ (fun i _ ↦ hG i)
  have hFG : Integrable (fun x : T3 ↦ F x + ∑ i : ι, G i x) := hF.add hGsum
  have hH := hHc.integrable_of_hasCompactSupport (μ := volume) (HasCompactSupport.of_compactSpace _)
  have he : ∀ x : T3, ⟪K x (spatialVorticity modes u x), discardedNonlinearField modes outputs u x⟫ =
      (F x + ∑ i : ι, G i x) + H x := fun x ↦
    weighted_freezing_decomposition (fun i ↦ quadraticWeight (c i) x) A (K x) _ _
  rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_add hFG hH,
    integral_add hF hGsum, integral_finsetSum Finset.univ (fun i _ ↦ hG i)]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact integral_quadratic_pairing_eq_boundary (c i) modes outputs (fourierCurl u) u (A i) hs

end Mettapedia.FluidDynamics.NavierStokes.PancakeQuadraticProjectionLocalization
