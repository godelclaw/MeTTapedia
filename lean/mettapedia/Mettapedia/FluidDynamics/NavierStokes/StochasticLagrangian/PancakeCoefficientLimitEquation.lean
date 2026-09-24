import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeVelocityPathLimit
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.Order.ProjIcc

/-!
# The coefficient limit satisfies the infinite nonlinear velocity equation

Uniform convergence of the actual Galerkin right-hand sides passes the
differential equation to each nonzero output on the open local interval.
Constant extension outside the closed interval only supplies a real-domain
representative; no evolution is asserted outside the local interval.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeCoefficientLimitEquation

open scoped BigOperators Topology
open Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeGalerkinCoefficientLimit PancakeCoefficientLimitProperties
open PancakeConvectionPathLimit PancakeVelocityPathLimit PancakeSobolevFiberEnvelope
open PancakeLocalVelocityExistence PancakeGalerkinKineticEnergy PancakeSobolevVelocityRate
open PancakePeriodicVorticityEquation

def infiniteConvection (u : FourierVelocity) (q : Wavevector) : VelocityCoefficient :=
  fun i ↦ ∑' k, outputFiber q u k i

def infiniteVelocityRHS (nu : ℝ) (u : FourierVelocity) (q : Wavevector) : VelocityCoefficient :=
  lerayMode q ((-unitTorusDerivativePhase) • infiniteConvection u q) +
    unitTorusViscousVorticityCoeff nu u q

theorem velocityPath_apply {T : ℝ} (nu : ℝ) (q : Wavevector) (a : CoefficientLimit T)
    (B : ℝ) (hB : 0 ≤ B) (hE : ∀ t F, sobolevEnergy F (limitField a t) ≤ B)
    (i : Fin 3) (t : Set.Icc (0 : ℝ) T) :
    velocityPath nu q a i t = infiniteVelocityRHS nu (limitField a t) q i := by
  simp only [velocityPath, BoundedContinuousFunction.add_apply, lerayPath_apply,
    BoundedContinuousFunction.smul_apply, convectionPath_apply q a B hB hE,
    infiniteVelocityRHS, Pi.add_apply, unitTorusViscousVorticityCoeff,
    Pi.smul_apply]
  rfl

def coefficientCurve {T : ℝ} (a : CoefficientLimit T) (hT : 0 ≤ T) : ℝ → FourierVelocity :=
  fun t q i ↦ Set.IccExtend hT (a q i) t

theorem coefficientCurve_apply {T : ℝ} (a : CoefficientLimit T) (hT : 0 ≤ T)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    coefficientCurve a hT t = limitField a ⟨t, ht⟩ := by
  ext q i
  exact Set.IccExtend_of_mem hT (a q i) ht

theorem continuous_coefficientCurve {T : ℝ} (a : CoefficientLimit T) (hT : 0 ≤ T)
    (q : Wavevector) (i : Fin 3) : Continuous (fun t ↦ coefficientCurve a hT t q i) :=
  (a q i).continuous.Icc_extend'

theorem infiniteVelocityRHS_zero (nu : ℝ) (u : FourierVelocity) :
    infiniteVelocityRHS nu u 0 = 0 := by
  ext i
  simp [infiniteVelocityRHS, infiniteConvection, outputFiber, modeDot, modeSquare,
    unitTorusViscousVorticityCoeff, lerayMode]

variable {nu T : ℝ} {u₀ : FourierVelocity}
  (s : ∀ n, LocalVelocitySolution (galerkinModes n) nu u₀ T)
  (phi : ℕ → ℕ) (a : CoefficientLimit T) (h : IsCoefficientLimit s phi a)

include h

theorem coefficientLimit_hasDerivAt_nonzero (hphi : StrictMono phi) (hT : 0 ≤ T)
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      sobolevEnergy (galerkinModes n) ((s n).coefficients t) ≤ B)
    (q : Wavevector) (hq : q ≠ 0) (i : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ coefficientCurve a hT τ q i)
      (infiniteVelocityRHS nu (coefficientCurve a hT t) q i) t := by
  have hu : TendstoUniformlyOn
      (fun n τ ↦ velocityRHS (galerkinModes (phi n)) ((s (phi n)).coefficients τ) nu q i)
      (Set.IccExtend hT (velocityPath nu q a i)) atTop (Set.Icc (0 : ℝ) T) := by
    apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    simpa only [Function.comp_def, Set.IccExtend_val] using
      coefficientLimit_velocity_uniform s phi a h B hB hE q i
  have hd := hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo
    (hu.mono Set.Ioo_subset_Icc_self)
    (show ∀ᶠ n in atTop, ∀ τ ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun r ↦ (s (phi n)).coefficients r q i)
        (velocityRHS (galerkinModes (phi n)) ((s (phi n)).coefficients τ) nu q i) τ from by
      filter_upwards [hphi.tendsto_atTop.eventually (eventually_mem_galerkinModes q hq)] with n hn
      intro τ hτ
      exact (s (phi n)).equation τ ⟨hτ.1.le, hτ.2.le⟩ q hn i)
    (show ∀ τ ∈ Set.Ioo (0 : ℝ) T,
      Tendsto (fun n ↦ (s (phi n)).coefficients τ q i)
        atTop (𝓝 (coefficientCurve a hT τ q i)) from by
      intro τ hτ
      rw [coefficientCurve_apply a hT τ ⟨hτ.1.le, hτ.2.le⟩]
      exact (h q i).tendsto_at ⟨τ, hτ.1.le, hτ.2.le⟩) ht
  rw [Set.IccExtend_of_mem hT _ ⟨ht.1.le, ht.2.le⟩,
    velocityPath_apply nu q a B hB (limitField_finite_sobolev_bound s phi a h B hE)] at hd
  rwa [coefficientCurve_apply a hT t ⟨ht.1.le, ht.2.le⟩]

theorem coefficientLimit_hasDerivAt (hphi : StrictMono phi) (hT : 0 ≤ T)
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      sobolevEnergy (galerkinModes n) ((s n).coefficients t) ≤ B)
    (q : Wavevector) (i : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ coefficientCurve a hT τ q i)
      (infiniteVelocityRHS nu (coefficientCurve a hT t) q i) t := by
  by_cases hq : q = 0
  · subst q
    have hz (τ : ℝ) : coefficientCurve a hT τ 0 i = 0 :=
      congrFun (limitField_zero s phi a h (Set.projIcc 0 T hT τ)) i
    have hf : (fun τ ↦ coefficientCurve a hT τ 0 i) = fun _ ↦ (0 : ℂ) := funext hz
    rw [hf, infiniteVelocityRHS_zero]
    exact hasDerivAt_const t 0
  · exact coefficientLimit_hasDerivAt_nonzero s phi a h hphi hT B hB hE q hq i t ht

end Mettapedia.FluidDynamics.NavierStokes.PancakeCoefficientLimitEquation
