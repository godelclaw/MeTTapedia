import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCoefficientLimitEquation

/-!
# Local infinite Fourier velocity solutions from physical initial data

This is an existence result for the infinite coefficient equations, with
reality, incompressibility, zero mean, and a common second-order energy bound.
It does not assert spatial smoothness or global continuation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalInfiniteVelocity

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeBlockReality
open PancakeGalerkinCoefficientLimit PancakeCoefficientLimitProperties
open PancakeCoefficientLimitEquation PancakeSobolevFiberEnvelope
open PancakeSobolevVelocityRate PancakeSobolevWeights PancakeLocalVelocityExistence
open PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks

structure LocalInfiniteVelocitySolution (nu : ℝ) (u₀ : FourierVelocity) (T B : ℝ) where
  coefficients : ℝ → FourierVelocity
  continuous : ∀ q i, Continuous (fun t ↦ coefficients t q i)
  initial : coefficients 0 = u₀
  reality : ∀ t q, coefficients t (-q) = coefficientConjugate (coefficients t q)
  transverse : ∀ t q, modeDot q (coefficients t q) = 0
  zero : ∀ t, coefficients t 0 = 0
  sobolev_bound : ∀ t, t ∈ Set.Icc (0 : ℝ) T →
    ∀ F : Finset Wavevector, sobolevEnergy F (coefficients t) ≤ B
  equation : ∀ t, t ∈ Set.Ioo (0 : ℝ) T → ∀ q i,
    HasDerivAt (fun τ ↦ coefficients τ q i) (infiniteVelocityRHS nu (coefficients t) q i) t

theorem LocalInfiniteVelocitySolution.summable_convection
    {nu T B : ℝ} {u₀ : FourierVelocity} (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) (i : Fin 3) :
    Summable (fun k ↦ outputFiber q (s.coefficients t) k i) :=
  summable_outputFiber _ B (s.sobolev_bound t ht) q i

theorem LocalInfiniteVelocitySolution.summable_sobolev
    {nu T B : ℝ} {u₀ : FourierVelocity} (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Summable (fun q ↦ (weight q * amplitude (s.coefficients t) q)^2) ∧
      (∑' q, (weight q * amplitude (s.coefficients t) q)^2) ≤ B := by
  have hb (F : Finset Wavevector) :
      (∑ q ∈ F, (weight q * amplitude (s.coefficients t) q)^2) ≤ B :=
    s.sobolev_bound t ht F
  exact ⟨summable_of_sum_le (fun _ ↦ sq_nonneg _) hb,
    Real.tsum_le_of_sum_le (fun _ ↦ sq_nonneg _) hb⟩

theorem nonempty_localInfiniteVelocitySolution {nu T : ℝ} {u₀ : FourierVelocity}
    (s : ∀ n, LocalVelocitySolution (galerkinModes n) nu u₀ T)
    (phi : ℕ → ℕ) (a : CoefficientLimit T) (h : IsCoefficientLimit s phi a)
    (hphi : StrictMono phi) (hT : 0 ≤ T) (hzero : u₀ 0 = 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      sobolevEnergy (galerkinModes n) ((s n).coefficients t) ≤ B) :
    Nonempty (LocalInfiniteVelocitySolution nu u₀ T B) := by
  refine ⟨{
    coefficients := coefficientCurve a hT
    continuous := continuous_coefficientCurve a hT
    initial := ?_
    reality := ?_
    transverse := ?_
    zero := ?_
    sobolev_bound := ?_
    equation := ?_ }⟩
  · rw [coefficientCurve_apply a hT 0 ⟨le_rfl, hT⟩]
    exact limitField_initial s phi a h hphi hT hzero
  · intro t q
    exact limitField_reality s phi a h (Set.projIcc 0 T hT t) q
  · intro t q
    exact limitField_transverse s phi a h (Set.projIcc 0 T hT t) q
  · intro t
    exact limitField_zero s phi a h (Set.projIcc 0 T hT t)
  · intro t ht F
    rw [coefficientCurve_apply a hT t ht]
    exact limitField_finite_sobolev_bound s phi a h B hE ⟨t, ht⟩ F
  · intro t ht q i
    exact coefficientLimit_hasDerivAt s phi a h hphi hT B hB hE q i t ht

local notation "T3" => UnitAddTorus (Fin 3)

/-- The input is the initial physical field, not a supplied evolution or an
assumed nonlinear limit. The zero Fourier coefficient is explicitly excluded
by the mean-zero hypothesis. -/
theorem exists_physical_localInfiniteVelocitySolution (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 6 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ k, modeDot k (torusFourierVelocity f k) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      Nonempty (LocalInfiniteVelocitySolution nu (torusFourierVelocity f) T B) := by
  obtain ⟨T, hT, B, hB, H, hH, s, a, phi, hphi, hb, ha⟩ :=
    exists_physical_galerkin_coefficient_limit nu hnu f hf hr hd
  exact ⟨T, hT, B, hB, nonempty_localInfiniteVelocitySolution s phi a ha hphi hT.le
    hzero B hB (fun n t ht ↦ (hb n t ht).1)⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalInfiniteVelocity
