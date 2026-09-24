import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityAnnularPolynomialSource

/-!
# Time continuity of actual annular source integrals

A common local Fourier envelope gives continuity through the initial endpoint.
The high-amplitude weight is continuous at threshold and equal-amplitude
interfaces; no differentiability of that weight is needed here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourceContinuity

open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity LocalAlignmentContinuity
open LocalLowDiffusionBudget VorticityAnnularPolynomialSource
open Mettapedia.Analysis SignedCrossKernel
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem continuousOn_pairIntegral {T : ℝ} (f : ℝ → T3 → T3 → ℝ)
    (hf : Continuous (fun z : Set.Icc (0 : ℝ) T × (T3 × T3) ↦ f z.1 z.2.1 z.2.2)) :
    ContinuousOn (fun t ↦ ∫ x : T3, ∫ y : T3, f t x y) (Set.Icc (0 : ℝ) T) := by
  apply continuousOn_spatialIntegral
  have h := continuous_parametric_integral_of_continuous (μ := (volume : Measure T3))
    (f := fun z : Set.Icc (0 : ℝ) T × T3 ↦ fun y ↦ f z.1 z.2 y)
    (hf.comp (f := fun z : (Set.Icc (0 : ℝ) T × T3) × T3 ↦
      (z.1.1, (z.1.2, z.2))) (by fun_prop)) isCompact_univ
  simpa only [Measure.restrict_univ] using h

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hSum : Summable g)
  (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q)

include hSum hu

theorem continuous_pairedDensity (n N : ℕ) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × (T3 × T3) ↦
      pairedStretch n (PeriodicRieszPolynomial.kernel N (z.2.1 - z.2.2))
        (fullVorticity (s.coefficients z.1) z.2.1)
        (fullVorticity (s.coefficients z.1) z.2.2)) := by
  have hw := continuous_fullVorticity_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q))
  have hK : Continuous (fun p : (Set.Icc (0 : ℝ) T × T3) × (Set.Icc (0 : ℝ) T × T3) ↦
      PeriodicRieszPolynomial.kernel N (p.1.2 - p.2.2)) :=
    (PeriodicRieszPolynomial.continuous_kernel N).comp (continuous_fst.snd.sub continuous_snd.snd)
  have h := continuous_pairedStretch
    (fun x y : Set.Icc (0 : ℝ) T × T3 ↦ PeriodicRieszPolynomial.kernel N (x.2 - y.2))
    (fun x : Set.Icc (0 : ℝ) T × T3 ↦ fullVorticity (s.coefficients x.1) x.2)
    hK hw n
  exact h.comp (f := fun z : Set.Icc (0 : ℝ) T × (T3 × T3) ↦
    ((z.1, z.2.1), (z.1, z.2.2))) (by fun_prop)

theorem continuous_highAmplitudeDensity (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × (T3 × T3) ↦
      highAmplitudeStretch n L (PeriodicRieszPolynomial.kernel N (z.2.1 - z.2.2))
        (fullVorticity (s.coefficients z.1) z.2.1)
        (fullVorticity (s.coefficients z.1) z.2.2)) := by
  have hw := continuous_fullVorticity_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q))
  have hK : Continuous (fun p : (Set.Icc (0 : ℝ) T × T3) × (Set.Icc (0 : ℝ) T × T3) ↦
      PeriodicRieszPolynomial.kernel N (p.1.2 - p.2.2)) :=
    (PeriodicRieszPolynomial.continuous_kernel N).comp (continuous_fst.snd.sub continuous_snd.snd)
  have h := continuous_highAmplitudeStretch
    (fun x y : Set.Icc (0 : ℝ) T × T3 ↦ PeriodicRieszPolynomial.kernel N (x.2 - y.2))
    (fun x : Set.Icc (0 : ℝ) T × T3 ↦ fullVorticity (s.coefficients x.1) x.2)
    hK hw n L hL
  exact h.comp (f := fun z : Set.Icc (0 : ℝ) T × (T3 × T3) ↦
    ((z.1, z.2.1), (z.1, z.2.2))) (by fun_prop)

theorem continuousOn_pairedSource (n N : ℕ) :
    ContinuousOn (fun t ↦ pairedSource n N (s.coefficients t)) (Set.Icc (0 : ℝ) T) :=
  (continuousOn_pairIntegral _ (continuous_pairedDensity s g hSum hu n N)).const_mul _

theorem continuousOn_highAmplitudeSource (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    ContinuousOn (fun t ↦ highAmplitudeSource n L N (s.coefficients t)) (Set.Icc (0 : ℝ) T) :=
  (continuousOn_pairIntegral _ (continuous_highAmplitudeDensity s g hSum hu n N L hL)).const_mul _

end Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourceContinuity
