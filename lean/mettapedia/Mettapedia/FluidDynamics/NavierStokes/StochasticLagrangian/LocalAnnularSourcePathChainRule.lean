import Mettapedia.Analysis.HighAmplitudeWeightChainRule
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityPathRegularity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularSourcePathIntegral

/-!
# Actual signed material source rate, including amplitude interfaces

The full branch-selected rate is the almost-everywhere derivative along
actual material paths. At an equal-amplitude contact either endpoint gives
the same derivative wherever it exists; at the threshold it is zero.
The kernel transport, radial strain excess and viscosity terms remain
explicit. The resulting signed identity is not a uniform budget estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourcePathChainRule

open Filter MeasureTheory
open PeriodicFourierTriad PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity
open PancakeCurlOutputTail PancakeFourierMaterialPaths LocalLowDiffusionBudget LocalJointDiffusionBudget
open LocalAlignmentForcing LocalVorticityPathRegularity LocalAnnularSourcePathIntegral
open PancakeLocalMaterialTrajectories
open Mettapedia.Analysis SignedCrossKernel
local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

def materialHighAmplitudeRate (n N : ℕ) (L : ℝ) (u : FourierVelocity)
    (nu : ℝ) (x y : T3) (v w : X3) : ℝ :=
  highAmplitudeWeightRate L (fullVorticity u x) (fullVorticity u y)
      (fullStrainOperator u x (fullVorticity u x) + nu • fullVorticityLaplacian u x)
      (fullStrainOperator u y (fullVorticity u y) + nu • fullVorticityLaplacian u y) *
    pairedStretch (2 * (n + 1)) (PeriodicRieszPolynomial.kernel N (x - y))
      (fullVorticity u x) (fullVorticity u y) +
  (1 - lowAmplitudeWeight L (fullVorticity u x) (fullVorticity u y)) *
    LocalAnnularStretchEvolution.materialPairedRate n N u nu x y v w

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
  (X Y : ℝ → X3) (hX : LocallyLipschitz X) (hY : LocallyLipschitz Y)
  (hDX : ∀ t ∈ Set.Ioo a b, HasDerivAt X (liftedVelocity s t (X t)) t)
  (hDY : ∀ t ∈ Set.Ioo a b, HasDerivAt Y (liftedVelocity s t (Y t)) t)

include hg hSum hu hab hI hX hY hDX hDY

theorem ae_hasDerivAt_highAmplitudeSource_path (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    ∀ᵐ t, t ∈ Set.Ioo a b → HasDerivAt (fun τ ↦ highAmplitudeStretch (2 * (n + 1)) L
      (PeriodicRieszPolynomial.kernel N (torusPoint (X τ) - torusPoint (Y τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (Y τ))))
      (materialHighAmplitudeRate n N L (s.coefficients t) nu (torusPoint (X t)) (torusPoint (Y t))
        (liftedVelocity s t (X t)) (liftedVelocity s t (Y t))) t := by
  have hac := absolutelyContinuousOnInterval_highAmplitudeWeight hL
    (absolutelyContinuousOnInterval_fullVorticity_path s g hg hSum hu a b hab hI X hX)
    (absolutelyContinuousOnInterval_fullVorticity_path s g hg hSum hu a b hab hI Y hY)
  filter_upwards [hac.ae_differentiableAt] with t hdt ht
  have hd := hdt (by simpa only [Set.uIcc_of_le hab] using Set.Ioo_subset_Icc_self ht)
  have hx := LocalVorticityTangency.hasDerivAt_fullVorticity_path
    s g hg hSum hu a b hab hI X t ht (hDX t ht)
  have hy := LocalVorticityTangency.hasDerivAt_fullVorticity_path
    s g hg hSum hu a b hab hI Y t ht (hDY t ht)
  exact (hasDerivAt_highAmplitudeWeight_of_differentiable hx hy hL hd).mul
    (LocalAnnularStretchEvolution.hasDerivAt_pairedStretch_path
      s g hg hSum hu a b hab hI X Y t ht (hDX t ht) (hDY t ht) n N)

theorem integrated_highAmplitudeSource_path_identity (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    let rate := fun t ↦ materialHighAmplitudeRate n N L (s.coefficients t) nu
      (torusPoint (X t)) (torusPoint (Y t)) (liftedVelocity s t (X t)) (liftedVelocity s t (Y t))
    let source := fun t ↦ highAmplitudeStretch (2 * (n + 1)) L
      (PeriodicRieszPolynomial.kernel N (torusPoint (X t) - torusPoint (Y t)))
      (fullVorticity (s.coefficients t) (torusPoint (X t)))
      (fullVorticity (s.coefficients t) (torusPoint (Y t)))
    IntervalIntegrable rate volume a b ∧ (∫ t in a..b, rate t) = source b - source a := by
  dsimp only
  have hAC := absolutelyContinuousOnInterval_highAmplitudeSource_path
    s g hg hSum hu a b hab hI X Y hX hY (n + 1) N L hL
  have hd := ae_hasDerivAt_highAmplitudeSource_path
    s g hg hSum hu a b hab hI X Y hX hY hDX hDY n N L hL
  have heq : ∀ᵐ t, t ∈ Set.uIcc a b →
      deriv (fun τ ↦ highAmplitudeStretch (2 * (n + 1)) L
        (PeriodicRieszPolynomial.kernel N (torusPoint (X τ) - torusPoint (Y τ)))
        (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
        (fullVorticity (s.coefficients τ) (torusPoint (Y τ)))) t =
      materialHighAmplitudeRate n N L (s.coefficients t) nu (torusPoint (X t)) (torusPoint (Y t))
        (liftedVelocity s t (X t)) (liftedVelocity s t (Y t)) := by
    filter_upwards [hd, (Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b))] with t hdt he hmem
    have hm : t ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using hmem
    exact (hdt (he.mpr hm)).deriv
  refine ⟨hAC.intervalIntegrable_deriv.congr_ae ?_, ?_⟩
  · apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [heq] with t ht hmem
    exact ht (Set.uIoc_subset_uIcc hmem)
  · rw [← hAC.integral_deriv_eq_sub]
    symm
    apply intervalIntegral.integral_congr_ae
    filter_upwards [heq] with t ht hmem
    exact ht (Set.uIoc_subset_uIcc hmem)

end Mettapedia.FluidDynamics.NavierStokes.LocalAnnularSourcePathChainRule
