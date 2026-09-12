import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalCompactMaterialPath
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAnnularSourcePathChainRule
import Mettapedia.Analysis.AbsolutelyContinuousTimeWeight

/-!
# Constructed material pairs satisfy the signed source identity

Paths through any two prescribed lifted points are constructed from the
actual local velocity, not supplied as geometric hypotheses. The same paths
work for every finite annular cutoff and every positive amplitude threshold.
The identity remains pathwise; no spatial or cutoff-uniform budget is claimed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAnnularMaterialPaths

open MeasureTheory
open PeriodicFourierTriad PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity
open PancakeCurlOutputTail PancakeFourierMaterialPaths LocalLowDiffusionBudget PancakeLocalMaterialTrajectories
open LocalAnnularSourcePathChainRule Mettapedia.Analysis SignedCrossKernel
local notation "X3" => Fin 3 → ℝ

variable {nu T B : ℝ} {u₀ : FourierVelocity}

def sourceAlong (s : LocalInfiniteVelocitySolution nu u₀ T B) (X Y : ℝ → X3)
    (n N : ℕ) (L t : ℝ) : ℝ :=
  highAmplitudeStretch (2 * (n + 1)) L
    (PeriodicRieszPolynomial.kernel N (torusPoint (X t) - torusPoint (Y t)))
    (fullVorticity (s.coefficients t) (torusPoint (X t)))
    (fullVorticity (s.coefficients t) (torusPoint (Y t)))

def rateAlong (s : LocalInfiniteVelocitySolution nu u₀ T B) (X Y : ℝ → X3)
    (n N : ℕ) (L t : ℝ) : ℝ :=
  materialHighAmplitudeRate n N L (s.coefficients t) nu (torusPoint (X t)) (torusPoint (Y t))
    (liftedVelocity s t (X t)) (liftedVelocity s t (Y t))

theorem integral_sourceAlong_eq_initial_add_weighted_rate
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X Y : ℝ → X3) (hX : LocallyLipschitz X) (hY : LocallyLipschitz Y)
    (hDX : ∀ t ∈ Set.Ioo a b, HasDerivAt X (liftedVelocity s t (X t)) t)
    (hDY : ∀ t ∈ Set.Ioo a b, HasDerivAt Y (liftedVelocity s t (Y t)) t)
    (n N : ℕ) (L : ℝ) (hL : 0 < L) :
    IntervalIntegrable (fun τ ↦ (b - τ) * rateAlong s X Y n N L τ) volume a b ∧
      (∫ τ in a..b, sourceAlong s X Y n N L τ) =
        (b - a) * sourceAlong s X Y n N L a +
          ∫ τ in a..b, (b - τ) * rateAlong s X Y n N L τ :=
  AbsolutelyContinuousTimeWeight.integral_eq_initial_add_weighted_rate hab
    (LocalAnnularSourcePathIntegral.absolutelyContinuousOnInterval_highAmplitudeSource_path
      s g hg hSum hu a b hab hI X Y hX hY (n + 1) N L hL)
    (ae_hasDerivAt_highAmplitudeSource_path s g hg hSum hu a b hab hI X Y hX hY hDX hDY n N L hL)

theorem exists_paths_integrated_source_identity (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (x y : X3) :
    ∃ X Y : ℝ → X3, X t = x ∧ Y t = y ∧ LocallyLipschitz X ∧ LocallyLipschitz Y ∧
      (∀ τ ∈ Set.Ioo a b, HasDerivAt X (liftedVelocity s τ (X τ)) τ) ∧
      (∀ τ ∈ Set.Ioo a b, HasDerivAt Y (liftedVelocity s τ (Y τ)) τ) ∧
      ∀ (n N : ℕ) (L : ℝ), 0 < L →
        (IntervalIntegrable (rateAlong s X Y n N L) volume a b ∧
        (∫ τ in a..b, rateAlong s X Y n N L τ) =
          sourceAlong s X Y n N L b - sourceAlong s X Y n N L a) ∧
        (IntervalIntegrable (fun τ ↦ (b - τ) * rateAlong s X Y n N L τ) volume a b ∧
        (∫ τ in a..b, sourceAlong s X Y n N L τ) =
          (b - a) * sourceAlong s X Y n N L a +
            ∫ τ in a..b, (b - τ) * rateAlong s X Y n N L τ) := by
  have hu1 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 1 (s.coefficients τ) q ≤ g q :=
    (fourierMoment_mono _ (by norm_num : 1 ≤ 3) q).trans (hu τ hτ q)
  obtain ⟨X, hXt, hX, hDX⟩ := LocalCompactMaterialPath.exists_locallyLipschitz_materialPath_through
    s g hg hSum hu1 a b hab hI t ht x
  obtain ⟨Y, hYt, hY, hDY⟩ := LocalCompactMaterialPath.exists_locallyLipschitz_materialPath_through
    s g hg hSum hu1 a b hab hI t ht y
  refine ⟨X, Y, hXt, hYt, hX, hY, hDX, hDY, fun n N L hL ↦ ?_⟩
  exact ⟨integrated_highAmplitudeSource_path_identity
    s g hg hSum hu a b hab hI X Y hX hY hDX hDY n N L hL,
    integral_sourceAlong_eq_initial_add_weighted_rate
      s g hg hSum hu a b hab hI X Y hX hY hDX hDY n N L hL⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalAnnularMaterialPaths
