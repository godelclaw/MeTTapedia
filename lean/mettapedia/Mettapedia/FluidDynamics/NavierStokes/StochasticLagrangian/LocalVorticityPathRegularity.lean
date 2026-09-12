import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpaceTimeExtension
import Mettapedia.Analysis.AbsolutelyContinuousComposition

/-! # Absolute continuity of actual full vorticity along locally Lipschitz paths -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalVorticityPathRegularity

open PeriodicFourierTriad PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity
open PancakeCurlOutputTail PancakeFourierMaterialPaths LocalLowDiffusionBudget
open Mettapedia.Analysis
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem absolutelyContinuousOnInterval_fullVorticity_path
    {nu T B : ℝ} {u₀ : FourierVelocity} (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X : ℝ → X3) (hX : LocallyLipschitz X) :
    AbsolutelyContinuousOnInterval
      (fun τ ↦ fullVorticity (s.coefficients τ) (torusPoint (X τ))) a b := by
  let w : ℝ × X3 → R3 := fun z ↦
    fullVorticity (LocalSpaceTimeExtension.coefficients s a b hab z.1) (torusPoint z.2)
  have hw : LocallyLipschitz w :=
    LocalSpaceTimeExtension.locallyLipschitz_fullVorticity s a b hab hI g hg hSum hu
  have hx : LocallyLipschitz (fun τ ↦ w (τ, X τ)) :=
    hw.comp (g := fun τ ↦ (τ, X τ)) (LocallyLipschitz.id.prodMk hX)
  apply AbsolutelyContinuousComposition.congr (AbsolutelyContinuousComposition.of_locallyLipschitz hx)
  intro τ hτ
  simp only [w, LocalSpaceTimeExtension.coefficients_eq s a b hab τ
    (by simpa only [Set.uIcc_of_le hab] using hτ)]

end Mettapedia.FluidDynamics.NavierStokes.LocalVorticityPathRegularity
