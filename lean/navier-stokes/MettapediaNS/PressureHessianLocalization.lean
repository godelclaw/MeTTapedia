import MettapediaNS.PressureHessianReceiver
import MettapediaNS.PressureLocalizationDifference
import MettapediaNS.WholeSpaceUnforcedEnergy

/-!
# Pressure-Hessian localization with the derivative remainder retained

Localizing a compact receiver and then differentiating it is not the same
as multiplying its Hessian by the cutoff. The exact remainder below connects
the actual pressure-Hessian test to the first/second commutator decomposition.
All tests are constructed in the upstream Schwartz space.
-/

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureHessianLocalization

open MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness
open NavierStokesR3.PressureRecovery
open NavierStokesR3.Comparison (ComplexTest pressurePair)
open PressureHessianReceiver PressureLocalizationDifference
open scoped ContDiff

/-- Multiply after differentiating. Compact support comes from the receiver. -/
def weightedHessianTest (ρ η : Space → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hη : ContDiff ℝ ∞ η) (a b : Fin 3) : ComplexTest :=
  realTest (fun x => η x * spatialPartial a (spatialPartial b ρ) x)
    (hη.mul (spatial_partial_contDiff (spatial_partial_contDiff hρ b) a))
    (NavierStokesR3.CompactEnergy.compact_partial
      (NavierStokesR3.CompactEnergy.compact_partial hcρ b) a).mul_left

theorem weightedHessianTest_apply (ρ η : Space → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hη : ContDiff ℝ ∞ η) (a b : Fin 3) (x : Space) :
    weightedHessianTest ρ η hρ hcρ hη a b x = η x • hessianTest ρ hρ hcρ a b x := by
  rw [hessianTest_apply]
  change ((η x * spatialPartial a (spatialPartial b ρ) x : ℝ) : ℂ) = _
  simp only [Complex.ofReal_mul, Complex.real_smul]

/-- The difference between differentiating the localized receiver and
localizing its differentiated test. -/
def cutoffDerivativeTest (ρ η : Space → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hη : ContDiff ℝ ∞ η) (a b : Fin 3) : ComplexTest :=
  hessianTest (fun x => η x * ρ x) (hη.mul hρ) hcρ.mul_left a b -
    weightedHessianTest ρ η hρ hcρ hη a b

/-- Exactly the two first-derivative terms and the second-cutoff-derivative
term remain. No derivative norm is assumed bounded here. -/
theorem cutoffDerivativeTest_apply (ρ η : Space → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hη : ContDiff ℝ ∞ η) (a b : Fin 3) (x : Space) :
    cutoffDerivativeTest ρ η hρ hcρ hη a b x =
      ((spatialPartial a η x * spatialPartial b ρ x +
        spatialPartial b η x * spatialPartial a ρ x +
        ρ x * spatialPartial a (spatialPartial b η) x : ℝ) : ℂ) := by
  simp only [cutoffDerivativeTest, _root_.sub_apply, hessianTest_apply,
    weightedHessianTest_apply, Complex.real_smul]
  rw [partial_partial_cutoff_mul η ρ hη hρ]
  simp only [Complex.ofReal_add, Complex.ofReal_mul]
  ring

/-- This identity is the application boundary for the second-difference
estimate: the first commutator and derivative remainder both survive. -/
theorem pressurePair_localized_hessian_eq (i j a b : Fin 3)
    (g ρ φ : Space → ℝ) (hg : Integrable g)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hφ : ContDiff ℝ ∞ φ) :
    pressurePair i j g
        (hessianTest (fun x => φ x ^ 4 * ρ x) ((hφ.pow 4).mul hρ) hcρ.mul_left a b) -
      pressurePair i j (fun x => φ x ^ 4 * g x) (hessianTest ρ hρ hcρ a b) =
      2 * firstDifference i j φ g
        (weightedHessianTest ρ (fun x => φ x ^ 2) hρ hcρ (hφ.pow 2) a b)
        (weightedHessianTest ρ (fun x => φ x ^ 4) hρ hcρ (hφ.pow 4) a b) -
      secondDifference i j φ g (hessianTest ρ hρ hcρ a b)
        (weightedHessianTest ρ (fun x => φ x ^ 2) hρ hcρ (hφ.pow 2) a b)
        (weightedHessianTest ρ (fun x => φ x ^ 4) hρ hcρ (hφ.pow 4) a b) +
      pressurePair i j g (cutoffDerivativeTest ρ (fun x => φ x ^ 4) hρ hcρ (hφ.pow 4) a b) := by
  have he := (NavierStokesR3.PressureFunctionals.pressurePairLinear i j g hg).map_sub
    (hessianTest (fun x => φ x ^ 4 * ρ x) ((hφ.pow 4).mul hρ) hcρ.mul_left a b)
    (weightedHessianTest ρ (fun x => φ x ^ 4) hρ hcρ (hφ.pow 4) a b)
  simp only [NavierStokesR3.PressureFunctionals.pressurePairLinear_apply] at he
  unfold cutoffDerivativeTest
  rw [he]
  unfold firstDifference secondDifference
  ring

/-- Both cutoff relations needed by the existing first/second commutator
bounds hold for the constructed Hessian tests, rather than being hypotheses. -/
theorem weightedHessianTest_square_relations (ρ φ : Space → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hφ : ContDiff ℝ ∞ φ)
    (a b : Fin 3) :
    (∀ x, weightedHessianTest ρ (fun y => φ y ^ 2) hρ hcρ (hφ.pow 2) a b x =
      φ x ^ 2 • hessianTest ρ hρ hcρ a b x) ∧
    (∀ x, weightedHessianTest ρ (fun y => φ y ^ 4) hρ hcρ (hφ.pow 4) a b x =
      φ x ^ 2 • weightedHessianTest ρ (fun y => φ y ^ 2) hρ hcρ (hφ.pow 2) a b x) := by
  constructor
  · intro x; exact weightedHessianTest_apply _ _ _ _ _ _ _ _
  · intro x
    simp only [weightedHessianTest_apply, smul_smul]
    congr 1
    ring

/-- The earlier initial-energy estimate now applies to the differentiated
receiver with both Schwartz multiplier relations constructed. The Hessian
test norm, first commutator, and cutoff derivative remainder are not paid. -/
theorem norm_sum_secondDifference_hessian_le_initial
    {ν T : ℝ} {u : NavierStokes.ProblemStatement.VelocityField}
    {p : NavierStokes.ProblemStatement.PressureField} {u₀ : Space → Space}
    (s : NavierStokesR3.H3Comparison.ClassicalH3Solution ν (fun _ => 0) u₀ T u p)
    (hν : 0 ≤ ν) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) T)
    (ρ φ : Space → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hφ : ContDiff ℝ ∞ φ) (hφrange : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1)
    {L R : ℝ} (hR : 0 < R)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖) (a b : Fin 3) :
    ‖∑ i : Fin 3, ∑ j : Fin 3, secondDifference i j φ
      (fun x => u (t, x) i * u (t, x) j) (hessianTest ρ hρ hcρ a b)
      (weightedHessianTest ρ (fun x => φ x ^ 2) hρ hcρ (hφ.pow 2) a b)
      (weightedHessianTest ρ (fun x => φ x ^ 4) hρ hcρ (hφ.pow 4) a b)‖ ≤
      9 * (NavierStokesR3.Comparison.heatKernelTimeConstant * (max (2 * L) 1) ^ 2) *
        NavierStokesR3.Comparison.comparisonLpNorm (4 / 3)
          (NavierStokesR3.Comparison.radialCommutatorKernel 1) ^ (2 / 3 : ℝ) *
        R ^ (-(3 / 2) : ℝ) * NavierStokesR3.Comparison.l2Sq u₀ *
        NavierStokesR3.Comparison.comparisonLpNorm 2 (fun x => hessianTest ρ hρ hcρ a b x) := by
  obtain ⟨hh, hhh⟩ := weightedHessianTest_square_relations ρ φ hρ hcρ hφ a b
  exact WholeSpaceUnforcedEnergy.norm_sum_secondPressureDifference_le_initial s hν ht
    hR hφ.continuous.measurable hφrange hLip _ _ _ hh hhh

end Mettapedia.FluidDynamics.NavierStokes.PressureHessianLocalization
