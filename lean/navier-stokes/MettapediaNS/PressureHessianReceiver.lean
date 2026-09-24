import MettapediaNS.WholeSpaceStretchingFlux

/-!
# Actual pressure-Hessian work on the constructed stretching receiver

The upstream compact integration-by-parts theorem and the already identified
Helmholtz pressure gradient put two derivatives on the actual receiver.
The cutoff product rule retains both first-derivative terms and the second
derivative of the cutoff. These are identities, not a bound on their norms.
-/

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureHessianReceiver

open MeasureTheory EulerLpTranslation EulerLpTranslation.SmoothL2Field
open EulerOrdinarySobolev
open NavierStokes.ProblemStatement (Space)
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness
open NavierStokesR3.PressureRecovery
open NavierStokesR3.Comparison (ComplexTest pressurePair)
open NavierStokesR3.HarmonicTestFunctionals (partialCLM)
open WholeSpaceStretchingFlux WholeSpacePressureRecovery
open scoped ContDiff

/-- The actual double derivative in the complex Schwartz test space. -/
def hessianTest (ρ : Space → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (a b : Fin 3) : ComplexTest :=
  partialCLM a (partialCLM b (realTest ρ hρ hcρ))

theorem hessianTest_apply (ρ : Space → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (a b : Fin 3) (x : Space) :
    hessianTest ρ hρ hcρ a b x =
      ((spatialPartial a (spatialPartial b ρ) x : ℝ) : ℂ) := by
  rw [hessianTest, partialCLM_realTest]
  change spatialPartial a (fun y => ((spatialPartial b ρ y : ℝ) : ℂ)) x = _
  exact partial_ofReal (spatial_partial_contDiff hρ b) a x

/-- One integration by parts followed by the pressure-gradient/Riesz identity.
No global integrability or normalization of scalar pressure is assumed. -/
theorem integral_pressureHessian_mul_eq_rieszPair (A : SmoothL2Field Space)
    (hdiv : ∀ x, EulerSmoothLimit.divergence A.field x = 0)
    (ρ : Space → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (a b : Fin 3) :
    ((∫ x, ρ x * spatialPartial b (fun y => (pressureField A).field y a) x : ℝ) : ℂ) =
      ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j
        (fun x => A.field x i * A.field x j) (hessianTest ρ hρ hcρ a b) := by
  rw [NavierStokesR3.CompactEnergy.integral_mul_partial hρ
    (component_contDiff (pressureField A).smooth a) hcρ b, Complex.ofReal_neg,
    integral_pressureField_mul_eq_rieszPair A hdiv (spatialPartial b ρ)
      (spatial_partial_contDiff hρ b) (NavierStokesR3.CompactEnergy.compact_partial hcρ b) a,
    neg_neg]
  simp only [hessianTest, partialCLM_realTest]

/-- All four product-rule terms remain in the differentiated receiver. -/
theorem partial_partial_cutoff_mul (η ρ : Space → ℝ)
    (hη : ContDiff ℝ ∞ η) (hρ : ContDiff ℝ ∞ ρ) (a b : Fin 3) (x : Space) :
    spatialPartial a (spatialPartial b (fun y => η y * ρ y)) x =
      η x * spatialPartial a (spatialPartial b ρ) x +
      spatialPartial a η x * spatialPartial b ρ x +
      spatialPartial b η x * spatialPartial a ρ x +
      ρ x * spatialPartial a (spatialPartial b η) x := by
  have he : spatialPartial b (fun y => η y * ρ y) =
      (fun y => η y * spatialPartial b ρ y + ρ y * spatialPartial b η y) :=
    funext (NavierStokesR3.ConservativeDifference.partial_mul hη hρ b)
  rw [he]
  have hd₁ := (hη.mul (spatial_partial_contDiff hρ b)).differentiable (by simp) x
  have hd₂ := (hρ.mul (spatial_partial_contDiff hη b)).differentiable (by simp) x
  have ha : spatialPartial a
      (fun y => η y * spatialPartial b ρ y + ρ y * spatialPartial b η y) x =
      spatialPartial a (fun y => η y * spatialPartial b ρ y) x +
        spatialPartial a (fun y => ρ y * spatialPartial b η y) x := by
    unfold spatialPartial
    rw [fderiv_fun_add hd₁ hd₂]
    rfl
  have hm₁ := NavierStokesR3.ConservativeDifference.partial_mul (f := η)
    (g := spatialPartial b ρ) hη (spatial_partial_contDiff hρ b) a x
  have hm₂ := NavierStokesR3.ConservativeDifference.partial_mul (f := ρ)
    (g := spatialPartial b η) hρ (spatial_partial_contDiff hη b) a x
  rw [ha, hm₁, hm₂]
  ring

/-- The compact receiver is constructed from the actual velocity, vorticity,
stretching flux, gradient projection, and the supplied scalar cutoff. -/
def localizedReceiver (A : SmoothL2Field Space) (η : Space → ℝ) (a b : Fin 3) : Space → ℝ :=
  fun x => η x * (receiver A a b).field x

theorem localizedReceiver_contDiff (A : SmoothL2Field Space) {η : Space → ℝ}
    (hη : ContDiff ℝ ∞ η) (a b : Fin 3) : ContDiff ℝ ∞ (localizedReceiver A η a b) :=
  hη.mul (receiver A a b).smooth

theorem localizedReceiver_compact (A : SmoothL2Field Space) {η : Space → ℝ}
    (hcη : HasCompactSupport η) (a b : Fin 3) : HasCompactSupport (localizedReceiver A η a b) :=
  hcη.mul_right

def receiverTest (A : SmoothL2Field Space) (η : Space → ℝ) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (a b : Fin 3) : ComplexTest :=
  hessianTest (localizedReceiver A η a b) (localizedReceiver_contDiff A hη a b)
    (localizedReceiver_compact A hcη a b) a b

theorem receiverTest_apply (A : SmoothL2Field Space) (η : Space → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (a b : Fin 3) (x : Space) :
    receiverTest A η hη hcη a b x =
      ((η x * spatialPartial a (spatialPartial b (receiver A a b).field) x +
        spatialPartial a η x * spatialPartial b (receiver A a b).field x +
        spatialPartial b η x * spatialPartial a (receiver A a b).field x +
        (receiver A a b).field x * spatialPartial a (spatialPartial b η) x : ℝ) : ℂ) := by
  rw [receiverTest, hessianTest_apply]
  exact congrArg Complex.ofReal (partial_partial_cutoff_mul η (receiver A a b).field
    hη (receiver A a b).smooth a b x)

/-- The pressure contribution of the constructed projected stretching tensor. -/
def pressureWork (A : SmoothL2Field Space) (η : Space → ℝ) : ℝ :=
  ∫ x, η x * ∑ j : Fin 3, (vorticityField A).field x j * ∑ a : Fin 3,
    (projectedColumn A a).field x j *
      (fderiv ℝ (pressureField A).field x ((vorticityField A).field x)) a

/-- The full pressure work, with every tensor component and derivative, is
identified with the upstream canonical Riesz pairings. -/
theorem pressureWork_eq_rieszPair (A : SmoothL2Field Space)
    (hdiv : ∀ x, EulerSmoothLimit.divergence A.field x = 0)
    (η : Space → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) :
    (pressureWork A η : ℂ) =
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
        pressurePair i j (fun x => A.field x i * A.field x j) (receiverTest A η hη hcη a b) := by
  have hi (a b : Fin 3) : Integrable (fun x => localizedReceiver A η a b x *
      spatialPartial b (fun y => (pressureField A).field y a) x) :=
    ((localizedReceiver_contDiff A hη a b).continuous.mul
      (spatial_partial_contDiff (component_contDiff (pressureField A).smooth a) b).continuous).integrable_of_hasCompactSupport
        (localizedReceiver_compact A hcη a b).mul_right
  have he : pressureWork A η = ∑ a : Fin 3, ∑ b : Fin 3,
      ∫ x, localizedReceiver A η a b x *
        spatialPartial b (fun y => (pressureField A).field y a) x := by
    unfold pressureWork
    simp_rw [pressure_contraction_eq, Finset.mul_sum, ← mul_assoc]
    change (∫ x, ∑ a : Fin 3, ∑ b : Fin 3, localizedReceiver A η a b x *
      spatialPartial b (fun y => (pressureField A).field y a) x) = _
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
    apply Finset.sum_congr rfl
    intro a _
    exact integral_finsetSum _ (fun b _ => hi a b)
  rw [he, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact integral_pressureHessian_mul_eq_rieszPair A hdiv _
    (localizedReceiver_contDiff A hη a b) (localizedReceiver_compact A hcη a b) a b

end Mettapedia.FluidDynamics.NavierStokes.PressureHessianReceiver
