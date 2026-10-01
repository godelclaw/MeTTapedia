import Mettapedia.QuantumTheory.YangMills.WilsonEliminationRoutes

/-!
# Composition of normalized Wilson projections

The intermediate marginal cancels against the normalization of the first
projected mark. Fubini then identifies successive projections with the
single projection integrating both interior groups. All generated weights
remain present in this identity.

Conditional covariances and third cumulants obey their exact tower laws.
Third order retains the transported inner cumulant and all three mixed
covariances; these terms remain continuous marks for subsequent integration.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Topology
namespace Mettapedia.QuantumTheory.YangMills.WilsonProjectionComposition
open WilsonBlockElimination

variable {B I J : Type*}
  [TopologicalSpace B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B]
  [TopologicalSpace I] [CompactSpace I] [MeasurableSpace I] [BorelSpace I]
  [SecondCountableTopology I]
  [TopologicalSpace J] [CompactSpace J] [MeasurableSpace J] [BorelSpace J]
  [SecondCountableTopology J]

omit [MeasurableSpace B] [BorelSpace B] in
/-- Exact tower identity for the actual normalized integral operators. -/
theorem project_staged (ν : Measure I) (ρ : Measure J)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (W : C((B × I) × J, ℝ)) (hW : ∀ p, 0 < W p)
    (F : C((B × I) × J, ℝ)) :
    project ν (marginal ρ W) (marginal_pos ρ W hW) (project ρ W hW F) =
      project (ν.prod ρ) (reassociate W) (fun _ => hW _) (reassociate F) := by
  have hmul : marginal ρ W * project ρ W hW F = marginal ρ (W * F) := by
    ext b
    change marginal ρ W b * (marginal ρ (W * F) b / marginal ρ W b) = _
    field_simp [(marginal_pos ρ W hW b).ne']
  ext b
  change marginal ν (marginal ρ W * project ρ W hW F) b /
    marginal ν (marginal ρ W) b = _
  rw [hmul, marginal_staged, marginal_staged]
  rfl

omit [MeasurableSpace B] [BorelSpace B] in
/-- The covariance inside the combined fiber is the covariance of the first
projected marks plus the first fiber covariance transported through the next
weighted integral. This is a pointwise identity at each retained boundary. -/
theorem fiberCovariance_staged (ν : Measure I) (ρ : Measure J)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (W : C((B × I) × J, ℝ)) (hW : ∀ p, 0 < W p)
    (F G : C((B × I) × J, ℝ)) :
    fiberCovariance (ν.prod ρ) (reassociate W) (fun _ ↦ hW _)
      (reassociate F) (reassociate G) =
      fiberCovariance ν (marginal ρ W) (marginal_pos ρ W hW)
        (project ρ W hW F) (project ρ W hW G) +
      project ν (marginal ρ W) (marginal_pos ρ W hW) (fiberCovariance ρ W hW F G) := by
  have hsub : project ν (marginal ρ W) (marginal_pos ρ W hW)
      (fiberCovariance ρ W hW F G) =
      project ν (marginal ρ W) (marginal_pos ρ W hW) (project ρ W hW (F * G)) -
      project ν (marginal ρ W) (marginal_pos ρ W hW)
        (project ρ W hW F * project ρ W hW G) := by
    ext b
    exact expectation_sub ν ((marginal ρ W).curry b)
      ((project ρ W hW (F * G)).curry b)
      ((project ρ W hW F * project ρ W hW G).curry b)
  rw [hsub]
  change project (ν.prod ρ) (reassociate W) _ (reassociate (F * G)) -
      project (ν.prod ρ) (reassociate W) _ (reassociate F) *
        project (ν.prod ρ) (reassociate W) _ (reassociate G) = _
  rw [← project_staged ν ρ W hW (F * G), ← project_staged ν ρ W hW F,
    ← project_staged ν ρ W hW G]
  ext b
  simp only [fiberCovariance, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.mul_apply]
  ring

omit [MeasurableSpace B] [BorelSpace B] in
/-- The mixed log-partition coefficient transports with both its contact
score and its conditional covariance. Omitting the latter changes the
Hessian of the generated effective weight. -/
theorem mixedScore_staged (ν : Measure I) (ρ : Measure J)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (β : ℝ) (W : C((B × I) × J, ℝ)) (hW : ∀ p, 0 < W p)
    (F G J₀ : C((B × I) × J, ℝ)) (b : B) :
    β ^ 2 * fiberCovariance (ν.prod ρ) (reassociate W) (fun _ ↦ hW _)
        (reassociate F) (reassociate G) b -
      β * project (ν.prod ρ) (reassociate W) (fun _ ↦ hW _) (reassociate J₀) b =
    β ^ 2 * fiberCovariance ν (marginal ρ W) (marginal_pos ρ W hW)
        (project ρ W hW F) (project ρ W hW G) b -
      β * project ν (marginal ρ W) (marginal_pos ρ W hW) (project ρ W hW J₀) b +
    β ^ 2 * project ν (marginal ρ W) (marginal_pos ρ W hW)
      (fiberCovariance ρ W hW F G) b := by
  rw [fiberCovariance_staged ν ρ W hW F G, ← project_staged ν ρ W hW J₀]
  simp only [ContinuousMap.add_apply]
  ring

omit [MeasurableSpace B] [BorelSpace B] in
/-- Exact third-cumulant transport under the same two weighted projections.
The three covariances couple a first projected score to the conditional
covariance of the other two; every generated density remains present. -/
theorem fiberThirdCumulant_staged (ν : Measure I) (ρ : Measure J)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (W : C((B × I) × J, ℝ)) (hW : ∀ p, 0 < W p)
    (F G H : C((B × I) × J, ℝ)) :
    fiberThirdCumulant (ν.prod ρ) (reassociate W) (fun _ ↦ hW _)
      (reassociate F) (reassociate G) (reassociate H) =
      fiberThirdCumulant ν (marginal ρ W) (marginal_pos ρ W hW)
        (project ρ W hW F) (project ρ W hW G) (project ρ W hW H) +
      project ν (marginal ρ W) (marginal_pos ρ W hW) (fiberThirdCumulant ρ W hW F G H) +
      fiberCovariance ν (marginal ρ W) (marginal_pos ρ W hW)
        (project ρ W hW F) (fiberCovariance ρ W hW G H) +
      fiberCovariance ν (marginal ρ W) (marginal_pos ρ W hW)
        (project ρ W hW G) (fiberCovariance ρ W hW F H) +
      fiberCovariance ν (marginal ρ W) (marginal_pos ρ W hW)
        (project ρ W hW H) (fiberCovariance ρ W hW F G) := by
  have ht : (fun U : C((B × I) × J, ℝ) ↦
      project (ν.prod ρ) (reassociate W) (fun _ ↦ hW _) (reassociate U)) =
      (projectLinear ν (marginal ρ W) (marginal_pos ρ W hW)).comp
        (projectLinear ρ W hW) := by
    funext U
    exact (project_staged ν ρ W hW U).symm
  change thirdMoment (fun U : C((B × I) × J, ℝ) ↦
      project (ν.prod ρ) (reassociate W) (fun _ ↦ hW _) (reassociate U)) F G H = _
  rw [ht]
  exact thirdMoment_comp (projectLinear ρ W hW)
    (projectLinear ν (marginal ρ W) (marginal_pos ρ W hW)) F G H

#print axioms project_staged
#print axioms fiberCovariance_staged
#print axioms mixedScore_staged
#print axioms fiberThirdCumulant_staged
end Mettapedia.QuantumTheory.YangMills.WilsonProjectionComposition
