import Mettapedia.QuantumTheory.YangMills.WilsonEliminationRoutes
import Mettapedia.QuantumTheory.YangMills.WilsonPinnedIntegral

/-!
# Composition of normalized Wilson projections

The intermediate marginal cancels against the normalization of the first
projected mark. Fubini then identifies successive projections with the
single projection integrating both interior groups. All generated weights
remain present in this identity.

Conditional covariances and third cumulants obey their exact tower laws.
Third order retains the transported inner cumulant and all three mixed
covariances; these terms remain continuous marks for subsequent integration.
Fourth cumulance retains all fifteen partition contributions, with the
generated inner and outer normalized maps explicit.
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

omit [MeasurableSpace B] [BorelSpace B] in
/-- Exact fourth-cumulant transport, retaining all fifteen partition terms
and the two generated normalized integration maps. -/
theorem fiberFourthCumulant_staged (ν : Measure I) (ρ : Measure J)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (W : C((B × I) × J, ℝ)) (hW : ∀ p, 0 < W p)
    (F G H K : C((B × I) × J, ℝ)) :
    let P := projectLinear ρ W hW
    let Q := projectLinear ν (marginal ρ W) (marginal_pos ρ W hW)
    fiberFourthCumulant (ν.prod ρ) (reassociate W) (fun _ ↦ hW _)
      (reassociate F) (reassociate G) (reassociate H) (reassociate K) =
      Q (fourthMoment P F G H K) + fourthMoment Q (P F) (P G) (P H) (P K) +
      secondMoment Q (P F) (thirdMoment P G H K) +
      secondMoment Q (P G) (thirdMoment P F H K) +
      secondMoment Q (P H) (thirdMoment P F G K) +
      secondMoment Q (P K) (thirdMoment P F G H) +
      secondMoment Q (secondMoment P F G) (secondMoment P H K) +
      secondMoment Q (secondMoment P F H) (secondMoment P G K) +
      secondMoment Q (secondMoment P F K) (secondMoment P G H) +
      thirdMoment Q (P F) (P G) (secondMoment P H K) +
      thirdMoment Q (P F) (P H) (secondMoment P G K) +
      thirdMoment Q (P F) (P K) (secondMoment P G H) +
      thirdMoment Q (P G) (P H) (secondMoment P F K) +
      thirdMoment Q (P G) (P K) (secondMoment P F H) +
      thirdMoment Q (P H) (P K) (secondMoment P F G) := by
  have ht : (fun U : C((B × I) × J, ℝ) ↦
      project (ν.prod ρ) (reassociate W) (fun _ ↦ hW _) (reassociate U)) =
      (projectLinear ν (marginal ρ W) (marginal_pos ρ W hW)).comp
        (projectLinear ρ W hW) := by
    funext U
    exact (project_staged ν ρ W hW U).symm
  change fourthMoment (fun U : C((B × I) × J, ℝ) ↦
      project (ν.prod ρ) (reassociate W) (fun _ ↦ hW _) (reassociate U)) F G H K = _
  rw [ht]
  exact fourthMoment_comp (projectLinear ρ W hW)
    (projectLinear ν (marginal ρ W) (marginal_pos ρ W hW)) F G H K

section Coordinates
open WilsonPinnedIntegral WilsonEliminationRoutes Mettapedia.GSLT.Ultrainfinite
variable {X E : Type} [Fintype X] [DecidableEq X]
  [TopologicalSpace E] [CompactSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- A finite-coordinate weighted state on the original lattice. Eliminated
coordinates remain only as normalized dummy probability factors. -/
abbrev coordinateState (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) : State :=
  ⟨X → E, inferInstance, inferInstance, inferInstance, inferInstance,
    Measure.pi (fun _ : X ↦ ν₀), inferInstance, W, hW⟩

/-- The actual conditional integral supplies a GSLT route step; expectation
preservation and the uniform bound are theorems about that integral. -/
def coordinateStep (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : Finset X) :
    Step (coordinateState ν₀ W hW)
      (coordinateState ν₀ (average ν₀ held W) (average_pos ν₀ held W hW)) where
  project := weightedProjectLinear ν₀ W hW held
  expectation := expectation_weightedProject ν₀ W hW held
  contract := fun F _ hF ↦ abs_weightedProject_le ν₀ W hW held F hF

/-- The complete sequence of generated states. No interaction is discarded. -/
abbrev coordinateStateSequence (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : ℕ → Finset X) (j : ℕ) : State :=
  coordinateState ν₀ (densitySequence ν₀ W held j) (densitySequence_pos ν₀ W hW held j)

/-- Any finite prefix is a route of the existing weighted integration
machinery. Nesting is an assumption on direct-versus-staged equality only. -/
def coordinateRoute (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : ℕ → Finset X) :
    (j : ℕ) → Route Step (coordinateStateSequence ν₀ W hW held 0)
      (coordinateStateSequence ν₀ W hW held j)
  | 0 => .refl _
  | j + 1 => (coordinateRoute ν₀ W hW held j).append
      (.cons (coordinateStep ν₀ (densitySequence ν₀ W held j)
        (densitySequence_pos ν₀ W hW held j) (held j)) (.refl _))

theorem action_coordinateRoute (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : ℕ → Finset X)
    (F : C(X → E, ℝ)) :
    ∀ j, action (coordinateRoute ν₀ W hW held j) F = markSequence ν₀ W hW held F j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    exact (action_append (coordinateRoute ν₀ W hW held j)
      (.cons (coordinateStep ν₀ (densitySequence ν₀ W held j)
        (densitySequence_pos ν₀ W hW held j) (held j)) (.refl _)) F).trans
      (congrArg (weightedProject ν₀ (densitySequence ν₀ W held j)
        (densitySequence_pos ν₀ W hW held j) (held j)) ih)

/-- Direct integration equals every finite nested route, for every
continuous observable and therefore every finite product of such marks. -/
theorem action_coordinateRoute_eq_direct (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : ℕ → Finset X)
    (hnested : ∀ j, held (j + 1) ⊆ held j) (F : C(X → E, ℝ)) (j : ℕ) :
    action (coordinateRoute ν₀ W hW held (j + 1)) F =
      weightedProject ν₀ W hW (held j) F := by
  rw [action_coordinateRoute, markSequence_eq_direct ν₀ W hW held hnested F j]

/-- Partition normalization is unchanged at every elimination depth,
including when the held sequence is not nested. -/
theorem coordinateStateSequence_partition (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : ℕ → Finset X) :
    ∀ j, (coordinateStateSequence ν₀ W hW held j).partition =
      (coordinateState ν₀ W hW).partition := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    exact (integral_average ν₀ (held j) (densitySequence ν₀ W held j)).trans ih

/-- Original marked moments transported through the full finite route.
These are stored moments indexed by original labels, not derivatives in
new coarse-link coordinates. -/
abbrev coordinateResponseState {ι : Type} (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : ℕ → Finset X)
    (F : ι → C(X → E, ℝ)) (j : ℕ) : BoundaryState ι :=
  ⟨coordinateStateSequence ν₀ W hW held j,
    (ResponseData.initial F).transport (coordinateRoute ν₀ W hW held j)⟩

theorem coordinateResponseState_pair {ι : Type} (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : ℕ → Finset X)
    (hnested : ∀ j, held (j + 1) ⊆ held j) (F : ι → C(X → E, ℝ)) (j : ℕ) (i k : ι) :
    (coordinateResponseState ν₀ W hW held F (j + 1)).2.pair i k =
      fiberCovariance (Measure.pi fun _ : X ↦ ν₀) (W.comp (pinMap (held j)))
        (fun p ↦ hW _) ((F i).comp (pinMap (held j))) ((F k).comp (pinMap (held j))) := by
  change action (coordinateRoute ν₀ W hW held (j + 1)) (F i * F k) -
    action (coordinateRoute ν₀ W hW held (j + 1)) (F i) *
      action (coordinateRoute ν₀ W hW held (j + 1)) (F k) = _
  rw [action_coordinateRoute_eq_direct ν₀ W hW held hnested (F i * F k) j,
    action_coordinateRoute_eq_direct ν₀ W hW held hnested (F i) j,
    action_coordinateRoute_eq_direct ν₀ W hW held hnested (F k) j]
  rfl

theorem coordinateResponseState_triple {ι : Type} (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : ℕ → Finset X)
    (hnested : ∀ j, held (j + 1) ⊆ held j) (F : ι → C(X → E, ℝ))
    (j : ℕ) (i k l : ι) :
    (coordinateResponseState ν₀ W hW held F (j + 1)).2.triple i k l =
      fiberThirdCumulant (Measure.pi fun _ : X ↦ ν₀) (W.comp (pinMap (held j)))
        (fun p ↦ hW _) ((F i).comp (pinMap (held j))) ((F k).comp (pinMap (held j)))
        ((F l).comp (pinMap (held j))) := by
  change thirdMoment (action (coordinateRoute ν₀ W hW held (j + 1))) (F i) (F k) (F l) = _
  have hP : action (coordinateRoute ν₀ W hW held (j + 1)) =
      weightedProjectLinear ν₀ W hW (held j) := by
    ext U b
    exact congrArg (fun V : C(X → E, ℝ) ↦ V b)
      (action_coordinateRoute_eq_direct ν₀ W hW held hnested U j)
  rw [hP]
  rfl

end Coordinates

section PairedCoordinates
open WilsonEliminationRoutes
variable {X I J E : Type} [Fintype X] [Fintype I] [Fintype J]
  [Group E] [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- A genuine change to coarse product coordinates is an actual weighted
GSLT step. Its target carries the entire generated marginal density. -/
def blockedStep (ν : Measure E) [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant ν] (e : ((I ⊕ I) ⊕ J) ≃ X)
    (W : C(X → E, ℝ)) (hW : ∀ U, 0 < W U) :
    Step (coordinateState ν W hW)
      (coordinateState ν (PairedLinks.blockedDensity ν e W)
        (PairedLinks.blockedDensity_pos ν e W hW)) where
  project := PairedLinks.blockedProjectLinear ν e W hW
  expectation := PairedLinks.expectation_blockedProject ν e W hW
  contract := fun F _ hF ↦ PairedLinks.abs_blockedProject_le ν e W hW F hF

end PairedCoordinates

#print axioms project_staged
#print axioms fiberCovariance_staged
#print axioms mixedScore_staged
#print axioms fiberThirdCumulant_staged
end Mettapedia.QuantumTheory.YangMills.WilsonProjectionComposition
