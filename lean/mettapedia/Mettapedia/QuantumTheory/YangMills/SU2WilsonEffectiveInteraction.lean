import Mettapedia.QuantumTheory.YangMills.SU2WilsonAssemblyLocality
import Mettapedia.QuantumTheory.YangMills.SU2WilsonSeparatorComparison

/-!
# Spatial response of the actual two-level effective Wilson weights

The logarithms of both assembly marginals are the original boundary log
partition functions. Their first and mixed derivatives retain the original
action scores, contact term and staged conditional covariance. Separated
responses decay uniformly in surrounding volume at strong coupling. The
growing family changes genuine retained links at both levels.

The weighted maximum-row seminorm bounds total second-order influence
uniformly in volume at both levels, including nearby contacts. The full
ordered third derivative retains every action contact and covariance
correction, including coincident patches. The coarse score cumulant is the
actual GSLT route's third remainder.
All singleton score triples satisfy a volume-uniform tree-weighted budget.
The actual Wilson scores also satisfy the boundary contract after each Haar
step, with concrete witnesses for its OSLF reachability. The quantitative
composition theorem is instantiated with spatial bounds for all three
mixed arrays and the new conditional moments under the generated density.

The seminorm uses the original lattice metric and the stated group rotation
directions. A rescaled multiscale recursion needs analytic control after a
genuine change of gauge-field coordinates and extraction of generated interactions.
-/
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Filter
open scoped Topology Classical
open Mettapedia.Combinatorics.PolymerGas
namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonEffectiveInteraction
open SU2WilsonAssembly SU2WilsonAssemblyLocality SU2WilsonBlockPilot
open WilsonDyadicGeometry WilsonDyadicProjection WilsonPinnedIntegral
open StrongCouplingCrossing WilsonLocalResponse WilsonBlockElimination
open WilsonSeparatedBoundaryResponse WilsonBoundaryChanges WilsonPatchGeometry
open CompactTransferGap

export SU2WilsonAssemblyLocality (fineCoordinates assemble_fineCoordinates)

/-- `false` selects the first marginal and `true` the second marginal. -/
def mesh (coarse : Bool) : ℕ := if coarse then 4 else 2

/-- Logarithm of the actual generated weight in the assembled route. -/
def logWeight (N : ℕ) (β : ℝ) (coarse : Bool) (b : FullField N) : ℝ :=
  if coarse then Real.log (secondDensity N β (coarseRestriction N b))
  else Real.log (firstDensity N β (fineCoordinates N b))

theorem boundaryLog_eq_pin (N : ℕ) (β : ℝ) (s : ℕ) (b : FullField N) :
    boundaryLogPartition (volume : Measure SU2)
      (SU2BoundaryResponse.model (volumeIndex N) univ)
      (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β (retainedSet s) b =
      Real.log (∫ ω : FullField N, fullDensity N β (pin (retainedSet s) b ω)) :=
  WilsonConditionalProjection.logPartition_eq_pin (volume : Measure SU2)
    (SU2BoundaryResponse.model (volumeIndex N) univ)
    (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β (retainedSet s) b

/-- Both generated effective weights are identified with original fixed-boundary
Wilson integrals, rather than with a new Wilson-form approximation. -/
theorem logWeight_eq_boundary (N : ℕ) (β : ℝ) (coarse : Bool) (b : FullField N) :
    logWeight N β coarse b = boundaryLogPartition (volume : Measure SU2)
      (SU2BoundaryResponse.model (volumeIndex N) univ)
      (SU2BoundaryResponse.model_continuous (volumeIndex N) univ)
      β (retainedSet (mesh coarse)) b := by
  rw [boundaryLog_eq_pin]
  cases coarse
  · change Real.log (∫ i : InternalField N, fullDensity N β
      (assembleFine N (assembleCoarse N (fineCoordinates N b), i))) =
      Real.log (∫ ω : FullField N, fullDensity N β (pin (retainedSet 2) b ω))
    rw [assemble_fineCoordinates, integral_pin_fine]
  · change Real.log (∫ i : InterfaceField N, ∫ j : InternalField N,
      fullDensity N β (assemble N ((coarseRestriction N b, i), j))) =
      Real.log (∫ ω : FullField N, fullDensity N β (pin (retainedSet 4) b ω))
    rw [integral_pin_coarse]
    congr 1
    exact (integral_prod (fun q : InterfaceField N × InternalField N =>
      fullDensity N β (assemble N ((coarseRestriction N b, q.1), q.2)))
      (IntegralKernel.integrable_continuous_fun _ (by
        exact (fullDensity N β).continuous.comp ((continuous_assemble N).comp (by fun_prop))))).symm

/-- The first derivative of either generated log weight is the conditional
expectation of the original, locally supported Wilson action score. -/
theorem hasDerivAt_logWeight (N : ℕ) (β : ℝ) (coarse : Bool)
    (S : Finset (AssemblyLink N)) (q b : FullField N) (t : ℝ) :
    HasDerivAt (fun s ↦ logWeight N β coarse (SU2BoundaryResponse.boundaryCurve S q b s))
      (-β * expectation (Measure.pi fun _ ↦ (volume : Measure SU2))
        (SU2BoundaryResponse.boundaryDensity β univ (retainedSet (mesh coarse))
          (SU2BoundaryResponse.boundaryCurve S q b t))
        (SU2BoundaryResponse.score univ (retainedSet (mesh coarse)) S q b t)) t := by
  simp_rw [logWeight_eq_boundary]
  exact SU2BoundaryResponse.hasDerivAt_boundaryLogPartition β univ
    (retainedSet (mesh coarse)) S q b t

/-- An iterated derivative of the complete generated log weight; no generated
interaction is replaced by a new Wilson-form plaquette ansatz. -/
def mixedDerivative (N : ℕ) (β : ℝ) (coarse : Bool) (S T : Finset (AssemblyLink N))
    (q r b : FullField N) : ℝ :=
  deriv (fun t ↦ deriv (fun s ↦ logWeight N β coarse
    (SU2BoundaryResponse.boundaryCurve S q (SU2BoundaryResponse.boundaryCurve T r b t) s)) 0) 0

theorem mixedDerivative_eq_boundary (N : ℕ) (β : ℝ) (coarse : Bool)
    (S T : Finset (AssemblyLink N)) (q r b : FullField N) :
    mixedDerivative N β coarse S T q r b = SU2BoundaryResponse.mixedDerivative β univ
      (retainedSet (mesh coarse)) S T q r b := by
  unfold mixedDerivative SU2BoundaryResponse.mixedDerivative
  simp_rw [logWeight_eq_boundary]

theorem mixedDerivative_eq_covariance (N : ℕ) (β : ℝ) (coarse : Bool)
    (S T : Finset (AssemblyLink N)) (q r b : FullField N)
    (hST : Disjoint (incident S) (incident T)) :
    mixedDerivative N β coarse S T q r b =
      β ^ 2 * covariance (Measure.pi fun _ ↦ (volume : Measure SU2))
        (SU2BoundaryResponse.boundaryDensity β univ (retainedSet (mesh coarse)) b)
        (SU2BoundaryResponse.score univ (retainedSet (mesh coarse)) S q b 0)
        (SU2BoundaryResponse.score univ (retainedSet (mesh coarse)) T r b 0) := by
  rw [mixedDerivative_eq_boundary]
  exact SU2BoundaryResponse.mixedDerivative_eq_covariance β univ
    (retainedSet (mesh coarse)) S T q r b hST

/-- Both generated log weights retain the contact term for overlapping patches. -/
theorem mixedDerivative_eq_covariance_sub_contact (N : ℕ) (β : ℝ) (coarse : Bool)
    (S T : Finset (AssemblyLink N)) (q r b : FullField N) :
    mixedDerivative N β coarse S T q r b =
      β ^ 2 * covariance (Measure.pi fun _ ↦ (volume : Measure SU2))
        (SU2BoundaryResponse.boundaryDensity β univ (retainedSet (mesh coarse)) b)
        (SU2BoundaryResponse.score univ (retainedSet (mesh coarse)) S q b 0)
        (SU2BoundaryResponse.score univ (retainedSet (mesh coarse)) T r b 0) -
      β * expectation (Measure.pi fun _ ↦ (volume : Measure SU2))
        (SU2BoundaryResponse.boundaryDensity β univ (retainedSet (mesh coarse)) b)
        (SU2BoundaryResponse.contact univ (retainedSet (mesh coarse)) S T q r b 0) := by
  rw [mixedDerivative_eq_boundary]
  exact SU2BoundaryResponse.mixedDerivative_eq_covariance_sub_contact β univ
    (retainedSet (mesh coarse)) S T q r b

/-- The genuine three-patch derivative of either generated log weight. -/
def thirdDerivative (N : ℕ) (β : ℝ) (coarse : Bool) (S T V : Finset (AssemblyLink N))
    (q r u b : FullField N) : ℝ :=
  deriv (fun t ↦ mixedDerivative N β coarse S T q r (SU2BoundaryResponse.boundaryCurve V u b t)) 0

theorem thirdDerivative_eq_boundary (N : ℕ) (β : ℝ) (coarse : Bool)
    (S T V : Finset (AssemblyLink N)) (q r u b : FullField N) :
    thirdDerivative N β coarse S T V q r u b =
      SU2BoundaryResponse.thirdDerivative β univ (retainedSet (mesh coarse)) S T V q r u b := by
  unfold thirdDerivative SU2BoundaryResponse.thirdDerivative
  simp_rw [mixedDerivative_eq_boundary]

/-- The complete ordered third derivative at either actual assembly level,
including the three contact covariances and the original third action contact. -/
theorem thirdDerivative_eq_cumulant_contacts (N : ℕ) (β : ℝ) (coarse : Bool)
    (S T V : Finset (AssemblyLink N)) (q r u b : FullField N) :
    thirdDerivative N β coarse S T V q r u b =
      -β ^ 3 * thirdCumulant (Measure.pi fun _ ↦ (volume : Measure SU2))
        (SU2BoundaryResponse.boundaryDensity β univ (retainedSet (mesh coarse)) b)
        (SU2BoundaryResponse.score univ (retainedSet (mesh coarse)) S q b 0)
        (SU2BoundaryResponse.score univ (retainedSet (mesh coarse)) T r b 0)
        (SU2BoundaryResponse.score univ (retainedSet (mesh coarse)) V u b 0) +
      β ^ 2 * (covariance (Measure.pi fun _ ↦ (volume : Measure SU2))
        (SU2BoundaryResponse.boundaryDensity β univ (retainedSet (mesh coarse)) b)
        (SU2BoundaryResponse.contact univ (retainedSet (mesh coarse)) S V q u b 0)
        (SU2BoundaryResponse.score univ (retainedSet (mesh coarse)) T r b 0) +
        covariance (Measure.pi fun _ ↦ (volume : Measure SU2))
          (SU2BoundaryResponse.boundaryDensity β univ (retainedSet (mesh coarse)) b)
          (SU2BoundaryResponse.score univ (retainedSet (mesh coarse)) S q b 0)
          (SU2BoundaryResponse.contact univ (retainedSet (mesh coarse)) T V r u b 0) +
        covariance (Measure.pi fun _ ↦ (volume : Measure SU2))
          (SU2BoundaryResponse.boundaryDensity β univ (retainedSet (mesh coarse)) b)
          (SU2BoundaryResponse.contact univ (retainedSet (mesh coarse)) S T q r b 0)
          (SU2BoundaryResponse.score univ (retainedSet (mesh coarse)) V u b 0)) -
      β * expectation (Measure.pi fun _ ↦ (volume : Measure SU2))
        (SU2BoundaryResponse.boundaryDensity β univ (retainedSet (mesh coarse)) b)
        (SU2BoundaryResponse.thirdContact univ (retainedSet (mesh coarse)) S T V q r u b 0) := by
  rw [thirdDerivative_eq_boundary]
  exact SU2BoundaryResponse.thirdDerivative_eq_cumulant_contacts β univ
    (retainedSet (mesh coarse)) S T V q r u b

/-- Both original generated weights have the exact separated three-score
response, for every real beta and arbitrary frames and boundary values. -/
theorem thirdDerivative_eq_cumulant (N : ℕ) (β : ℝ) (coarse : Bool)
    (S T V : Finset (AssemblyLink N)) (q r u b : FullField N)
    (hST : Disjoint (incident S) (incident T))
    (hSV : Disjoint (incident S) (incident V))
    (hTV : Disjoint (incident T) (incident V)) :
    thirdDerivative N β coarse S T V q r u b = -β ^ 3 * thirdCumulant
      (Measure.pi fun _ ↦ (volume : Measure SU2))
      (SU2BoundaryResponse.boundaryDensity β univ (retainedSet (mesh coarse)) b)
      (SU2BoundaryResponse.score univ (retainedSet (mesh coarse)) S q b 0)
      (SU2BoundaryResponse.score univ (retainedSet (mesh coarse)) T r b 0)
      (SU2BoundaryResponse.score univ (retainedSet (mesh coarse)) V u b 0) := by
  rw [thirdDerivative_eq_boundary]
  exact SU2BoundaryResponse.thirdDerivative_eq_cumulant β univ (retainedSet (mesh coarse))
    S T V q r u b hST hSV hTV

/-- Original score third cumulance is identified with the actual coarse
GSLT remainder. The three marks are pinned at that same coarse boundary. -/
theorem scoreThirdCumulant_eq_route (N : ℕ) (β : ℝ)
    (S T V : Finset (AssemblyLink N)) (q r u b : FullField N) :
    thirdCumulant (Measure.pi fun _ ↦ (volume : Measure SU2))
      (SU2BoundaryResponse.boundaryDensity β univ (retainedSet 4) b)
      (SU2BoundaryResponse.score univ (retainedSet 4) S q b 0)
      (SU2BoundaryResponse.score univ (retainedSet 4) T r b 0)
      (SU2BoundaryResponse.score univ (retainedSet 4) V u b 0) =
      WilsonEliminationRoutes.thirdRemainder (route N β)
        (splitObservable N (SU2BoundaryResponse.score univ (retainedSet 4) S q b 0))
        (splitObservable N (SU2BoundaryResponse.score univ (retainedSet 4) T r b 0))
        (splitObservable N (SU2BoundaryResponse.score univ (retainedSet 4) V u b 0))
        (coarseRestriction N b) :=
  conditional_thirdCumulant_remainder N β _ _ _ b
    (SU2BoundaryResponse.score_pin univ (retainedSet 4) S q b)
    (SU2BoundaryResponse.score_pin univ (retainedSet 4) T r b)
    (SU2BoundaryResponse.score_pin univ (retainedSet 4) V u b)

/-- For arbitrary patches the actual coarse Hessian consists of the route's
conditional covariance and its transported original-action contact mark. -/
theorem mixedDerivative_eq_route_with_contact (N : ℕ) (β : ℝ)
    (S T : Finset (AssemblyLink N)) (q r b : FullField N) :
    mixedDerivative N β true S T q r b = β ^ 2 *
      WilsonEliminationRoutes.remainder (route N β)
        (splitObservable N (SU2BoundaryResponse.score univ (retainedSet 4) S q b 0))
        (splitObservable N (SU2BoundaryResponse.score univ (retainedSet 4) T r b 0))
        (coarseRestriction N b) -
      β * secondProjected N β (SU2BoundaryResponse.contact univ (retainedSet 4) S T q r b 0) b := by
  have hc := conditional_covariance_remainder N β _ _ b
    (SU2BoundaryResponse.score_pin univ (retainedSet 4) S q b)
    (SU2BoundaryResponse.score_pin univ (retainedSet 4) T r b)
  have hj := secondProjected_eq_pinnedExpectation N β _ b
    (SU2BoundaryResponse.contact_pin univ (retainedSet 4) S T q r b)
  exact (mixedDerivative_eq_covariance_sub_contact N β true S T q r b).trans
    (congrArg₂ (fun x y : ℝ ↦ β ^ 2 * x - β * y) hc hj.symm)

/-- The Hessian of the second generated log weight is the actual conditional
covariance remainder of the assembled two-step route. -/
theorem mixedDerivative_eq_route_remainder (N : ℕ) (β : ℝ)
    (S T : Finset (AssemblyLink N)) (q r b : FullField N)
    (hST : Disjoint (incident S) (incident T)) :
    mixedDerivative N β true S T q r b = β ^ 2 *
      WilsonEliminationRoutes.remainder (route N β)
        (splitObservable N (SU2BoundaryResponse.score univ (retainedSet 4) S q b 0))
        (splitObservable N (SU2BoundaryResponse.score univ (retainedSet 4) T r b 0))
        (coarseRestriction N b) := by
  rw [mixedDerivative_eq_covariance N β true S T q r b hST]
  congr 1
  exact conditional_covariance_remainder N β _ _ b
    (SU2BoundaryResponse.score_pin univ (retainedSet 4) S q b)
    (SU2BoundaryResponse.score_pin univ (retainedSet 4) T r b)

/-- Direct and staged second derivatives agree, including the first-stage
conditional covariance transported under the generated first density. -/
theorem mixedDerivative_staged (N : ℕ) (β : ℝ)
    (S T : Finset (AssemblyLink N)) (q r b : FullField N)
    (hST : Disjoint (incident S) (incident T)) :
    mixedDerivative N β true S T q r b =
      β ^ 2 * fiberCovariance (volume : Measure (InterfaceField N)) (firstDensity N β)
        (marginal_pos volume (density N β) (density_pos N β))
        (project (volume : Measure (InternalField N)) (density N β) (density_pos N β)
          (splitObservable N (SU2BoundaryResponse.score univ (retainedSet 4) S q b 0)))
        (project (volume : Measure (InternalField N)) (density N β) (density_pos N β)
          (splitObservable N (SU2BoundaryResponse.score univ (retainedSet 4) T r b 0)))
        (coarseRestriction N b) +
      β ^ 2 * project (volume : Measure (InterfaceField N)) (firstDensity N β)
        (marginal_pos volume (density N β) (density_pos N β))
        (fiberCovariance (volume : Measure (InternalField N)) (density N β) (density_pos N β)
          (splitObservable N (SU2BoundaryResponse.score univ (retainedSet 4) S q b 0))
          (splitObservable N (SU2BoundaryResponse.score univ (retainedSet 4) T r b 0)))
        (coarseRestriction N b) := by
  rw [mixedDerivative_eq_route_remainder N β S T q r b hST, route_remainder_staged]
  exact mul_add _ _ _

/-- The full Hessian agrees with staged Haar elimination. Both the contact
mark and the first conditional covariance pass through the generated density. -/
theorem mixedDerivative_staged_with_contact (N : ℕ) (β : ℝ)
    (S T : Finset (AssemblyLink N)) (q r b : FullField N) :
    mixedDerivative N β true S T q r b =
      β ^ 2 * fiberCovariance (volume : Measure (InterfaceField N)) (firstDensity N β)
        (marginal_pos volume (density N β) (density_pos N β))
        (project (volume : Measure (InternalField N)) (density N β) (density_pos N β)
          (splitObservable N (SU2BoundaryResponse.score univ (retainedSet 4) S q b 0)))
        (project (volume : Measure (InternalField N)) (density N β) (density_pos N β)
          (splitObservable N (SU2BoundaryResponse.score univ (retainedSet 4) T r b 0)))
        (coarseRestriction N b) -
      β * project (volume : Measure (InterfaceField N)) (firstDensity N β)
        (marginal_pos volume (density N β) (density_pos N β))
        (project (volume : Measure (InternalField N)) (density N β) (density_pos N β)
          (splitObservable N (SU2BoundaryResponse.contact univ (retainedSet 4) S T q r b 0)))
        (coarseRestriction N b) +
      β ^ 2 * project (volume : Measure (InterfaceField N)) (firstDensity N β)
        (marginal_pos volume (density N β) (density_pos N β))
        (fiberCovariance (volume : Measure (InternalField N)) (density N β) (density_pos N β)
          (splitObservable N (SU2BoundaryResponse.score univ (retainedSet 4) S q b 0))
          (splitObservable N (SU2BoundaryResponse.score univ (retainedSet 4) T r b 0)))
        (coarseRestriction N b) := by
  rw [mixedDerivative_eq_route_with_contact, route_remainder_staged, secondProjected_eq_staged]
  have h (a c j : ℝ) : β ^ 2 * (a + c) - β * j = β ^ 2 * a - β * j + β ^ 2 * c := by ring
  exact h _ _ _

/-- The same decay rate works for both actual elimination levels, before
choosing the ambient volume, background, directions and separated patches. -/
theorem uniform_mixedDerivative {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ κ > 0, ∀ (N : ℕ) (coarse : Bool) (S T : Finset (AssemblyLink N))
      (q r b : FullField N),
      (collar S).Nonempty → (collar T).Nonempty → 1 < polymerDist S T →
      |mixedDerivative N β coarse S T q r b| ≤
        3 * β ^ 2 * (256 * S.card) * (256 * T.card) *
          Real.exp (768 * (S.card + T.card) + 2 * κ) *
          Real.exp (-κ * polymerDist S T) := by
  obtain ⟨κ, hκ, h⟩ := SU2BoundaryResponse.uniform_mixedDerivative hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro N coarse S T q r b
  rw [mixedDerivative_eq_boundary]
  exact h (volumeIndex N) univ (retainedSet (mesh coarse)) S T q r b

/-- Single-link second responses of the actual generated log weight. -/
def responseArray (N : ℕ) (β : ℝ) (coarse : Bool) (q r b : FullField N) :
    AssemblyLink N → AssemblyLink N → ℝ :=
  fun l m ↦ mixedDerivative N β coarse {l} {m} q r b

theorem responseArray_eq_boundary (N : ℕ) (β : ℝ) (coarse : Bool)
    (q r b : FullField N) :
    responseArray N β coarse q r b = SU2BoundaryResponse.responseArray β univ
      (retainedSet (mesh coarse)) q r b := by
  funext l m
  exact mixedDerivative_eq_boundary N β coarse {l} {m} q r b

/-- Both exact assembly levels satisfy the same bound on total weighted
boundary influence. Constants precede the level, spatial volume, boundary
values and frames; nearby and diagonal contacts are included. -/
theorem uniform_weightedResponseSeminorm {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ η > 0, ∃ C ≥ 0, ∀ (N : ℕ) (coarse : Bool) (q r b : FullField N),
      WilsonBoundaryResponse.weightedResponseSeminorm η
        (responseArray N β coarse q r b) ≤ C := by
  obtain ⟨η, hη, C, hC, h⟩ := SU2BoundaryResponse.uniform_weightedResponseSeminorm hβ hβ0
  refine ⟨η, hη, C, hC, ?_⟩
  intro N coarse q r b
  rw [responseArray_eq_boundary]
  exact h (volumeIndex N) univ (retainedSet (mesh coarse)) q r b

/-- The weighted influence of any individual retained or unretained link is
bounded by the same volume-independent constant at either assembly level. -/
theorem uniform_weightedResponseRow {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ η > 0, ∃ C ≥ 0, ∀ (N : ℕ) (coarse : Bool) (q r b : FullField N)
      (l : AssemblyLink N),
      ∑ m, Real.exp (η * dist l m) * |responseArray N β coarse q r b l m| ≤ C := by
  obtain ⟨η, hη, C, hC, h⟩ := uniform_weightedResponseSeminorm hβ hβ0
  refine ⟨η, hη, C, hC, ?_⟩
  intro N coarse q r b l
  exact (WilsonBoundaryResponse.weightedResponseRow_le η l _).trans (h N coarse q r b)

/-- Actual singleton score cumulants at either assembly level. -/
def scoreThirdArray (N : ℕ) (β : ℝ) (coarse : Bool) (q r u b : FullField N) :
    AssemblyLink N → AssemblyLink N → AssemblyLink N → ℝ :=
  SU2BoundaryResponse.scoreThirdArray β univ (retainedSet (mesh coarse)) q r u b

/-- The same spatial exponent and third-cumulant budget work for both
generated densities, before choosing volume, boundary data or frames. -/
theorem uniform_weightedThirdSeminorm {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ η > 0, ∃ C ≥ 0, ∀ (N : ℕ) (coarse : Bool) (q r u b : FullField N),
      WilsonBoundaryResponse.weightedThirdSeminorm η
        (scoreThirdArray N β coarse q r u b) ≤ C := by
  obtain ⟨η, hη, C, hC, h⟩ := SU2BoundaryResponse.uniform_weightedThirdSeminorm hβ hβ0
  exact ⟨η, hη, C, hC, fun N coarse q r u b ↦
    h (volumeIndex N) univ (retainedSet (mesh coarse)) q r u b⟩

theorem uniform_weightedThirdRow {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ η > 0, ∃ C ≥ 0, ∀ (N : ℕ) (coarse : Bool) (q r u b : FullField N)
      (l : AssemblyLink N),
      ∑ m, ∑ k, Real.exp (η * WilsonBoundaryResponse.threeTreeLength l m k) *
        |scoreThirdArray N β coarse q r u b l m k| ≤ C := by
  obtain ⟨η, hη, C, hC, h⟩ := uniform_weightedThirdSeminorm hβ hβ0
  refine ⟨η, hη, C, hC, ?_⟩
  intro N coarse q r u b l
  exact (WilsonBoundaryResponse.weightedThirdRow_le η l _).trans (h N coarse q r u b)

/-- Original Wilson scores used as fixed local probes in either exact Haar
integration. At their prescribed boundary they are the derivative scores. -/
def scoreFamily (N : ℕ) (coarse : Bool) (q b : FullField N) :
    AssemblyLink N → C(FullField N, ℝ) := fun l ↦
  SU2BoundaryResponse.score univ (retainedSet (mesh coarse)) {l} q b 0

/-- The actual Wilson score family inhabits the quantitative boundary
contract after each Haar step. No analytic contract is an input hypothesis. -/
theorem uniform_scoreResponseContract {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ η > 0, ∃ C₂ ≥ 0, ∃ C₃ ≥ 0,
      ∀ (N : ℕ) (coarse : Bool) (q b : FullField N),
        WilsonEliminationRoutes.boundaryContract η 256 C₂ C₃
          (firstResponseState N β (scoreFamily N coarse q b)) ∧
        WilsonEliminationRoutes.boundaryContract η 256 C₂ C₃
          (secondResponseState N β (scoreFamily N coarse q b)) := by
  obtain ⟨η, hη, C₂, hC₂, C₃, hC₃, hc⟩ :=
    uniform_responseContract hβ hβ0 (show (0 : ℝ) ≤ 256 by norm_num)
  refine ⟨η, hη, C₂, hC₂, C₃, hC₃, ?_⟩
  intro N coarse q b
  exact hc N (scoreFamily N coarse q b)
    (fun l ↦ SU2BoundaryResponse.score_local univ (retainedSet (mesh coarse)) {l} q b 0)
    (fun l ↦ by simpa [scoreFamily] using
      SU2BoundaryResponse.abs_score_le univ (retainedSet (mesh coarse)) {l} q b 0)

/-- Quantitative composition for the actual Wilson scores. The source
budgets, new conditional budgets and all three mixed costs are proved;
none is an additional hypothesis on the generated measure. -/
theorem uniform_scoreCompositionContract {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ η > 0, ∃ C₂ ≥ 0, ∃ C₃ ≥ 0, ∃ D₂ ≥ 0, ∃ D₃ ≥ 0, ∃ E ≥ 0,
      ∀ (N : ℕ) (coarse : Bool) (q b : FullField N),
        WilsonEliminationRoutes.boundaryContract η 256 C₂ C₃
          (firstResponseState N β (scoreFamily N coarse q b)) ∧
        WilsonEliminationRoutes.boundaryContract η 256 (C₂ + D₂) (C₃ + D₃ + 3 * E)
          (secondResponseState N β (scoreFamily N coarse q b)) := by
  obtain ⟨η, hη, C₂, hC₂, C₃, hC₃, D₂, hD₂, D₃, hD₃, E, hE, hc⟩ :=
    uniform_composed_responseContract hβ hβ0 (show (0 : ℝ) ≤ 256 by norm_num)
  refine ⟨η, hη, C₂, hC₂, C₃, hC₃, D₂, hD₂, D₃, hD₃, E, hE, ?_⟩
  intro N coarse q b
  exact hc N (scoreFamily N coarse q b)
    (fun l ↦ SU2BoundaryResponse.score_local univ (retainedSet (mesh coarse)) {l} q b 0)
    (fun l ↦ by simpa [scoreFamily] using
      SU2BoundaryResponse.abs_score_le univ (retainedSet (mesh coarse)) {l} q b 0)

theorem uniform_scoreContract_reachable {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ η > 0, ∃ C₂ ≥ 0, ∃ C₃ ≥ 0,
      ∀ (N : ℕ) (coarse : Bool) (q b : FullField N),
        Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond
          (WilsonEliminationRoutes.haarTheory (AssemblyLink N))
          (WilsonEliminationRoutes.boundaryContract η 256 C₂ C₃)
          (initialResponseState N β (scoreFamily N coarse q b)) ∧
        Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond
          (WilsonEliminationRoutes.haarTheory (AssemblyLink N))
          (WilsonEliminationRoutes.boundaryContract η 256 C₂ C₃)
          (firstResponseState N β (scoreFamily N coarse q b)) := by
  obtain ⟨η, hη, C₂, hC₂, C₃, hC₃, hc⟩ :=
    uniform_responseContract_reachable hβ hβ0 (show (0 : ℝ) ≤ 256 by norm_num)
  refine ⟨η, hη, C₂, hC₂, C₃, hC₃, ?_⟩
  intro N coarse q b
  exact hc N (scoreFamily N coarse q b)
    (fun l ↦ SU2BoundaryResponse.score_local univ (retainedSet (mesh coarse)) {l} q b 0)
    (fun l ↦ by simpa [scoreFamily] using
      SU2BoundaryResponse.abs_score_le univ (retainedSet (mesh coarse)) {l} q b 0)

/-- Mixed finite change of the complete effective log weight. -/
def mixedChange (N : ℕ) (β : ℝ) (coarse : Bool) (S T : Finset (AssemblyLink N))
    (b a c : FullField N) : ℝ :=
  logWeight N β coarse (replace T c (replace S a b)) + logWeight N β coarse b -
    logWeight N β coarse (replace S a b) - logWeight N β coarse (replace T c b)

theorem mixedChange_eq_response (N : ℕ) (β : ℝ) (coarse : Bool)
    (S T : Finset (AssemblyLink N)) (b a c : FullField N) :
    mixedChange N β coarse S T b a c = SU2BoundaryResponse.response β (volumeIndex N)
      univ (retainedSet (mesh coarse)) S T b a c := by
  unfold mixedChange
  simp_rw [logWeight_eq_boundary]
  rfl

/-- The rate is chosen before the volume, elimination level, changed patches
and all boundary values. Only the two patch sizes enter the prefactor. -/
theorem uniform_mixedChange {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ κ > 0, ∀ (N : ℕ) (coarse : Bool) (S T : Finset (AssemblyLink N))
      (b a c : FullField N),
      (collar S).Nonempty → (collar T).Nonempty → 1 < polymerDist S T →
      |mixedChange N β coarse S T b a c| ≤
        3 * Real.exp ((256*β + 768) * (S.card + T.card) + 2*κ) *
          Real.exp (-κ * polymerDist S T) := by
  obtain ⟨κ, hκ, h⟩ := SU2WilsonSeparatorComparison.both_separators_response hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro N coarse S T b a c
  rw [mixedChange_eq_response]
  exact h N (mesh coarse) S T b a c

theorem heldFace_subset_separator (n s : ℕ) :
    SU2BoundaryResponse.heldFace n ⊆ (retainedSet s : Finset (Link 4 n)) := by
  intro l hl
  obtain ⟨hdir, hface⟩ := (mem_filter.mp hl).2
  apply mem_filter.mpr
  refine ⟨mem_univ _, 1, Ne.symm hdir, ?_⟩
  rw [hface, ZMod.val_zero]
  exact dvd_zero _

/-- The separated patches used below are contained in both actual separators. -/
theorem growing_patches_retained (N : ℕ) (coarse : Bool) :
    SU2BoundaryResponse.firstPatch N ∪ SU2BoundaryResponse.secondPatch N ⊆
      (retainedSet (mesh coarse) : Finset (AssemblyLink N)) :=
  (SU2BoundaryResponse.growing_patches_on_face N).trans
    (heldFace_subset_separator _ _)

/-- A nonvacuous growing-separation estimate for each actual effective weight. -/
theorem growing_mixedChange {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ κ > 0, ∀ (N : ℕ) (coarse : Bool) (b a c : FullField N),
      |mixedChange N β coarse (SU2BoundaryResponse.firstPatch N)
        (SU2BoundaryResponse.secondPatch N) b a c| ≤
      3 * Real.exp (512*β + 1536 + 2*κ) * Real.exp (-κ * ((N : ℝ) + 3)) := by
  obtain ⟨κ, hκ, h⟩ := SU2BoundaryResponse.growing_family_bound hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro N coarse b a c
  rw [mixedChange_eq_response]
  exact h N univ (retainedSet (mesh coarse)) b a c

/-- The actual mixed change tends to zero, allowing both the selected level
and the boundary assignments to vary with volume. -/
theorem tendsto_mixedChange {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4)
    (coarse : ℕ → Bool) (b a c : ∀ N, FullField N) :
    Tendsto (fun N => mixedChange N β (coarse N) (SU2BoundaryResponse.firstPatch N)
      (SU2BoundaryResponse.secondPatch N) (b N) (a N) (c N)) atTop (𝓝 0) := by
  simp_rw [mixedChange_eq_response]
  exact SU2BoundaryResponse.tendsto_growing_response hβ hβ0 (fun _ => univ)
    (fun N => retainedSet (mesh (coarse N))) b a c

theorem growing_mixedDerivative {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4) :
    ∃ κ > 0, ∀ (N : ℕ) (coarse : Bool) (q r b : FullField N),
      |mixedDerivative N β coarse (SU2BoundaryResponse.firstPatch N)
        (SU2BoundaryResponse.secondPatch N) q r b| ≤
        3 * β ^ 2 * 256 ^ 2 * Real.exp (1536 + 2 * κ) *
          Real.exp (-κ * ((N : ℝ) + 3)) := by
  obtain ⟨κ, hκ, h⟩ := SU2BoundaryResponse.growing_mixedDerivative_bound hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro N coarse q r b
  rw [mixedDerivative_eq_boundary]
  exact h N univ (retainedSet (mesh coarse)) q r b

theorem tendsto_mixedDerivative {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 4)
    (coarse : ℕ → Bool) (q r b : ∀ N, FullField N) :
    Tendsto (fun N ↦ mixedDerivative N β (coarse N) (SU2BoundaryResponse.firstPatch N)
      (SU2BoundaryResponse.secondPatch N) (q N) (r N) (b N)) atTop (𝓝 0) := by
  simp_rw [mixedDerivative_eq_boundary]
  exact SU2BoundaryResponse.tendsto_growing_mixedDerivative hβ hβ0 (fun _ ↦ univ)
    (fun N ↦ retainedSet (mesh (coarse N))) q r b

#print axioms logWeight_eq_boundary
#print axioms hasDerivAt_logWeight
#print axioms mixedDerivative_eq_covariance
#print axioms mixedDerivative_staged
#print axioms mixedDerivative_eq_covariance_sub_contact
#print axioms mixedDerivative_staged_with_contact
#print axioms thirdDerivative_eq_cumulant
#print axioms scoreThirdCumulant_eq_route
#print axioms uniform_mixedDerivative
#print axioms uniform_weightedResponseSeminorm
#print axioms uniform_weightedResponseRow
#print axioms tendsto_mixedDerivative
#print axioms uniform_mixedChange
#print axioms growing_patches_retained
#print axioms growing_mixedChange
#print axioms tendsto_mixedChange
/-! ## Responses under the actual scale-two product constraint

The remaining integration variables carry product Haar measure. Their positive
weight is the complete fine Wilson density evaluated in the block chart; it
is not the law obtained by pinning individual fine links. The unitary rotation
frames depend on fluctuation variables, and all ordered contact terms remain.
-/

namespace ScaleTwo
open StrongCouplingCrossing WilsonDyadicGeometry SU2WilsonBlockPilot WilsonBlockElimination
open SU2BoundaryResponse SU2WilsonAssembly.ScaleTwo
variable {n : ℕ}

def configuration (c : CoarseConfig n) : C(Fluctuation n, FineConfig n) :=
  ⟨fun f ↦ chart n (c, f), (PairedLinks.continuous_chart (E := SU2) (blockIndexEquiv 4 n)).comp
    (continuous_const.prodMk continuous_id)⟩

/-- The fine Wilson density in the exact product-constrained Haar chart. -/
def fiberDensity (β : ℝ) (c : CoarseConfig n) : C(Fluctuation n, ℝ) :=
  (fineDensity n β).comp (configuration c)

theorem fiberDensity_pos (β : ℝ) (c : CoarseConfig n) (f : Fluctuation n) :
    0 < fiberDensity β c f := fineDensity_pos n β _

theorem integral_fiberDensity (β : ℝ) (c : CoarseConfig n) :
    (∫ f, fiberDensity β c f) = coarseDensity n β c := rfl

theorem fiberDensity_eq_pinned (β : ℝ) (c : CoarseConfig n) (f : Fluctuation n) :
    fiberDensity β c f = boundaryDensity β univ univ (chart n (c, f)) (fun _ ↦ 1) := by
  simp only [fiberDensity, configuration, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    fineDensity, boundaryDensity, WilsonLocalResponse.realDensity,
    StrongCouplingCrossing.potential, InhomogeneousWilsonCrossing.Model.pinned,
    Finset.mem_univ, ↓reduceIte]
  rfl

def blockScore (S : Finset (Link 4 n)) (q c : CoarseConfig n) (t : ℝ) :
    C(Fluctuation n, ℝ) :=
  ⟨fun f ↦ score univ univ (liftPatch S) (liftFrame q f) (chart n (c, f)) t (fun _ ↦ 1),
    continuous_score_parametric univ univ (liftPatch S) (continuous_liftFrame q)
      (configuration c).continuous continuous_const continuous_const⟩

def blockContact (S T : Finset (Link 4 n)) (q r c : CoarseConfig n) (t : ℝ) :
    C(Fluctuation n, ℝ) :=
  ⟨fun f ↦ contact univ univ (liftPatch S) (liftPatch T)
    (liftFrame q f) (liftFrame r f) (chart n (c, f)) t (fun _ ↦ 1),
    continuous_contact_parametric univ univ (liftPatch S) (liftPatch T)
      (continuous_liftFrame q) (continuous_liftFrame r)
      (configuration c).continuous continuous_const continuous_const⟩

def blockThirdContact (S T V : Finset (Link 4 n)) (q r u c : CoarseConfig n) (t : ℝ) :
    C(Fluctuation n, ℝ) :=
  ⟨fun f ↦ thirdContact univ univ (liftPatch S) (liftPatch T) (liftPatch V)
    (liftFrame q f) (liftFrame r f) (liftFrame u f) (chart n (c, f)) t (fun _ ↦ 1),
    continuous_thirdContact_parametric univ univ (liftPatch S) (liftPatch T) (liftPatch V)
      (continuous_liftFrame q) (continuous_liftFrame r) (continuous_liftFrame u)
      (configuration c).continuous continuous_const continuous_const⟩

theorem abs_blockScore_le (S : Finset (Link 4 n)) (q c : CoarseConfig n) (t : ℝ)
    (f : Fluctuation n) : |blockScore S q c t f| ≤ 256 * S.card := by
  simpa only [blockScore, ContinuousMap.coe_mk, card_liftPatch] using
    abs_score_le univ univ (liftPatch S) (liftFrame q f) (chart n (c, f)) t (fun _ ↦ 1)

theorem abs_blockContact_le (S T : Finset (Link 4 n)) (q r c : CoarseConfig n) (t : ℝ)
    (f : Fluctuation n) : |blockContact S T q r c t f| ≤ 1024 * S.card := by
  simpa only [blockContact, ContinuousMap.coe_mk, card_liftPatch] using abs_contact_le univ univ (liftPatch S) (liftPatch T)
    (liftFrame q f) (liftFrame r f) (chart n (c, f)) t (fun _ ↦ 1)

theorem abs_blockThirdContact_le (S T V : Finset (Link 4 n))
    (q r u c : CoarseConfig n) (t : ℝ) (f : Fluctuation n) :
    |blockThirdContact S T V q r u c t f| ≤ 4096 * S.card := by
  simpa only [blockThirdContact, ContinuousMap.coe_mk, card_liftPatch] using abs_thirdContact_le univ univ
    (liftPatch S) (liftPatch T) (liftPatch V)
    (liftFrame q f) (liftFrame r f) (liftFrame u f) (chart n (c, f)) t (fun _ ↦ 1)

theorem continuous_configuration_curve (S : Finset (Link 4 n)) (q c : CoarseConfig n) :
    Continuous (fun z : ℝ × Fluctuation n ↦ chart n (boundaryCurve S q c z.1, z.2)) :=
  (PairedLinks.continuous_chart (E := SU2) (blockIndexEquiv 4 n)).comp
    (((continuous_boundaryCurve S q c).comp continuous_fst).prodMk continuous_snd)

theorem continuous_fiberDensity_curve (β : ℝ) (S : Finset (Link 4 n)) (q c : CoarseConfig n) :
    Continuous (fun z : ℝ × Fluctuation n ↦ fiberDensity β (boundaryCurve S q c z.1) z.2) :=
  (fineDensity n β).continuous.comp (continuous_configuration_curve S q c)

theorem continuous_blockScore (S : Finset (Link 4 n)) (q c : CoarseConfig n) :
    Continuous (fun z : ℝ × Fluctuation n ↦ blockScore S q c z.1 z.2) :=
  continuous_score_parametric univ univ (liftPatch S)
    ((continuous_liftFrame q).comp continuous_snd)
    ((configuration c).continuous.comp continuous_snd) continuous_const continuous_fst

theorem continuous_blockScore_other (S V : Finset (Link 4 n)) (q u c : CoarseConfig n) :
    Continuous (fun z : ℝ × Fluctuation n ↦ blockScore S q (boundaryCurve V u c z.1) 0 z.2) :=
  continuous_score_parametric univ univ (liftPatch S)
    ((continuous_liftFrame q).comp continuous_snd)
    (continuous_configuration_curve V u c) continuous_const continuous_const

theorem continuous_blockContact (S T : Finset (Link 4 n)) (q r c : CoarseConfig n) :
    Continuous (fun z : ℝ × Fluctuation n ↦ blockContact S T q r c z.1 z.2) :=
  continuous_contact_parametric univ univ (liftPatch S) (liftPatch T)
    ((continuous_liftFrame q).comp continuous_snd) ((continuous_liftFrame r).comp continuous_snd)
    ((configuration c).continuous.comp continuous_snd) continuous_const continuous_fst

theorem continuous_blockContact_other (S T V : Finset (Link 4 n))
    (q r u c : CoarseConfig n) :
    Continuous (fun z : ℝ × Fluctuation n ↦
      blockContact S T q r (boundaryCurve V u c z.1) 0 z.2) :=
  continuous_contact_parametric univ univ (liftPatch S) (liftPatch T)
    ((continuous_liftFrame q).comp continuous_snd) ((continuous_liftFrame r).comp continuous_snd)
    (continuous_configuration_curve V u c) continuous_const continuous_const

theorem continuous_blockThirdContact (S T V : Finset (Link 4 n))
    (q r u c : CoarseConfig n) :
    Continuous (fun z : ℝ × Fluctuation n ↦ blockThirdContact S T V q r u c z.1 z.2) :=
  continuous_thirdContact_parametric univ univ (liftPatch S) (liftPatch T) (liftPatch V)
    ((continuous_liftFrame q).comp continuous_snd) ((continuous_liftFrame r).comp continuous_snd)
    ((continuous_liftFrame u).comp continuous_snd)
    ((configuration c).continuous.comp continuous_snd) continuous_const continuous_fst

theorem hasDerivAt_fiberDensity (β : ℝ) (S : Finset (Link 4 n))
    (q c : CoarseConfig n) (t : ℝ) (f : Fluctuation n) :
    HasDerivAt (fun s ↦ fiberDensity β (boundaryCurve S q c s) f)
      (-β * (fiberDensity β (boundaryCurve S q c t) f * blockScore S q c t f)) t := by
  simp_rw [fiberDensity_eq_pinned, chart_boundaryCurve]
  exact hasDerivAt_boundaryDensity β univ univ (liftPatch S)
    (liftFrame q f) (chart n (c, f)) t (fun _ ↦ 1)

theorem hasDerivAt_blockScore_contact (S T : Finset (Link 4 n))
    (q r c : CoarseConfig n) (t : ℝ) (f : Fluctuation n) :
    HasDerivAt (fun s ↦ blockScore S q (boundaryCurve T r c s) 0 f)
      (blockContact S T q r c t f) t := by
  simp only [blockScore, ContinuousMap.coe_mk]
  simp_rw [chart_boundaryCurve T r c f]
  exact hasDerivAt_score_contact univ univ (liftPatch S) (liftPatch T)
    (liftFrame q f) (liftFrame r f) (chart n (c, f)) t (fun _ ↦ 1)

theorem hasDerivAt_blockContact_thirdContact (S T V : Finset (Link 4 n))
    (q r u c : CoarseConfig n) (t : ℝ) (f : Fluctuation n) :
    HasDerivAt (fun s ↦ blockContact S T q r (boundaryCurve V u c s) 0 f)
      (blockThirdContact S T V q r u c t f) t := by
  simp only [blockContact, ContinuousMap.coe_mk]
  simp_rw [chart_boundaryCurve V u c f]
  exact hasDerivAt_contact_thirdContact univ univ (liftPatch S) (liftPatch T) (liftPatch V)
    (liftFrame q f) (liftFrame r f) (liftFrame u f) (chart n (c, f)) t (fun _ ↦ 1)

def blockLogWeight (β : ℝ) (c : CoarseConfig n) : ℝ := Real.log (coarseDensity n β c)

theorem hasDerivAt_blockLogWeight (β : ℝ) (S : Finset (Link 4 n))
    (q c : CoarseConfig n) (t : ℝ) :
    HasDerivAt (fun s ↦ blockLogWeight β (boundaryCurve S q c s))
      (-β * expectation volume (fiberDensity β (boundaryCurve S q c t)) (blockScore S q c t)) t := by
  have h := WilsonBoundaryResponse.hasDerivAt_logPartition volume β
    (fun t ↦ fiberDensity β (boundaryCurve S q c t)) (blockScore S q c)
    (continuous_fiberDensity_curve β S q c) (continuous_blockScore S q c)
    (hasDerivAt_fiberDensity β S q c) t (fiberDensity_pos β _)
  simpa only [WilsonBoundaryResponse.logPartition, integral_fiberDensity, blockLogWeight] using h

def blockMixedDerivative (β : ℝ) (S T : Finset (Link 4 n)) (q r c : CoarseConfig n) : ℝ :=
  deriv (fun t ↦ deriv (fun s ↦ blockLogWeight β
    (boundaryCurve S q (boundaryCurve T r c t) s)) 0) 0

theorem blockMixedDerivative_eq_covariance_sub_contact (β : ℝ) (S T : Finset (Link 4 n))
    (q r c : CoarseConfig n) :
    blockMixedDerivative β S T q r c =
      β ^ 2 * covariance volume (fiberDensity β c) (blockScore S q c 0) (blockScore T r c 0) -
      β * expectation volume (fiberDensity β c) (blockContact S T q r c 0) := by
  have hd (t : ℝ) := (hasDerivAt_blockLogWeight β S q (boundaryCurve T r c t) 0).deriv
  simp only [boundaryCurve_zero] at hd
  unfold blockMixedDerivative
  simp_rw [hd]
  have h := WilsonBoundaryResponse.hasDerivAt_logPartitionScore volume β
    (fun t ↦ fiberDensity β (boundaryCurve T r c t))
    (fun t ↦ blockScore S q (boundaryCurve T r c t) 0)
    (blockScore T r c) (blockContact S T q r c)
    (continuous_fiberDensity_curve β T r c) (continuous_blockScore_other S T q r c)
    (continuous_blockScore T r c) (continuous_blockContact S T q r c)
    (hasDerivAt_fiberDensity β T r c) (hasDerivAt_blockScore_contact S T q r c) 0
    (fiberDensity_pos β _)
  simpa only [boundaryCurve_zero] using h.deriv

def blockThirdDerivative (β : ℝ) (S T V : Finset (Link 4 n)) (q r u c : CoarseConfig n) : ℝ :=
  deriv (fun t ↦ blockMixedDerivative β S T q r (boundaryCurve V u c t)) 0

/-- The full ordered third derivative of the actual scale-two Wilson log
weight. Expectations use the constrained Haar law `fiberDensity`, and every
contact term remains even for coincident patches. Valid for every real beta. -/
theorem blockThirdDerivative_eq_cumulant_contacts (β : ℝ) (S T V : Finset (Link 4 n))
    (q r u c : CoarseConfig n) :
    blockThirdDerivative β S T V q r u c =
      -β ^ 3 * thirdCumulant volume (fiberDensity β c)
        (blockScore S q c 0) (blockScore T r c 0) (blockScore V u c 0) +
      β ^ 2 * (covariance volume (fiberDensity β c)
          (blockContact S V q u c 0) (blockScore T r c 0) +
        covariance volume (fiberDensity β c) (blockScore S q c 0) (blockContact T V r u c 0) +
        covariance volume (fiberDensity β c) (blockContact S T q r c 0) (blockScore V u c 0)) -
      β * expectation volume (fiberDensity β c) (blockThirdContact S T V q r u c 0) := by
  have h := WilsonBoundaryResponse.hasDerivAt_logPartitionHessian volume β
    (fun t ↦ fiberDensity β (boundaryCurve V u c t)) (blockScore V u c)
    (fun t ↦ blockScore S q (boundaryCurve V u c t) 0)
    (fun t ↦ blockScore T r (boundaryCurve V u c t) 0)
    (fun t ↦ blockContact S T q r (boundaryCurve V u c t) 0)
    (blockContact S V q u c) (blockContact T V r u c) (blockThirdContact S T V q r u c)
    (continuous_fiberDensity_curve β V u c) (continuous_blockScore V u c)
    (continuous_blockScore_other S V q u c) (continuous_blockScore_other T V r u c)
    (continuous_blockContact_other S T V q r u c)
    (continuous_blockContact S V q u c) (continuous_blockContact T V r u c)
    (continuous_blockThirdContact S T V q r u c)
    (hasDerivAt_fiberDensity β V u c) (hasDerivAt_blockScore_contact S V q u c)
    (hasDerivAt_blockScore_contact T V r u c) (hasDerivAt_blockContact_thirdContact S T V q r u c)
    0 (fiberDensity_pos β _)
  unfold blockThirdDerivative
  simp_rw [blockMixedDerivative_eq_covariance_sub_contact]
  simpa only [boundaryCurve_zero] using h.deriv

/-- Rotation sites are second halves, not the even anchors. Their bounded
shift costs `exp(2η)` for the second response after doubling the rate. -/
theorem weightedSecond_blockEdges (η : ℝ) (hη : 0 ≤ η)
    (H : Link 4 (doubleIndex n) → Link 4 (doubleIndex n) → ℝ) :
    WilsonBoundaryResponse.weightedResponseSeminorm (2 * η)
      (fun i j : Link 4 n ↦ H (blockEdge i 1) (blockEdge j 1)) ≤
      Real.exp (2 * η) * WilsonBoundaryResponse.weightedResponseSeminorm η H := by
  simpa only [mul_comm η 2] using
    WilsonBoundaryResponse.weightedResponseSeminorm_reindex_le_of_dist_le
      (fun i : Link 4 n ↦ blockEdge i 1)
      (fun i j h ↦ congrArg Prod.fst (@blockEdge_injective 4 n (i, 1) (j, 1) h))
      2 η 2 hη dist_coarse_le_second H

/-- The two edges of a three-point tree cost `exp(4η)` under the same
representative shift. This is a geometric comparison of response arrays. -/
theorem weightedThird_blockEdges (η : ℝ) (hη : 0 ≤ η)
    (H : Link 4 (doubleIndex n) → Link 4 (doubleIndex n) → Link 4 (doubleIndex n) → ℝ) :
    WilsonBoundaryResponse.weightedThirdSeminorm (2 * η)
      (fun i j k : Link 4 n ↦ H (blockEdge i 1) (blockEdge j 1) (blockEdge k 1)) ≤
      Real.exp (4 * η) * WilsonBoundaryResponse.weightedThirdSeminorm η H := by
  convert WilsonBoundaryResponse.weightedThirdSeminorm_reindex_le_of_dist_le
      (fun i : Link 4 n ↦ blockEdge i 1)
      (fun i j h ↦ congrArg Prod.fst (@blockEdge_injective 4 n (i, 1) (j, 1) h))
      2 η 2 (by norm_num) hη dist_coarse_le_second H using 1 <;> ring_nf

end ScaleTwo

end Mettapedia.QuantumTheory.YangMills.SU2WilsonEffectiveInteraction
