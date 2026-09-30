import Mettapedia.QuantumTheory.YangMills.SU2WilsonAssemblyLocality
import Mettapedia.QuantumTheory.YangMills.SU2WilsonSeparatorComparison

/-!
# Spatial response of the actual two-level effective Wilson weights

The logarithms of both assembly marginals are the boundary log partition
functions used in the spatial response theorem. Their mixed finite changes
therefore decay uniformly in surrounding volume at strong coupling. The
growing family changes genuine retained links at both levels.
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

def fineCoordinates (N : ℕ) (b : FullField N) : CoarseField N × InterfaceField N :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : FineLink N => SU2)
    (fun l => Retained 4 l.val) (fineRestriction N b)

theorem assemble_fineCoordinates (N : ℕ) (b : FullField N) :
    assembleCoarse N (fineCoordinates N b) = fineRestriction N b :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : FineLink N => SU2)
    (fun l => Retained 4 l.val)).symm_apply_apply _

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
#print axioms uniform_mixedDerivative
#print axioms tendsto_mixedDerivative
#print axioms uniform_mixedChange
#print axioms growing_patches_retained
#print axioms growing_mixedChange
#print axioms tendsto_mixedChange
end Mettapedia.QuantumTheory.YangMills.SU2WilsonEffectiveInteraction
