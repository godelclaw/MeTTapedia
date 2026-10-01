import Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly
import Mettapedia.QuantumTheory.YangMills.WilsonDyadicProjection
import Mettapedia.QuantumTheory.YangMills.WilsonProjectionComposition

/-!
# Locality of the two actual SU(2) assembly projections

The normalized projections in the assembled GSLT route coincide pointwise
with Wilson conditional expectations at the fine and coarse separators.
Thus the geometric locality theorem applies to the actual operators,
including the second operator with its generated effective density.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Finset MeasureTheory
open scoped Topology Classical
namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonAssemblyLocality
open SU2WilsonAssembly SU2WilsonBlockPilot WilsonDyadicGeometry
open WilsonDyadicLocality WilsonDyadicProjection WilsonPinnedIntegral
open WilsonBlockElimination WilsonProductLocality CompactTransferGap

def fineRestriction (N : ℕ) (b : FullField N) : FineField N := fun l => b l.val
def coarseRestriction (N : ℕ) (b : FullField N) : CoarseField N := fun l => b l.val.val

def fineCoordinates (N : ℕ) (b : FullField N) : CoarseField N × InterfaceField N :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : FineLink N => SU2)
    (fun l => Retained 4 l.val) (fineRestriction N b)

theorem assemble_fineCoordinates (N : ℕ) (b : FullField N) :
    assembleCoarse N (fineCoordinates N b) = fineRestriction N b :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : FineLink N => SU2)
    (fun l => Retained 4 l.val)).symm_apply_apply _

theorem pin_fine_assemble (N : ℕ) (b : FullField N)
    (p : FineField N × InternalField N) :
    pin (retainedSet 2) b (assembleFine N p) = assembleFine N (fineRestriction N b, p.2) := by
  funext l
  by_cases h : Retained 2 l <;>
    simp [pin, retainedSet, assembleFine, fineRestriction,
      MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply, h]

theorem pin_coarse_assemble (N : ℕ) (b : FullField N) (p : SplitField N) :
    pin (retainedSet 4) b (assemble N p) =
      assemble N ((coarseRestriction N b, p.1.2), p.2) := by
  funext l
  by_cases h4 : Retained 4 l
  · have h2 := coarse_retained_fine l h4
    simp [pin, retainedSet, assemble, assembleFine, assembleCoarse, coarseRestriction,
      MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply, h4, h2]
  · by_cases h2 : Retained 2 l <;>
      simp [pin, retainedSet, assemble, assembleFine, assembleCoarse,
        MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply, h4, h2]

/-- Pinning the fine separator integrates precisely the original fine interiors. -/
theorem integral_pin_fine (N : ℕ) (b : FullField N) (F : FullField N → ℝ) :
    (∫ ω : FullField N, F (pin (retainedSet 2) b ω)) =
      ∫ i : InternalField N, F (assembleFine N (fineRestriction N b, i)) := by
  rw [← integral_assembleFine N (fun ω => F (pin (retainedSet 2) b ω))]
  simp_rw [pin_fine_assemble]
  simpa using (integral_fun_snd (μ := (volume : Measure (FineField N)))
    (ν := (volume : Measure (InternalField N)))
    (fun i => F (assembleFine N (fineRestriction N b, i))))

/-- Pinning the coarse separator integrates both original groups of eliminated
variables; the coarse-coordinate probability factor cancels exactly. -/
theorem integral_pin_coarse (N : ℕ) (b : FullField N) (F : C(FullField N, ℝ)) :
    (∫ ω : FullField N, F (pin (retainedSet 4) b ω)) =
      ∫ q : InterfaceField N × InternalField N,
        F (assemble N ((coarseRestriction N b, q.1), q.2)) ∂volume.prod volume := by
  let H := WilsonConditionalProjection.pinnedMark (retainedSet 4) b F
  change (∫ ω, H ω) = _
  rw [← integral_assemble N H]
  change (∫ p : SplitField N, F (pin (retainedSet 4) b (assemble N p))
    ∂(volume.prod volume).prod volume) = _
  simp_rw [pin_coarse_assemble]
  rw [integral_prod (fun p : SplitField N =>
    F (assemble N ((coarseRestriction N b, p.1.2), p.2)))
    (IntegralKernel.integrable_continuous_fun _ (by
      exact F.continuous.comp ((continuous_assemble N).comp (by fun_prop))))]
  change (∫ x : CoarseField N × InterfaceField N,
    (∫ y : InternalField N, F (assemble N ((coarseRestriction N b, x.2), y)))
      ∂volume.prod volume) = _
  have hdummy := integral_fun_snd (μ := (volume : Measure (CoarseField N)))
    (ν := (volume : Measure (InterfaceField N)))
    (fun i => ∫ y : InternalField N, F (assemble N ((coarseRestriction N b, i), y)))
  rw [hdummy]
  simp only [probReal_univ, one_smul]
  exact (integral_prod (fun q : InterfaceField N × InternalField N =>
    F (assemble N ((coarseRestriction N b, q.1), q.2)))
    (IntegralKernel.integrable_continuous_fun _ (by
      exact F.continuous.comp ((continuous_assemble N).comp (by fun_prop))))).symm

/-- The first actual route projection, expressed as a function of original
boundary coordinates. -/
def firstProjected (N : ℕ) (β : ℝ) (F : C(FullField N, ℝ)) (b : FullField N) : ℝ :=
  project (volume : Measure (InternalField N)) (density N β) (density_pos N β)
    (splitObservable N F)
    ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : FineLink N => SU2)
      (fun l => Retained 4 l.val)) (fineRestriction N b))

/-- The composite route mark, including its intermediate generated weight. -/
def secondProjected (N : ℕ) (β : ℝ) (F : C(FullField N, ℝ)) (b : FullField N) : ℝ :=
  WilsonEliminationRoutes.action (route N β) (splitObservable N F) (coarseRestriction N b)

theorem secondProjected_eq_staged (N : ℕ) (β : ℝ) (F : C(FullField N, ℝ)) (b : FullField N) :
    secondProjected N β F b =
      project (volume : Measure (InterfaceField N)) (firstDensity N β)
        (marginal_pos volume (density N β) (density_pos N β))
        (project (volume : Measure (InternalField N)) (density N β) (density_pos N β)
          (splitObservable N F)) (coarseRestriction N b) := rfl

theorem continuous_firstProjected (N : ℕ) (β : ℝ) (F : C(FullField N, ℝ)) :
    Continuous (firstProjected N β F) := by
  apply (project (volume : Measure (InternalField N)) (density N β) (density_pos N β)
    (splitObservable N F)).continuous.comp
  change Continuous (fun b : FullField N =>
    ((fun l : CoarseLink N => b l.val.val), (fun l : InterfaceLink N => b l.val.val)))
  fun_prop

/-- The first boundary mark lifted without changing its values. -/
def firstLift (N : ℕ) (β : ℝ) (F : C(FullField N, ℝ)) : C(FullField N, ℝ) :=
  ⟨firstProjected N β F, continuous_firstProjected N β F⟩

theorem fineRestriction_assembleFine (N : ℕ) (p : FineField N × InternalField N) :
    fineRestriction N (assembleFine N p) = p.1 := by
  funext l
  simp [fineRestriction, assembleFine, MeasurableEquiv.piEquivPiSubtypeProd,
    Equiv.piEquivPiSubtypeProd_symm_apply, l.property]

theorem fineCoordinates_assemble (N : ℕ) (p : SplitField N) :
    fineCoordinates N (assemble N p) = p.1 := by
  unfold fineCoordinates assemble
  rw [fineRestriction_assembleFine]
  exact (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : FineLink N => SU2)
    (fun l => Retained 4 l.val)).apply_symm_apply p.1

theorem coarseRestriction_assemble (N : ℕ) (p : SplitField N) :
    coarseRestriction N (assemble N p) = p.1.1 := by
  funext l
  simp [coarseRestriction, assemble, assembleFine, assembleCoarse,
    MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply,
    l.property, l.val.property]

theorem split_firstLift (N : ℕ) (β : ℝ) (F : C(FullField N, ℝ)) :
    splitObservable N (firstLift N β F) =
      lift (project volume (density N β) (density_pos N β) (splitObservable N F)) := by
  ext p
  change project volume (density N β) (density_pos N β) (splitObservable N F)
    ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : FineLink N => SU2)
      (fun l => Retained 4 l.val))
      (fineRestriction N (assembleFine N (assembleCoarse N p.1, p.2)))) = _
  rw [fineRestriction_assembleFine]
  have h := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : FineLink N => SU2)
    (fun l => Retained 4 l.val)).apply_symm_apply p.1
  change (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : FineLink N => SU2)
    (fun l => Retained 4 l.val)) (assembleCoarse N p.1) = p.1 at h
  rw [h]
  rfl

/-- The coarse projection of the first projected mark equals the actual
two-stage projection of the original mark. This is the weighted tower law. -/
theorem secondProjected_firstLift (N : ℕ) (β : ℝ) (F : C(FullField N, ℝ)) :
    secondProjected N β (firstLift N β F) = secondProjected N β F := by
  funext b
  change project volume (firstDensity N β) (marginal_pos volume _ (density_pos N β))
    (project volume (density N β) (density_pos N β) (splitObservable N (firstLift N β F)))
    (coarseRestriction N b) = _
  rw [split_firstLift, project_lift]
  rfl

theorem firstProjected_eq_conditional (N : ℕ) (β : ℝ) (F : C(FullField N, ℝ))
    (b : FullField N) :
    firstProjected N β F b = WilsonConditionalProjection.project (volume : Measure SU2)
      (SU2BoundaryResponse.model (volumeIndex N) univ)
      (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β (retainedSet 2) F b := by
  have hassemble : assembleCoarse N
      ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : FineLink N => SU2)
        (fun l => Retained 4 l.val)) (fineRestriction N b)) = fineRestriction N b :=
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : FineLink N => SU2)
      (fun l => Retained 4 l.val)).symm_apply_apply _
  rw [WilsonConditionalProjection.project_eq_ratio]
  change (∫ i : InternalField N, fullDensity N β
    (assembleFine N (assembleCoarse N _, i)) * F (assembleFine N (assembleCoarse N _, i))) /
    (∫ i : InternalField N, fullDensity N β (assembleFine N (assembleCoarse N _, i))) =
    (∫ ω : FullField N, (fullDensity N β * F) (pin (retainedSet 2) b ω)) /
      (∫ ω : FullField N, fullDensity N β (pin (retainedSet 2) b ω))
  dsimp only
  rw [hassemble, integral_pin_fine, integral_pin_fine]
  rfl

theorem secondProjected_eq_conditional (N : ℕ) (β : ℝ) (F : C(FullField N, ℝ))
    (b : FullField N) :
    secondProjected N β F b = WilsonConditionalProjection.project (volume : Measure SU2)
      (SU2BoundaryResponse.model (volumeIndex N) univ)
      (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β (retainedSet 4) F b := by
  rw [WilsonConditionalProjection.project_eq_ratio]
  change project volume (marginal volume (density N β))
    (marginal_pos volume (density N β) (density_pos N β))
    (project volume (density N β) (density_pos N β) (splitObservable N F))
    (coarseRestriction N b) = _
  rw [WilsonProjectionComposition.project_staged]
  change (∫ q : InterfaceField N × InternalField N,
    (fullDensity N β * F) (assemble N ((coarseRestriction N b, q.1), q.2))
      ∂volume.prod volume) /
    (∫ q : InterfaceField N × InternalField N,
      fullDensity N β (assemble N ((coarseRestriction N b, q.1), q.2))
      ∂volume.prod volume) =
    (∫ ω : FullField N, (fullDensity N β * F) (pin (retainedSet 4) b ω)) /
      (∫ ω : FullField N, fullDensity N β (pin (retainedSet 4) b ω))
  rw [integral_pin_coarse, integral_pin_coarse]

/-- An original mark already ignoring the held dummy variables is transported
without an extra change to its value in the pinned Wilson expectation. -/
theorem secondProjected_eq_pinnedExpectation (N : ℕ) (β : ℝ)
    (F : C(FullField N, ℝ)) (b : FullField N)
    (hF : ∀ ω, F (pin (retainedSet 4) b ω) = F ω) :
    secondProjected N β F b = expectation
      (Measure.pi fun _ : AssemblyLink N ↦ (volume : Measure SU2))
      (SU2BoundaryResponse.boundaryDensity β univ (retainedSet 4) b) F := by
  rw [secondProjected_eq_conditional]
  exact WilsonConditionalProjection.project_eq_expectation_of_pinInvariant _ _ _ _ _ _ _ hF

/-- Conditional covariance at fixed coarse data is the actual GSLT route
remainder, with both original integrated groups still present. -/
theorem conditional_covariance_remainder (N : ℕ) (β : ℝ)
    (F G : C(FullField N, ℝ)) (b : FullField N)
    (hF : ∀ ω, F (pin (retainedSet 4) b ω) = F ω)
    (hG : ∀ ω, G (pin (retainedSet 4) b ω) = G ω) :
    covariance (Measure.pi fun _ : AssemblyLink N ↦ (volume : Measure SU2))
      (SU2BoundaryResponse.boundaryDensity β univ (retainedSet 4) b) F G =
      WilsonEliminationRoutes.remainder (route N β) (splitObservable N F) (splitObservable N G)
        (coarseRestriction N b) := by
  have hFG : ∀ ω, (F * G) (pin (retainedSet 4) b ω) = (F * G) ω := by
    intro ω
    simp only [ContinuousMap.mul_apply, hF, hG]
  rw [covariance, ← secondProjected_eq_pinnedExpectation N β (F * G) b hFG,
    ← secondProjected_eq_pinnedExpectation N β F b hF,
    ← secondProjected_eq_pinnedExpectation N β G b hG]
  rfl

/-- Exact stage-by-stage covariance transport for the concrete Haar assembly.
The first-stage fiber covariance is projected through the generated first
weight before being added to the second-stage covariance. -/
theorem route_remainder_staged (N : ℕ) (β : ℝ) (F G : C(FullField N, ℝ)) :
    WilsonEliminationRoutes.remainder (route N β) (splitObservable N F) (splitObservable N G) =
      fiberCovariance (volume : Measure (InterfaceField N)) (firstDensity N β)
        (marginal_pos volume (density N β) (density_pos N β))
        (project (volume : Measure (InternalField N)) (density N β) (density_pos N β)
          (splitObservable N F))
        (project (volume : Measure (InternalField N)) (density N β) (density_pos N β)
          (splitObservable N G)) +
      project (volume : Measure (InterfaceField N)) (firstDensity N β)
        (marginal_pos volume (density N β) (density_pos N β))
        (fiberCovariance (volume : Measure (InternalField N)) (density N β) (density_pos N β)
          (splitObservable N F) (splitObservable N G)) := by
  have hdirect : WilsonEliminationRoutes.remainder (route N β)
      (splitObservable N F) (splitObservable N G) =
      fiberCovariance ((volume : Measure (InterfaceField N)).prod
        (volume : Measure (InternalField N))) (reassociate (density N β))
        (fun p ↦ density_pos N β _) (reassociate (splitObservable N F))
        (reassociate (splitObservable N G)) := by
    ext b
    change project volume (marginal volume (density N β))
        (marginal_pos volume (density N β) (density_pos N β))
        (project volume (density N β) (density_pos N β)
          (splitObservable N F * splitObservable N G)) b -
        project volume (marginal volume (density N β))
          (marginal_pos volume (density N β) (density_pos N β))
          (project volume (density N β) (density_pos N β) (splitObservable N F)) b *
        project volume (marginal volume (density N β))
          (marginal_pos volume (density N β) (density_pos N β))
          (project volume (density N β) (density_pos N β) (splitObservable N G)) b = _
    rw [WilsonProjectionComposition.project_staged, WilsonProjectionComposition.project_staged,
      WilsonProjectionComposition.project_staged]
    rfl
  rw [hdirect, WilsonProjectionComposition.fiberCovariance_staged]
  rfl

/-- Conditional third cumulance at the coarse boundary is the actual
GSLT route's third remainder, against its original generated densities. -/
theorem conditional_thirdCumulant_remainder (N : ℕ) (β : ℝ)
    (F G H : C(FullField N, ℝ)) (b : FullField N)
    (hF : ∀ ω, F (pin (retainedSet 4) b ω) = F ω)
    (hG : ∀ ω, G (pin (retainedSet 4) b ω) = G ω)
    (hH : ∀ ω, H (pin (retainedSet 4) b ω) = H ω) :
    thirdCumulant (Measure.pi fun _ : AssemblyLink N ↦ (volume : Measure SU2))
      (SU2BoundaryResponse.boundaryDensity β univ (retainedSet 4) b) F G H =
      WilsonEliminationRoutes.thirdRemainder (route N β)
        (splitObservable N F) (splitObservable N G) (splitObservable N H)
        (coarseRestriction N b) := by
  have hp (A B : C(FullField N, ℝ))
      (hA : ∀ ω, A (pin (retainedSet 4) b ω) = A ω)
      (hB : ∀ ω, B (pin (retainedSet 4) b ω) = B ω) :
      ∀ ω, (A * B) (pin (retainedSet 4) b ω) = (A * B) ω := by
    intro ω
    simp only [ContinuousMap.mul_apply, hA, hB]
  rw [thirdCumulant, thirdMoment,
    ← secondProjected_eq_pinnedExpectation N β (F * G * H) b (hp (F * G) H (hp F G hF hG) hH),
    ← secondProjected_eq_pinnedExpectation N β (F * G) b (hp F G hF hG),
    ← secondProjected_eq_pinnedExpectation N β (F * H) b (hp F H hF hH),
    ← secondProjected_eq_pinnedExpectation N β (G * H) b (hp G H hG hH),
    ← secondProjected_eq_pinnedExpectation N β F b hF,
    ← secondProjected_eq_pinnedExpectation N β G b hG,
    ← secondProjected_eq_pinnedExpectation N β H b hH]
  rfl

/-- The full five-term tower for the actual two-stage Haar route. The
normalized second projection uses the generated first density throughout. -/
theorem route_thirdRemainder_staged (N : ℕ) (β : ℝ) (F G H : C(FullField N, ℝ)) :
    let P := project (volume : Measure (InternalField N)) (density N β) (density_pos N β)
    let Q := project (volume : Measure (InterfaceField N)) (firstDensity N β)
      (marginal_pos volume (density N β) (density_pos N β))
    let R := fiberCovariance (volume : Measure (InternalField N)) (density N β) (density_pos N β)
    let F₀ := splitObservable N F
    let G₀ := splitObservable N G
    let H₀ := splitObservable N H
    WilsonEliminationRoutes.thirdRemainder (route N β) F₀ G₀ H₀ =
      fiberThirdCumulant (volume : Measure (InterfaceField N)) (firstDensity N β)
        (marginal_pos volume (density N β) (density_pos N β)) (P F₀) (P G₀) (P H₀) +
      Q (fiberThirdCumulant (volume : Measure (InternalField N)) (density N β) (density_pos N β)
        F₀ G₀ H₀) +
      (Q (P F₀ * R G₀ H₀) - Q (P F₀) * Q (R G₀ H₀)) +
      (Q (P G₀ * R F₀ H₀) - Q (P G₀) * Q (R F₀ H₀)) +
      (Q (P H₀ * R F₀ G₀) - Q (P H₀) * Q (R F₀ G₀)) := by
  exact thirdMoment_comp
    (projectLinear (volume : Measure (InternalField N)) (density N β) (density_pos N β))
    (projectLinear (volume : Measure (InterfaceField N)) (firstDensity N β)
      (marginal_pos volume (density N β) (density_pos N β)))
    (splitObservable N F) (splitObservable N G) (splitObservable N H)

/-- Each mixed correction in the actual third-cumulant tower has a uniform
absolute bound. It uses the generated first density in the second route and
requires no coupling restriction or spatial separation. -/
theorem mixedCorrection_le (N : ℕ) (β : ℝ) (F G H : C(FullField N, ℝ))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B)
    (hG : ∀ ω, |G ω| ≤ B) (hH : ∀ ω, |H ω| ≤ B) (b : CoarseField N) :
    |WilsonEliminationRoutes.remainder (secondRoute N β)
      (WilsonEliminationRoutes.action (firstRoute N β) (splitObservable N F))
      (WilsonEliminationRoutes.remainder (firstRoute N β)
        (splitObservable N G) (splitObservable N H)) b| ≤ 4 * B ^ 3 := by
  have hp := WilsonEliminationRoutes.action_contract (firstRoute N β)
    (splitObservable N F) B (fun _ ↦ hF _)
  have hpair := fun y ↦ WilsonEliminationRoutes.abs_remainder_le (firstRoute N β)
    (splitObservable N G) (splitObservable N H) hB hB (fun _ ↦ hG _) (fun _ ↦ hH _) y
  exact (WilsonEliminationRoutes.abs_remainder_le (secondRoute N β) _ _
    hB (show 0 ≤ 2 * B * B by positivity) hp hpair b).trans_eq (by ring)

/-- The three mixed terms have total absolute cost at most `12 * B³`.
This is a pointwise budget; a separate spatial estimate is needed to bound
their individual tree-weighted sums across later rescaled stages. -/
theorem mixedCorrections_abs_sum_le (N : ℕ) (β : ℝ) (F G H : C(FullField N, ℝ))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B)
    (hG : ∀ ω, |G ω| ≤ B) (hH : ∀ ω, |H ω| ≤ B) (b : CoarseField N) :
    |WilsonEliminationRoutes.remainder (secondRoute N β)
      (WilsonEliminationRoutes.action (firstRoute N β) (splitObservable N F))
      (WilsonEliminationRoutes.remainder (firstRoute N β)
        (splitObservable N G) (splitObservable N H)) b| +
    |WilsonEliminationRoutes.remainder (secondRoute N β)
      (WilsonEliminationRoutes.action (firstRoute N β) (splitObservable N G))
      (WilsonEliminationRoutes.remainder (firstRoute N β)
        (splitObservable N F) (splitObservable N H)) b| +
    |WilsonEliminationRoutes.remainder (secondRoute N β)
      (WilsonEliminationRoutes.action (firstRoute N β) (splitObservable N H))
      (WilsonEliminationRoutes.remainder (firstRoute N β)
        (splitObservable N F) (splitObservable N G)) b| ≤ 12 * B ^ 3 := by
  linarith [mixedCorrection_le N β F G H hB hF hG hH b,
    mixedCorrection_le N β G F H hB hG hF hH b,
    mixedCorrection_le N β H F G hB hH hF hG b]

/-! ## Spatial contracts for both actual integration states -/

theorem firstResponse_pair_eq (N : ℕ) (β : ℝ)
    (F : AssemblyLink N → C(FullField N, ℝ)) (b : FullField N) (i j : AssemblyLink N) :
    (firstResponseState N β F).2.pair i j (fineCoordinates N b) =
      covariance (Measure.pi fun _ : AssemblyLink N ↦ (volume : Measure SU2))
        (SU2BoundaryResponse.boundaryDensity β univ (retainedSet 2) b)
        (WilsonConditionalProjection.pinnedMark (retainedSet 2) b (F i))
        (WilsonConditionalProjection.pinnedMark (retainedSet 2) b (F j)) := by
  change firstProjected N β (F i * F j) b -
    firstProjected N β (F i) b * firstProjected N β (F j) b = _
  simp_rw [firstProjected_eq_conditional]
  rfl

theorem secondResponse_pair_eq (N : ℕ) (β : ℝ)
    (F : AssemblyLink N → C(FullField N, ℝ)) (b : FullField N) (i j : AssemblyLink N) :
    (secondResponseState N β F).2.pair i j (coarseRestriction N b) =
      covariance (Measure.pi fun _ : AssemblyLink N ↦ (volume : Measure SU2))
        (SU2BoundaryResponse.boundaryDensity β univ (retainedSet 4) b)
        (WilsonConditionalProjection.pinnedMark (retainedSet 4) b (F i))
        (WilsonConditionalProjection.pinnedMark (retainedSet 4) b (F j)) := by
  change secondProjected N β (F i * F j) b -
    secondProjected N β (F i) b * secondProjected N β (F j) b = _
  simp_rw [secondProjected_eq_conditional]
  rfl

theorem firstResponse_triple_eq (N : ℕ) (β : ℝ)
    (F : AssemblyLink N → C(FullField N, ℝ)) (b : FullField N) (i j k : AssemblyLink N) :
    (firstResponseState N β F).2.triple i j k (fineCoordinates N b) =
      thirdCumulant (Measure.pi fun _ : AssemblyLink N ↦ (volume : Measure SU2))
        (SU2BoundaryResponse.boundaryDensity β univ (retainedSet 2) b)
        (WilsonConditionalProjection.pinnedMark (retainedSet 2) b (F i))
        (WilsonConditionalProjection.pinnedMark (retainedSet 2) b (F j))
        (WilsonConditionalProjection.pinnedMark (retainedSet 2) b (F k)) := by
  change firstProjected N β (F i * F j * F k) b -
    firstProjected N β (F i * F j) b * firstProjected N β (F k) b -
    firstProjected N β (F i * F k) b * firstProjected N β (F j) b -
    firstProjected N β (F j * F k) b * firstProjected N β (F i) b +
    2 * (firstProjected N β (F i) b * firstProjected N β (F j) b *
      firstProjected N β (F k) b) = _
  simp_rw [firstProjected_eq_conditional]
  rfl

theorem secondResponse_triple_eq (N : ℕ) (β : ℝ)
    (F : AssemblyLink N → C(FullField N, ℝ)) (b : FullField N) (i j k : AssemblyLink N) :
    (secondResponseState N β F).2.triple i j k (coarseRestriction N b) =
      thirdCumulant (Measure.pi fun _ : AssemblyLink N ↦ (volume : Measure SU2))
        (SU2BoundaryResponse.boundaryDensity β univ (retainedSet 4) b)
        (WilsonConditionalProjection.pinnedMark (retainedSet 4) b (F i))
        (WilsonConditionalProjection.pinnedMark (retainedSet 4) b (F j))
        (WilsonConditionalProjection.pinnedMark (retainedSet 4) b (F k)) := by
  change secondProjected N β (F i * F j * F k) b -
    secondProjected N β (F i * F j) b * secondProjected N β (F k) b -
    secondProjected N β (F i * F k) b * secondProjected N β (F j) b -
    secondProjected N β (F j * F k) b * secondProjected N β (F i) b +
    2 * (secondProjected N β (F i) b * secondProjected N β (F j) b *
      secondProjected N β (F k) b) = _
  simp_rw [secondProjected_eq_conditional]
  rfl

/-- Both concrete Haar integration states satisfy one quantitative contract.
The constants precede the spatial volume, local marks and every retained
boundary value. Pinning the marks preserves their original collars. -/
theorem uniform_responseContract {β B : ℝ} (hβ : 0 ≤ β)
    (hβ0 : β ≤ StrongCouplingCrossing.beta0 4) (hB : 0 ≤ B) :
    ∃ η > 0, ∃ C₂ ≥ 0, ∃ C₃ ≥ 0,
      ∀ (N : ℕ) (F : AssemblyLink N → C(FullField N, ℝ)),
        (∀ l, DependsOn (WilsonPatchGeometry.collar {l}) (F l)) →
        (∀ l ω, |F l ω| ≤ B) →
        WilsonEliminationRoutes.boundaryContract η B C₂ C₃ (firstResponseState N β F) ∧
        WilsonEliminationRoutes.boundaryContract η B C₂ C₃ (secondResponseState N β F) := by
  obtain ⟨η, hη, C₂, hC₂, C₃, hC₃, hc⟩ :=
    WilsonLocalResponse.uniform_collar_response_bounds (volume : Measure SU2)
      (1 : SU2) hβ hβ0 hB
  refine ⟨η, hη, C₂, hC₂, C₃, hC₃, ?_⟩
  intro N F hlocal hF
  have hb (s : ℕ) (b : FullField N) :=
    hc ((SU2BoundaryResponse.model (volumeIndex N) univ).pinned (retainedSet s) b)
      (WilsonLocalResponse.continuous_pinned _
        (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) (retainedSet s) b)
      (fun l ↦ WilsonConditionalProjection.pinnedMark (retainedSet s) b (F l))
      (fun l ↦ WilsonConditionalProjection.pinnedMark_local _ _ _ _ (hlocal l))
      (fun l _ ↦ hF l _)
  constructor
  · refine ⟨hη, hB, hC₂, hC₃, ?_, ?_, ?_⟩
    · intro l y
      exact WilsonEliminationRoutes.action_contract (firstRoute N β)
        (splitObservable N (F l)) B (fun _ ↦ hF l _) y
    · intro y
      have h := (hb 2 (assemble N (y, fun _ ↦ 1))).1
      simp_rw [← firstResponse_pair_eq] at h
      rwa [fineCoordinates_assemble] at h
    · intro y
      have h := (hb 2 (assemble N (y, fun _ ↦ 1))).2
      simp_rw [← firstResponse_triple_eq] at h
      rwa [fineCoordinates_assemble] at h
  · refine ⟨hη, hB, hC₂, hC₃, ?_, ?_, ?_⟩
    · intro l y
      exact WilsonEliminationRoutes.action_contract (route N β)
        (splitObservable N (F l)) B (fun _ ↦ hF l _) y
    · intro y
      have h := (hb 4 (assemble N ((y, fun _ ↦ 1), fun _ ↦ 1))).1
      simp_rw [← secondResponse_pair_eq] at h
      rwa [coarseRestriction_assemble] at h
    · intro y
      have h := (hb 4 (assemble N ((y, fun _ ↦ 1), fun _ ↦ 1))).2
      simp_rw [← secondResponse_triple_eq] at h
      rwa [coarseRestriction_assemble] at h

/-- OSLF reachability of the quantitative contract is witnessed by the two
actual integration constructors, with both target contracts proved. -/
theorem uniform_responseContract_reachable {β B : ℝ} (hβ : 0 ≤ β)
    (hβ0 : β ≤ StrongCouplingCrossing.beta0 4) (hB : 0 ≤ B) :
    ∃ η > 0, ∃ C₂ ≥ 0, ∃ C₃ ≥ 0,
      ∀ (N : ℕ) (F : AssemblyLink N → C(FullField N, ℝ)),
        (∀ l, DependsOn (WilsonPatchGeometry.collar {l}) (F l)) →
        (∀ l ω, |F l ω| ≤ B) →
        Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond
          (WilsonEliminationRoutes.haarTheory (AssemblyLink N))
          (WilsonEliminationRoutes.boundaryContract η B C₂ C₃) (initialResponseState N β F) ∧
        Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond
          (WilsonEliminationRoutes.haarTheory (AssemblyLink N))
          (WilsonEliminationRoutes.boundaryContract η B C₂ C₃) (firstResponseState N β F) := by
  obtain ⟨η, hη, C₂, hC₂, C₃, hC₃, hc⟩ := uniform_responseContract hβ hβ0 hB
  refine ⟨η, hη, C₂, hC₂, C₃, hC₃, ?_⟩
  intro N F hlocal hF
  obtain ⟨hfirst, hsecond⟩ := hc N F hlocal hF
  rw [WilsonEliminationRoutes.haarDiamond_contract_iff,
    WilsonEliminationRoutes.haarDiamond_contract_iff]
  exact ⟨⟨firstResponseState N β F, initialResponse_transition N β F, hfirst⟩,
    ⟨secondResponseState N β F, firstResponse_transition N β F, hsecond⟩⟩

/-- First-stage locality derived from the original Wilson plaquettes. -/
theorem firstProjected_locality (N : ℕ) (β : ℝ) (S : Finset (AssemblyLink N))
    (F : C(FullField N, ℝ)) (hF : DependsOn S F) :
    DependsOn (dependencyBoundary 2 S) (firstProjected N β F) := by
  intro b b' h
  rw [firstProjected_eq_conditional, firstProjected_eq_conditional]
  exact project_dependsOn (volume : Measure SU2) 1
    (SU2BoundaryResponse.model (volumeIndex N) univ)
    (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β 2 S F hF b b' h

/-- Second-stage locality for the actual composed map, despite the generated
interactions in the first marginal. -/
theorem secondProjected_locality (N : ℕ) (β : ℝ) (S : Finset (AssemblyLink N))
    (F : C(FullField N, ℝ)) (hF : DependsOn S F) :
    DependsOn (dependencyBoundary 4 S) (secondProjected N β F) := by
  intro b b' h
  rw [secondProjected_eq_conditional, secondProjected_eq_conditional]
  exact project_dependsOn (volume : Measure SU2) 1
    (SU2BoundaryResponse.model (volumeIndex N) univ)
    (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β 4 S F hF b b' h

/-- The support update at the second elimination is applied to the actually
projected first mark, not postulated for the generated density. -/
theorem secondProjected_staged_locality (N : ℕ) (β : ℝ) (S : Finset (AssemblyLink N))
    (F : C(FullField N, ℝ)) (hF : DependsOn S F) :
    DependsOn (supportSequence S 2) (secondProjected N β F) := by
  have h := secondProjected_locality N β (dependencyBoundary 2 S) (firstLift N β F)
    (firstProjected_locality N β S F hF)
  rw [secondProjected_firstLift] at h
  convert h using 1
  simp [supportSequence]

/-- For the actual two-step route, the derived support recurrence gives a
uniform collar in units of the coarse lattice spacing. -/
theorem secondProjected_support_radius (N : ℕ) (β : ℝ) (S : Finset (AssemblyLink N))
    (F : C(FullField N, ℝ)) (hF : DependsOn S F) (c : AssemblyLink N) (r : ℝ)
    (hS : ∀ l ∈ S, dist l c ≤ r) :
    DependsOn (supportSequence S 2) (secondProjected N β F) ∧
      ∀ l ∈ supportSequence S 2, dist l c / 4 ≤ r / 4 + 4 := by
  refine ⟨secondProjected_staged_locality N β S F hF, ?_⟩
  intro l hl
  simpa only [show (2 : ℝ)^2 = 4 by norm_num] using
    supportSequence_uniform_collar S c r hS 2 l hl

/-- The explicitly chosen Wilson marks depend on their four original links. -/
theorem plaquetteObservable_local (N : ℕ) (p : AssemblyPlaquette N) :
    DependsOn (StrongCouplingCrossing.support p) (plaquetteObservable N p) := by
  intro ω ω' h
  apply congrArg SU2BoundaryResponse.plaquetteEnergy
  funext i
  exact h _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)

#print axioms firstProjected_eq_conditional
#print axioms conditional_covariance_remainder
#print axioms route_remainder_staged
#print axioms conditional_thirdCumulant_remainder
#print axioms route_thirdRemainder_staged
#print axioms secondProjected_eq_conditional
#print axioms firstProjected_locality
#print axioms secondProjected_locality
#print axioms secondProjected_staged_locality
#print axioms secondProjected_support_radius
#print axioms plaquetteObservable_local
end Mettapedia.QuantumTheory.YangMills.SU2WilsonAssemblyLocality
