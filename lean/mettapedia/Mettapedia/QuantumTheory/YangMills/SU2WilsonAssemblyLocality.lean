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

/-- A continuous function of the retained fine coordinates, lifted to the
original field. No extra conditional averaging occurs in this operation. -/
def fineLift (N : ℕ) (F : C(CoarseField N × InterfaceField N, ℝ)) :
    C(FullField N, ℝ) :=
  ⟨fun b ↦ F (fineCoordinates N b), F.continuous.comp (by
    change Continuous (fun b : FullField N ↦
      ((fun l : CoarseLink N ↦ b l.val.val), (fun l : InterfaceLink N ↦ b l.val.val)))
    fun_prop)⟩

theorem split_fineLift (N : ℕ) (F : C(CoarseField N × InterfaceField N, ℝ)) :
    splitObservable N (fineLift N F) = lift (I := InternalField N) F := by
  ext p
  exact congrArg F (fineCoordinates_assemble N p)

theorem secondProjected_fineLift (N : ℕ) (β : ℝ)
    (F : C(CoarseField N × InterfaceField N, ℝ)) (b : FullField N) :
    secondProjected N β (fineLift N F) b =
      WilsonEliminationRoutes.action (secondRoute N β) F (coarseRestriction N b) := by
  change project volume (firstDensity N β) (marginal_pos volume _ (density_pos N β))
    (project volume (density N β) (density_pos N β) (splitObservable N (fineLift N F)))
    (coarseRestriction N b) = _
  rw [split_fineLift, project_lift]
  rfl

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

theorem firstRemainder_eq_covariance (N : ℕ) (β : ℝ)
    (F G : C(FullField N, ℝ)) (b : FullField N) :
    WilsonEliminationRoutes.remainder (firstRoute N β)
      (splitObservable N F) (splitObservable N G) (fineCoordinates N b) =
      covariance (Measure.pi fun _ : AssemblyLink N ↦ (volume : Measure SU2))
        (SU2BoundaryResponse.boundaryDensity β univ (retainedSet 2) b)
        (WilsonConditionalProjection.pinnedMark (retainedSet 2) b F)
        (WilsonConditionalProjection.pinnedMark (retainedSet 2) b G) := by
  change firstProjected N β (F * G) b - firstProjected N β F b * firstProjected N β G b = _
  simp_rw [firstProjected_eq_conditional]
  rfl

theorem fineLift_firstAction (N : ℕ) (β : ℝ) (F : C(FullField N, ℝ)) :
    fineLift N (WilsonEliminationRoutes.action (firstRoute N β) (splitObservable N F)) =
      firstLift N β F := rfl

theorem fineLift_firstRemainder (N : ℕ) (β : ℝ) (F G : C(FullField N, ℝ)) :
    fineLift N (WilsonEliminationRoutes.remainder (firstRoute N β)
      (splitObservable N F) (splitObservable N G)) =
      firstLift N β (F * G) - firstLift N β F * firstLift N β G := rfl

/-- A covariance for the generated first density is exactly a covariance
under the original Wilson law with the coarse boundary pinned. The lifted
marks are pinned as well; they need not ignore the held coordinates. -/
theorem secondRemainder_eq_covariance (N : ℕ) (β : ℝ)
    (F G : C(CoarseField N × InterfaceField N, ℝ)) (b : FullField N) :
    WilsonEliminationRoutes.remainder (secondRoute N β) F G (coarseRestriction N b) =
      covariance (Measure.pi fun _ : AssemblyLink N ↦ (volume : Measure SU2))
        (SU2BoundaryResponse.boundaryDensity β univ (retainedSet 4) b)
        (WilsonConditionalProjection.pinnedMark (retainedSet 4) b (fineLift N F))
        (WilsonConditionalProjection.pinnedMark (retainedSet 4) b (fineLift N G)) := by
  change WilsonEliminationRoutes.action (secondRoute N β) (F * G) (coarseRestriction N b) -
    WilsonEliminationRoutes.action (secondRoute N β) F (coarseRestriction N b) *
      WilsonEliminationRoutes.action (secondRoute N β) G (coarseRestriction N b) = _
  rw [← secondProjected_fineLift, ← secondProjected_fineLift, ← secondProjected_fineLift]
  simp_rw [secondProjected_eq_conditional]
  rfl

theorem secondThirdRemainder_eq_cumulant (N : ℕ) (β : ℝ)
    (F G H : C(CoarseField N × InterfaceField N, ℝ)) (b : FullField N) :
    WilsonEliminationRoutes.thirdRemainder (secondRoute N β) F G H (coarseRestriction N b) =
      thirdCumulant (Measure.pi fun _ : AssemblyLink N ↦ (volume : Measure SU2))
        (SU2BoundaryResponse.boundaryDensity β univ (retainedSet 4) b)
        (WilsonConditionalProjection.pinnedMark (retainedSet 4) b (fineLift N F))
        (WilsonConditionalProjection.pinnedMark (retainedSet 4) b (fineLift N G))
        (WilsonConditionalProjection.pinnedMark (retainedSet 4) b (fineLift N H)) := by
  change WilsonEliminationRoutes.action (secondRoute N β) (F * G * H) (coarseRestriction N b) -
    WilsonEliminationRoutes.action (secondRoute N β) (F * G) (coarseRestriction N b) *
      WilsonEliminationRoutes.action (secondRoute N β) H (coarseRestriction N b) -
    WilsonEliminationRoutes.action (secondRoute N β) (F * H) (coarseRestriction N b) *
      WilsonEliminationRoutes.action (secondRoute N β) G (coarseRestriction N b) -
    WilsonEliminationRoutes.action (secondRoute N β) (G * H) (coarseRestriction N b) *
      WilsonEliminationRoutes.action (secondRoute N β) F (coarseRestriction N b) +
    2 * (WilsonEliminationRoutes.action (secondRoute N β) F (coarseRestriction N b) *
      WilsonEliminationRoutes.action (secondRoute N β) G (coarseRestriction N b) *
      WilsonEliminationRoutes.action (secondRoute N β) H (coarseRestriction N b)) = _
  simp_rw [← secondProjected_fineLift, secondProjected_eq_conditional]
  rfl

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

/-- The actual first projected collar mark stays within radius four, in
original lattice units. This holds at every coupling. -/
theorem firstLift_ball_locality (N : ℕ) (β : ℝ) (l : AssemblyLink N)
    (F : C(FullField N, ℝ)) (hF : DependsOn (WilsonPatchGeometry.collar {l}) F) :
    DependsOn (WilsonPatchGeometry.linkBall 4 l) (firstLift N β F) := by
  exact (firstProjected_locality N β _ F hF).mono (by
    simpa only [Nat.cast_ofNat, show (2 : ℝ) + 2 = 4 by norm_num] using
      dependencyBoundary_collar_subset_ball (n := volumeIndex N) (by decide : 0 < 2) l)

/-- The first fiber covariance has exact support in the union of the two
enlarged collars, including overlapping and coincident source links. -/
theorem firstRemainder_ball_locality (N : ℕ) (β : ℝ) (l m : AssemblyLink N)
    (F G : C(FullField N, ℝ))
    (hF : DependsOn (WilsonPatchGeometry.collar {l}) F)
    (hG : DependsOn (WilsonPatchGeometry.collar {m}) G) :
    DependsOn (WilsonPatchGeometry.linkBall 4 l ∪ WilsonPatchGeometry.linkBall 4 m)
      (fineLift N (WilsonEliminationRoutes.remainder (firstRoute N β)
        (splitObservable N F) (splitObservable N G))) := by
  rw [fineLift_firstRemainder]
  have hFG := firstProjected_locality N β
    (WilsonPatchGeometry.collar {l} ∪ WilsonPatchGeometry.collar {m}) (F * G)
    ((hF.mono subset_union_left).mul (hG.mono subset_union_right))
  have hprod : DependsOn
      (WilsonPatchGeometry.linkBall 4 l ∪ WilsonPatchGeometry.linkBall 4 m)
      (firstLift N β (F * G)) := hFG.mono (by
    simpa only [Nat.cast_ofNat, show (2 : ℝ) + 2 = 4 by norm_num] using
      dependencyBoundary_collars_subset_balls (n := volumeIndex N) (by decide : 0 < 2) l m)
  exact hprod.sub (((firstLift_ball_locality N β l F hF).mono subset_union_left).mul
    ((firstLift_ball_locality N β m G hG).mono subset_union_right))

/-- The mixed covariance in the actual two-step cumulant tower has spatial
tree decay. One estimate separates the inner pair; the other separates the
transported mean from that pair. The second law uses the generated density. -/
theorem mixedCorrection_clustering {β B : ℝ} (hβ : 0 ≤ β)
    (hβ0 : β ≤ StrongCouplingCrossing.beta0 4) (hB : 0 ≤ B) :
    ∃ κ > 0, ∃ A ≥ 0, ∀ (N : ℕ) (i j k : AssemblyLink N)
      (F G H : C(FullField N, ℝ)),
      DependsOn (WilsonPatchGeometry.collar {i}) F →
      DependsOn (WilsonPatchGeometry.collar {j}) G →
      DependsOn (WilsonPatchGeometry.collar {k}) H →
      (∀ ω, |F ω| ≤ B) → (∀ ω, |G ω| ≤ B) → (∀ ω, |H ω| ≤ B) →
      ∀ b : CoarseField N,
        |WilsonEliminationRoutes.remainder (secondRoute N β)
          (WilsonEliminationRoutes.action (firstRoute N β) (splitObservable N F))
          (WilsonEliminationRoutes.remainder (firstRoute N β)
            (splitObservable N G) (splitObservable N H)) b| ≤
          A * Real.exp (-(κ / 2) * WilsonBoundaryResponse.threeTreeLength i j k) := by
  obtain ⟨κ₁, hκ₁, hc₁⟩ := WilsonLocalResponse.covariance_collar_clustering
    (volume : Measure SU2) (1 : SU2) hβ hβ0
  obtain ⟨κ₂, hκ₂, hc₂⟩ := WilsonLocalResponse.covariance_ball_union_clustering
    (volume : Measure SU2) (1 : SU2) hβ hβ0
  let A₁ := 2 * B * WilsonLocalResponse.covarianceEnvelope B κ₁
  let A₂ := 6 * B ^ 3 * WilsonLocalResponse.ballResponseEnvelope 4 κ₂
  have hA₁ : 0 ≤ A₁ := by dsimp [A₁, WilsonLocalResponse.covarianceEnvelope]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp [A₂, WilsonLocalResponse.ballResponseEnvelope]; positivity
  refine ⟨min κ₁ κ₂, lt_min hκ₁ hκ₂, A₁ + A₂, add_nonneg hA₁ hA₂, ?_⟩
  intro N i j k F G H hFdep hGdep hHdep hF hG hH b
  have hp := WilsonEliminationRoutes.action_contract (firstRoute N β)
    (splitObservable N F) B (fun _ ↦ hF _)
  have hpair : ∀ y,
      |WilsonEliminationRoutes.remainder (firstRoute N β)
        (splitObservable N G) (splitObservable N H) y| ≤
        WilsonLocalResponse.covarianceEnvelope B κ₁ * Real.exp (-κ₁ * dist j k) := by
    intro y
    let b₀ := assemble N (y, fun _ ↦ 1)
    have h := hc₁ ((SU2BoundaryResponse.model (volumeIndex N) univ).pinned (retainedSet 2) b₀)
      (WilsonLocalResponse.continuous_pinned _
        (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) (retainedSet 2) b₀)
      j k (WilsonConditionalProjection.pinnedMark (retainedSet 2) b₀ G)
      (WilsonConditionalProjection.pinnedMark (retainedSet 2) b₀ H) B hB
      (WilsonConditionalProjection.pinnedMark_local _ _ _ _ hGdep)
      (WilsonConditionalProjection.pinnedMark_local _ _ _ _ hHdep)
      (fun _ ↦ hG _) (fun _ ↦ hH _)
    rw [← firstRemainder_eq_covariance] at h
    simpa only [b₀, fineCoordinates_assemble] using h
  have hinner := WilsonEliminationRoutes.abs_remainder_le (secondRoute N β) _ _ hB
    (show 0 ≤ WilsonLocalResponse.covarianceEnvelope B κ₁ * Real.exp (-κ₁ * dist j k) by
      unfold WilsonLocalResponse.covarianceEnvelope; positivity) hp hpair b
  have hinner' : |WilsonEliminationRoutes.remainder (secondRoute N β)
      (WilsonEliminationRoutes.action (firstRoute N β) (splitObservable N F))
      (WilsonEliminationRoutes.remainder (firstRoute N β)
        (splitObservable N G) (splitObservable N H)) b| ≤ A₁ * Real.exp (-κ₁ * dist j k) := by
    exact hinner.trans_eq (by dsimp only [A₁]; ring)
  let P := WilsonEliminationRoutes.action (firstRoute N β) (splitObservable N F)
  let R := WilsonEliminationRoutes.remainder (firstRoute N β)
    (splitObservable N G) (splitObservable N H)
  have hR : ∀ y, |R y| ≤ 2 * B * B := fun y ↦
    WilsonEliminationRoutes.abs_remainder_le (firstRoute N β) _ _ hB hB
      (fun _ ↦ hG _) (fun _ ↦ hH _) y
  let b₀ := assemble N ((b, fun _ ↦ 1), fun _ ↦ 1)
  have houter := hc₂ ((SU2BoundaryResponse.model (volumeIndex N) univ).pinned (retainedSet 4) b₀)
    (WilsonLocalResponse.continuous_pinned _
      (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) (retainedSet 4) b₀)
    4 (by norm_num) i j k
    (WilsonConditionalProjection.pinnedMark (retainedSet 4) b₀ (fineLift N P))
    (WilsonConditionalProjection.pinnedMark (retainedSet 4) b₀ (fineLift N R))
    B (2 * B * B) hB (by positivity)
    (WilsonConditionalProjection.pinnedMark_local _ _ _ _ (by
      rw [show fineLift N P = firstLift N β F from rfl]
      exact firstLift_ball_locality N β i F hFdep))
    (WilsonConditionalProjection.pinnedMark_local _ _ _ _
      (firstRemainder_ball_locality N β j k G H hGdep hHdep))
    (fun _ ↦ hp _) (fun _ ↦ hR _)
  rw [← secondRemainder_eq_covariance N β P R b₀] at houter
  have houter' : |WilsonEliminationRoutes.remainder (secondRoute N β) P R b| ≤
      A₂ * Real.exp (-κ₂ * min (dist i j) (dist i k)) := by
    have hb : coarseRestriction N b₀ = b := coarseRestriction_assemble N _
    rw [hb] at houter
    exact houter.trans_eq (by dsimp only [A₂]; ring)
  have hcombine (a ρ δ : ℝ) (ha : a ≤ A₁ + A₂) (hρ : min κ₁ κ₂ ≤ ρ)
      (hδ : 0 ≤ δ) (ht : WilsonBoundaryResponse.threeTreeLength i j k ≤ 2 * δ) :
      a * Real.exp (-ρ * δ) ≤ (A₁ + A₂) *
        Real.exp (-(min κ₁ κ₂ / 2) * WilsonBoundaryResponse.threeTreeLength i j k) := by
    apply mul_le_mul ha _ (Real.exp_pos _).le (add_nonneg hA₁ hA₂)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ) hδ,
      mul_nonneg (le_min hκ₁.le hκ₂.le) (sub_nonneg.mpr ht)]
  rcases WilsonBoundaryResponse.threeTreeLength_pair_cut i j k with h | h
  · exact hinner'.trans (hcombine A₁ κ₁ _ (by linarith) (min_le_left _ _) dist_nonneg h)
  · exact houter'.trans (hcombine A₂ κ₂ _ (by linarith) (min_le_right _ _)
      (le_min dist_nonneg dist_nonneg) h)

/-- All three mixed arrays in `ResponseData.Contract.transport` have one
volume-uniform tree-weighted budget for the actual Haar assembly. -/
theorem uniform_mixedCorrection_bounds {β B : ℝ} (hβ : 0 ≤ β)
    (hβ0 : β ≤ StrongCouplingCrossing.beta0 4) (hB : 0 ≤ B) :
    ∃ η > 0, ∃ C ≥ 0, ∀ (N : ℕ) (F : AssemblyLink N → C(FullField N, ℝ)),
      (∀ l, DependsOn (WilsonPatchGeometry.collar {l}) (F l)) →
      (∀ l ω, |F l ω| ≤ B) → ∀ y : CoarseField N,
      let D := (firstResponseState N β F).2
      WilsonBoundaryResponse.weightedThirdSeminorm η
        (fun i j k ↦ WilsonEliminationRoutes.remainder (secondRoute N β)
          (D.first i) (D.pair j k) y) ≤ C ∧
      WilsonBoundaryResponse.weightedThirdSeminorm η
        (fun i j k ↦ WilsonEliminationRoutes.remainder (secondRoute N β)
          (D.first j) (D.pair i k) y) ≤ C ∧
      WilsonBoundaryResponse.weightedThirdSeminorm η
        (fun i j k ↦ WilsonEliminationRoutes.remainder (secondRoute N β)
          (D.first k) (D.pair i j) y) ≤ C := by
  obtain ⟨κ, hκ, A, hA, hc⟩ := mixedCorrection_clustering hβ hβ0 hB
  have hV : 0 ≤ StrongCouplingCrossing.exponentialVolumeBound 4 (κ / 8) := by
    unfold StrongCouplingCrossing.exponentialVolumeBound; positivity
  refine ⟨κ / 4, by positivity,
    A * (StrongCouplingCrossing.exponentialVolumeBound 4 (κ / 8)) ^ 2, by positivity, ?_⟩
  intro N F hlocal hF y
  have hbound (H : AssemblyLink N → AssemblyLink N → AssemblyLink N → ℝ)
      (hH : ∀ i j k, |H i j k| ≤
        A * Real.exp (-(κ / 2) * WilsonBoundaryResponse.threeTreeLength i j k)) :
      WilsonBoundaryResponse.weightedThirdSeminorm (κ / 4) H ≤
        A * (StrongCouplingCrossing.exponentialVolumeBound 4 (κ / 8)) ^ 2 := by
    apply WilsonBoundaryResponse.weightedThirdSeminorm_le_of_envelope
      (κ / 4) (κ / 2) (by linarith) _ hA hV hH
    intro i
    simpa only [show (κ / 2 - κ / 4) / 2 = κ / 8 by ring] using
      StrongCouplingCrossing.sum_exp_dist_le (by decide) (by positivity : 0 < κ / 8) i
  have hcut (i j k : AssemblyLink N) := hc N i j k (F i) (F j) (F k)
    (hlocal i) (hlocal j) (hlocal k) (hF i) (hF j) (hF k) y
  refine ⟨hbound _ hcut, hbound _ ?_, hbound _ ?_⟩
  · intro i j k
    exact (hcut j i k).trans_eq (by rw [WilsonBoundaryResponse.threeTreeLength_swap j i k])
  · intro i j k
    exact (hcut k i j).trans_eq (by rw [WilsonBoundaryResponse.threeTreeLength_rotate k i j])

/-- The new conditional second and third moments of the transported means
also satisfy uniform budgets under the explicitly generated first density. -/
theorem uniform_transported_response_bounds {β B : ℝ} (hβ : 0 ≤ β)
    (hβ0 : β ≤ StrongCouplingCrossing.beta0 4) (hB : 0 ≤ B) :
    ∃ η > 0, ∃ C₂ ≥ 0, ∃ C₃ ≥ 0,
      ∀ (N : ℕ) (F : AssemblyLink N → C(FullField N, ℝ)),
        (∀ l, DependsOn (WilsonPatchGeometry.collar {l}) (F l)) →
        (∀ l ω, |F l ω| ≤ B) → ∀ y : CoarseField N,
        let D := (firstResponseState N β F).2
        WilsonBoundaryResponse.weightedResponseSeminorm η
          (fun i j ↦ WilsonEliminationRoutes.remainder (secondRoute N β)
            (D.first i) (D.first j) y) ≤ C₂ ∧
        WilsonBoundaryResponse.weightedThirdSeminorm η
          (fun i j k ↦ WilsonEliminationRoutes.thirdRemainder (secondRoute N β)
            (D.first i) (D.first j) (D.first k) y) ≤ C₃ := by
  obtain ⟨η, hη, C₂, hC₂, C₃, hC₃, hc⟩ :=
    WilsonLocalResponse.uniform_ball_response_bounds (volume : Measure SU2) (1 : SU2)
      hβ hβ0 hB (by norm_num : (0 : ℝ) ≤ 4)
  refine ⟨η, hη, C₂, hC₂, C₃, hC₃, ?_⟩
  intro N F hlocal hF y
  let b := assemble N ((y, fun _ ↦ 1), fun _ ↦ 1)
  let P := fun l ↦ WilsonEliminationRoutes.action (firstRoute N β) (splitObservable N (F l))
  have hp (l : AssemblyLink N) := WilsonEliminationRoutes.action_contract (firstRoute N β)
    (splitObservable N (F l)) B (fun _ ↦ hF l _)
  have h := hc ((SU2BoundaryResponse.model (volumeIndex N) univ).pinned (retainedSet 4) b)
    (WilsonLocalResponse.continuous_pinned _
      (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) (retainedSet 4) b)
    (fun l ↦ WilsonConditionalProjection.pinnedMark (retainedSet 4) b (fineLift N (P l)))
    (fun l ↦ WilsonConditionalProjection.pinnedMark_local _ _ _ _ (by
      rw [show fineLift N (P l) = firstLift N β (F l) from rfl]
      exact firstLift_ball_locality N β l (F l) (hlocal l)))
    (fun l _ ↦ hp l _)
  have hb : coarseRestriction N b = y := coarseRestriction_assemble N _
  constructor
  · convert h.1 using 1
    congr 1
    funext i j
    exact ((secondRemainder_eq_covariance N β (P i) (P j) b).symm.trans
      (congrArg (WilsonEliminationRoutes.remainder (secondRoute N β) (P i) (P j)) hb)).symm
  · convert h.2 using 1
    congr 1
    funext i j k
    exact ((secondThirdRemainder_eq_cumulant N β (P i) (P j) (P k) b).symm.trans
      (congrArg (WilsonEliminationRoutes.thirdRemainder (secondRoute N β) (P i) (P j) (P k)) hb)).symm

/-- The quantitative transport theorem instantiated with proved spatial
estimates for both Haar steps, including all three mixed covariance arrays.
Every rate and budget is chosen before the volume, marks and boundary data. -/
theorem uniform_composed_responseContract {β B : ℝ} (hβ : 0 ≤ β)
    (hβ0 : β ≤ StrongCouplingCrossing.beta0 4) (hB : 0 ≤ B) :
    ∃ η > 0, ∃ C₂ ≥ 0, ∃ C₃ ≥ 0, ∃ D₂ ≥ 0, ∃ D₃ ≥ 0, ∃ E ≥ 0,
      ∀ (N : ℕ) (F : AssemblyLink N → C(FullField N, ℝ)),
        (∀ l, DependsOn (WilsonPatchGeometry.collar {l}) (F l)) →
        (∀ l ω, |F l ω| ≤ B) →
        WilsonEliminationRoutes.boundaryContract η B C₂ C₃ (firstResponseState N β F) ∧
        WilsonEliminationRoutes.boundaryContract η B (C₂ + D₂) (C₃ + D₃ + 3 * E)
          (secondResponseState N β F) := by
  obtain ⟨η₀, hη₀, C₂, hC₂, C₃, hC₃, hfirst⟩ := uniform_responseContract hβ hβ0 hB
  obtain ⟨η₁, hη₁, D₂, hD₂, D₃, hD₃, hnew⟩ := uniform_transported_response_bounds hβ hβ0 hB
  obtain ⟨η₂, hη₂, E, hE, hmix⟩ := uniform_mixedCorrection_bounds hβ hβ0 hB
  let η := min η₀ (min η₁ η₂)
  have hη : 0 < η := lt_min hη₀ (lt_min hη₁ hη₂)
  have hη₀' : η ≤ η₀ := min_le_left _ _
  have hη₁' : η ≤ η₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hη₂' : η ≤ η₂ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η, hη, C₂, hC₂, C₃, hC₃, D₂, hD₂, D₃, hD₃, E, hE, ?_⟩
  intro N F hlocal hF
  have hD := (hfirst N F hlocal hF).1.weaken_rate hη hη₀'
  refine ⟨hD, ?_⟩
  have hnext := hD.transport (secondRoute N β) (firstResponseState N β F).2
    hD₂ hD₃ hE hE hE
    (fun y ↦ (WilsonBoundaryResponse.weightedResponseSeminorm_mono_rate hη₁' _).trans
      (hnew N F hlocal hF y).1)
    (fun y ↦ (WilsonBoundaryResponse.weightedThirdSeminorm_mono_rate hη₁' _).trans
      (hnew N F hlocal hF y).2)
    (fun y ↦ (WilsonBoundaryResponse.weightedThirdSeminorm_mono_rate hη₂' _).trans
      (hmix N F hlocal hF y).1)
    (fun y ↦ (WilsonBoundaryResponse.weightedThirdSeminorm_mono_rate hη₂' _).trans
      (hmix N F hlocal hF y).2.1)
    (fun y ↦ (WilsonBoundaryResponse.weightedThirdSeminorm_mono_rate hη₂' _).trans
      (hmix N F hlocal hF y).2.2)
  rw [show C₃ + D₃ + E + E + E = C₃ + D₃ + 3 * E by ring] at hnext
  exact hnext

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

/-! ## Spatial covariance inside an actual scale-two Haar fiber -/

namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo
open StrongCouplingCrossing WilsonBlockElimination WilsonBlockElimination.PairedLinks
open WilsonConditionalProjection.PairedHaar WilsonDyadicGeometry SU2WilsonBlockPilot
open WilsonLocalResponse SU2BoundaryResponse Mettapedia.Combinatorics.PolymerGas

/-- The full Wilson action at fixed coarse products, regrouped by its actual
independent fluctuation support. No plaquette or induced dependence is removed. -/
def conditionalWilsonInteraction (n : ℕ) (β : ℝ) (c : CoarseConfig n) :
    Finset (FluctuationLink n) → C(FluctuationLink n → SU2, ℝ) :=
  regroupInteraction fluctuationPlaquetteSupport (fun p : Plaquette 4 (doubleIndex n) =>
    fluctuationMark (blockIndexEquiv 4 n) c ((-β) • plaquetteTrace p))

theorem conditionalWilsonInteraction_local (n : ℕ) (β : ℝ) (c : CoarseConfig n)
    (S : Finset (FluctuationLink n)) : DependsOn S (conditionalWilsonInteraction n β c S) := by
  apply regroupInteraction_local
  intro p
  apply fluctuationMark_local
  intro U V h
  exact congrArg (fun t : ℝ => -β*t) (plaquetteTrace_local p U V h)

theorem conditionalWilsonInteraction_empty (n : ℕ) (β : ℝ) (c : CoarseConfig n) :
    conditionalWilsonInteraction n β c ∅ = 0 := by
  apply sum_eq_zero
  intro p hp
  have he : fluctuationPlaquetteSupport p = ∅ := by
    simpa only [mem_filter, mem_univ, true_and] using hp
  exact ((fluctuationPlaquetteSupport_nonempty p).ne_empty he).elim

theorem conditionalWilsonInteraction_spatial_norm_le (n : ℕ) (β a η : ℝ)
    (ha : 0 ≤ a) (hη : 0 ≤ η) (c : CoarseConfig n) :
    spatialInteractionNorm a η (conditionalWilsonInteraction n β c) ≤
      128 * |β| * Real.exp (4*a+12*η) := by
  rw [mul_comm 4 a, mul_comm 12 η]
  apply spatialInteractionNorm_regroup_le (s := 4) (D := 128) (t := 12)
    fluctuationPlaquetteSupport
    (fun p => fluctuationMark (blockIndexEquiv 4 n) c ((-β) • plaquetteTrace p))
    ha hη (abs_nonneg β) card_fluctuationPlaquetteSupport_le
  · intro p
    have hc : ((fluctuationPlaquetteSupport p).card : ℝ) ≤ 4 := by
      exact_mod_cast card_fluctuationPlaquetteSupport_le p
    have ht := treeLength_le_card_mul_diam (fluctuationPlaquetteSupport p)
    have hd := diam_fluctuationPlaquetteSupport_le p
    have hn := polymerDiam_nonneg (fluctuationPlaquetteSupport p)
    have hn' : (0 : ℝ) ≤ (fluctuationPlaquetteSupport p).card := by positivity
    nlinarith
  · intro i
    have h := card_incident_fluctuationPlaquetteSupport_le n i
    convert h using 1
    congr 1
    exact Finset.filter_congr_decidable _ _ _
  · intro p
    apply (norm_fluctuationMark_le (blockIndexEquiv 4 n) c _).trans
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
    exact (mul_le_mul_of_nonneg_left (norm_plaquetteTrace_le p) (abs_nonneg β)).trans_eq (mul_one _)

/-- Rate and coupling threshold precede volume and every retained field. -/
def conditionalCovarianceBeta (η : ℝ) : ℝ := 1 / (256 * Real.exp (32+12*η))

theorem conditionalCovarianceBeta_pos (η : ℝ) : 0 < conditionalCovarianceBeta η := by
  unfold conditionalCovarianceBeta
  positivity

theorem conditionalWilsonInteraction_small {η β : ℝ} (hη : 0 ≤ η)
    (hβ : |β| ≤ conditionalCovarianceBeta η) (n : ℕ) (c : CoarseConfig n) :
    spatialInteractionNorm 8 η (conditionalWilsonInteraction n β c) ≤ 1/2 := by
  have hp : 0 < 256 * Real.exp (32+12*η) := by positivity
  have hh := (le_div_iff₀ hp).mp hβ
  apply (conditionalWilsonInteraction_spatial_norm_le n β 8 η (by norm_num) hη c).trans
  norm_num only at *
  nlinarith

theorem fluctuation_wilson_density (n : ℕ) (β : ℝ) (c : CoarseConfig n) :
    fluctuationMark (blockIndexEquiv 4 n) c (fineDensity n β) =
      Real.exp (-β * Fintype.card (Plaquette 4 (doubleIndex n))) •
        interactionDensity (conditionalWilsonInteraction n β c) := by
  ext f
  change fineDensity n β (fluctuationChart (blockIndexEquiv 4 n) c f) = _
  rw [fineDensity, realDensity_eq_wilsonInteraction, sum_wilsonInteraction]
  have hs : (∑ S, conditionalWilsonInteraction n β c S) f =
      ∑ p : Plaquette 4 (doubleIndex n), -β * plaquetteTrace p (fluctuationChart (blockIndexEquiv 4 n) c f) := by
    unfold conditionalWilsonInteraction
    rw [sum_regroupInteraction]
    simp only [ContinuousMap.sum_apply, fluctuationMark, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, ContinuousMap.smul_apply, smul_eq_mul]
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
    interactionDensity, ContinuousMap.coe_mk, Real.exp_add]
  congr 1
  apply congrArg Real.exp
  simpa only [ContinuousMap.sum_apply] using hs.symm

/-- The covariance discarded by the actual one-step normalized Haar projection. -/
def conditionalCovariance (n : ℕ) (β : ℝ) (F G : C(FineConfig n, ℝ)) : C(CoarseConfig n, ℝ) :=
  projected n β (F*G) - projected n β F * projected n β G

theorem conditionalCovariance_spatial_le {η β : ℝ} (hη : 0 ≤ η)
    (hβ : |β| ≤ conditionalCovarianceBeta η) (n : ℕ)
    (S T : Finset (Link 4 (doubleIndex n))) (hS : S.Nonempty) (hT : T.Nonempty)
    (F G : C(FineConfig n, ℝ)) (hF : DependsOn S F) (hG : DependsOn T G)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hFB : ∀ U, |F U| ≤ B) (hGC : ∀ U, |G U| ≤ C) (c : CoarseConfig n) :
    |conditionalCovariance n β F G c| ≤
      3*B*C*Real.exp (3*S.card+3*T.card) * Real.exp (-η*(polymerDist S T-2)) := by
  have he := covariance_fluctuationMark (volume : Measure SU2) (blockIndexEquiv 4 n)
    (fineDensity n β) (fineDensity_pos n β) F G c
  change _ = conditionalCovariance n β F G c at he
  rw [← he, fluctuation_wilson_density,
    covariance_smul_density _ _ _ _ (Real.exp_pos _).ne']
  have hc := covariance_interactionDensity_le (conditionalWilsonInteraction n β c) volume hη
    (conditionalWilsonInteraction_local n β c) (conditionalWilsonInteraction_empty n β c)
    (conditionalWilsonInteraction_small hη hβ n c)
    (fluctuationSupport (blockIndexEquiv 4 n) S) (fluctuationSupport (blockIndexEquiv 4 n) T)
    (fluctuationSupport_nonempty _ hS) (fluctuationMark (blockIndexEquiv 4 n) c F)
    (fluctuationMark (blockIndexEquiv 4 n) c G)
    (fluctuationMark_local _ _ S F hF) (fluctuationMark_local _ _ T G hG)
    B C (fun f => hFB _) (fun f => hGC _)
  apply hc.trans
  have hd := dist_fluctuationSupport_ge (blockIndexEquiv 4 n)
    (r := 1) dist_fluctuationRepresentative_le S T hS hT
  have hcardS : ((fluctuationSupport (blockIndexEquiv 4 n) S).card : ℝ) ≤ S.card := by
    exact_mod_cast card_fluctuationSupport_le (blockIndexEquiv 4 n) S
  have hcardT : ((fluctuationSupport (blockIndexEquiv 4 n) T).card : ℝ) ≤ T.card := by
    exact_mod_cast card_fluctuationSupport_le (blockIndexEquiv 4 n) T
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    linarith
  · apply Real.exp_le_exp.mpr
    nlinarith
  · positivity
  · positivity

/-- Averaging uses the generated coarse Wilson density, with its exact
normalization. The same rate and constant remain uniform in volume. -/
theorem expectation_conditionalCovariance_spatial_le {η β : ℝ} (hη : 0 ≤ η)
    (hβ : |β| ≤ conditionalCovarianceBeta η) (n : ℕ)
    (S T : Finset (Link 4 (doubleIndex n))) (hS : S.Nonempty) (hT : T.Nonempty)
    (F G : C(FineConfig n, ℝ)) (hF : DependsOn S F) (hG : DependsOn T G)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hFB : ∀ U, |F U| ≤ B) (hGC : ∀ U, |G U| ≤ C) :
    |expectation volume (coarseDensity n β) (conditionalCovariance n β F G)| ≤
      3*B*C*Real.exp (3*S.card+3*T.card) * Real.exp (-η*(polymerDist S T-2)) :=
  abs_expectation_le volume _ _ (coarseDensity_pos n β)
    (conditionalCovariance_spatial_le hη hβ n S T hS hT F G hF hG hB hC hFB hGC)

def twoConditionalWilsonInteraction (n : ℕ) (β : ℝ) (c : CoarseConfig n) :
    Finset (TwoFluctuationLink n) → C(TwoFluctuationLink n → SU2, ℝ) :=
  regroupInteraction twoFluctuationPlaquetteSupport (fun p : Plaquette 4 (doubleIndex (doubleIndex n)) =>
    twoFluctuationMark (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) c ((-β) • plaquetteTrace p))

theorem twoConditionalWilsonInteraction_local (n : ℕ) (β : ℝ) (c : CoarseConfig n)
    (S : Finset (TwoFluctuationLink n)) : DependsOn S (twoConditionalWilsonInteraction n β c S) := by
  apply regroupInteraction_local
  intro p
  apply twoFluctuationMark_local
  intro U V h
  exact congrArg (fun t : ℝ => -β*t) (plaquetteTrace_local p U V h)

theorem twoConditionalWilsonInteraction_empty (n : ℕ) (β : ℝ) (c : CoarseConfig n) :
    twoConditionalWilsonInteraction n β c ∅ = 0 := by
  apply sum_eq_zero
  intro p hp
  have he : twoFluctuationPlaquetteSupport p = ∅ := by
    simpa only [mem_filter, mem_univ, true_and] using hp
  exact ((twoFluctuationPlaquetteSupport_nonempty p).ne_empty he).elim

theorem twoConditionalWilsonInteraction_spatial_norm_le (n : ℕ) (β a η : ℝ)
    (ha : 0 ≤ a) (hη : 0 ≤ η) (c : CoarseConfig n) :
    spatialInteractionNorm a η (twoConditionalWilsonInteraction n β c) ≤
      128 * |β| * Real.exp (8*a+56*η) := by
  rw [mul_comm 8 a, mul_comm 56 η]
  apply spatialInteractionNorm_regroup_le (s := 8) (D := 128) (t := 56)
    twoFluctuationPlaquetteSupport
    (fun p => twoFluctuationMark (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) c ((-β) • plaquetteTrace p))
    ha hη (abs_nonneg β) card_twoFluctuationPlaquetteSupport_le
  · intro p
    have hc : ((twoFluctuationPlaquetteSupport p).card : ℝ) ≤ 8 := by
      exact_mod_cast card_twoFluctuationPlaquetteSupport_le p
    have ht := treeLength_le_card_mul_diam (twoFluctuationPlaquetteSupport p)
    have hd := diam_twoFluctuationPlaquetteSupport_le p
    have hn := polymerDiam_nonneg (twoFluctuationPlaquetteSupport p)
    have hn' : (0 : ℝ) ≤ (twoFluctuationPlaquetteSupport p).card := by positivity
    nlinarith
  · intro i
    have h := card_incident_twoFluctuationPlaquetteSupport_le n i
    convert h using 1
  · intro p
    apply (norm_twoFluctuationMark_le (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) c _).trans
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
    exact (mul_le_mul_of_nonneg_left (norm_plaquetteTrace_le p) (abs_nonneg β)).trans_eq (mul_one _)

/-- Two actual scale changes, uniformly over the original volume and the final
retained field.  This is a fixed two-step threshold, not an all-depth claim. -/
def twoConditionalCovarianceBeta (η : ℝ) : ℝ := 1 / (256 * Real.exp (64+56*η))

theorem twoConditionalCovarianceBeta_pos (η : ℝ) : 0 < twoConditionalCovarianceBeta η := by
  unfold twoConditionalCovarianceBeta
  positivity

theorem twoConditionalCovarianceBeta_le {η : ℝ} (hη : 0 ≤ η) :
    twoConditionalCovarianceBeta η ≤ conditionalCovarianceBeta η := by
  apply one_div_le_one_div_of_le (by positivity : 0 < 256 * Real.exp (32+12*η))
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  linarith

theorem twoConditionalWilsonInteraction_small {η β : ℝ} (hη : 0 ≤ η)
    (hβ : |β| ≤ twoConditionalCovarianceBeta η) (n : ℕ) (c : CoarseConfig n) :
    spatialInteractionNorm 8 η (twoConditionalWilsonInteraction n β c) ≤ 1/2 := by
  have hp : 0 < 256 * Real.exp (64+56*η) := by positivity
  have hh := (le_div_iff₀ hp).mp hβ
  apply (twoConditionalWilsonInteraction_spatial_norm_le n β 8 η (by norm_num) hη c).trans
  norm_num only at *
  nlinarith

theorem twoFluctuation_wilson_density (n : ℕ) (β : ℝ) (c : CoarseConfig n) :
    twoFluctuationMark (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) c (fineDensity (doubleIndex n) β) =
      Real.exp (-β * Fintype.card (Plaquette 4 (doubleIndex (doubleIndex n)))) •
        interactionDensity (twoConditionalWilsonInteraction n β c) := by
  ext f
  change fineDensity (doubleIndex n) β (twoFluctuationChart (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) c f) = _
  rw [fineDensity, realDensity_eq_wilsonInteraction, sum_wilsonInteraction]
  have hs : (∑ S, twoConditionalWilsonInteraction n β c S) f =
      ∑ p : Plaquette 4 (doubleIndex (doubleIndex n)), -β * plaquetteTrace p (twoFluctuationChart (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) c f) := by
    unfold twoConditionalWilsonInteraction
    rw [sum_regroupInteraction]
    simp only [ContinuousMap.sum_apply, twoFluctuationMark, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, ContinuousMap.smul_apply, smul_eq_mul]
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
    interactionDensity, ContinuousMap.coe_mk, Real.exp_add]
  congr 1
  apply congrArg Real.exp
  simpa only [ContinuousMap.sum_apply] using hs.symm

/-- Covariance of original local marks conditioned on two successive retained
products.  Both eliminated fibers remain in the actual Wilson density. -/
theorem covariance_twoFluctuationMark_spatial_le {η β : ℝ} (hη : 0 ≤ η)
    (hβ : |β| ≤ twoConditionalCovarianceBeta η) (n : ℕ)
    (S T : Finset (Link 4 (doubleIndex (doubleIndex n)))) (hS : S.Nonempty) (hT : T.Nonempty)
    (F G : C(FineConfig (doubleIndex n), ℝ)) (hF : DependsOn S F) (hG : DependsOn T G)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hFB : ∀ U, |F U| ≤ B) (hGC : ∀ U, |G U| ≤ C) (c : CoarseConfig n) :
    |covariance volume
      (twoFluctuationMark (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) c (fineDensity (doubleIndex n) β))
      (twoFluctuationMark (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) c F)
      (twoFluctuationMark (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) c G)| ≤
      3*B*C*Real.exp (6*S.card+6*T.card) * Real.exp (-η*(polymerDist S T-6)) := by
  rw [twoFluctuation_wilson_density, covariance_smul_density _ _ _ _ (Real.exp_pos _).ne']
  have hc := covariance_interactionDensity_le (twoConditionalWilsonInteraction n β c) volume hη
    (twoConditionalWilsonInteraction_local n β c) (twoConditionalWilsonInteraction_empty n β c)
    (twoConditionalWilsonInteraction_small hη hβ n c)
    (twoFluctuationSupport (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) S)
    (twoFluctuationSupport (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) T)
    (twoFluctuationSupport_nonempty _ _ hS)
    (twoFluctuationMark (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) c F)
    (twoFluctuationMark (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) c G)
    (twoFluctuationMark_local _ _ _ S F hF) (twoFluctuationMark_local _ _ _ T G hG)
    B C (fun f => hFB _) (fun f => hGC _)
  apply hc.trans
  have hd := dist_twoFluctuationSupport_ge_six S T hS hT
  have hcardS : ((twoFluctuationSupport (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) S).card : ℝ) ≤ 2*S.card := by
    exact_mod_cast card_twoFluctuationSupport_le (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) S
  have hcardT : ((twoFluctuationSupport (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) T).card : ℝ) ≤ 2*T.card := by
    exact_mod_cast card_twoFluctuationSupport_le (blockIndexEquiv 4 (doubleIndex n)) (blockIndexEquiv 4 n) T
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    linarith
  · apply Real.exp_le_exp.mpr
    nlinarith
  · positivity
  · positivity

end Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo
