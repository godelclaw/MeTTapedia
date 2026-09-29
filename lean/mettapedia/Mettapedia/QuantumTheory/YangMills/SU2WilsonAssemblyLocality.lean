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
#print axioms secondProjected_eq_conditional
#print axioms firstProjected_locality
#print axioms secondProjected_locality
#print axioms secondProjected_staged_locality
#print axioms secondProjected_support_radius
#print axioms plaquetteObservable_local
end Mettapedia.QuantumTheory.YangMills.SU2WilsonAssemblyLocality
