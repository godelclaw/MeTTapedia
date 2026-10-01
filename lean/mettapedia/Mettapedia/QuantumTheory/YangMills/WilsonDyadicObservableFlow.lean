import Mettapedia.QuantumTheory.YangMills.SU2WilsonAssemblyLocality

/-!
# Observable locality along arbitrary dyadic conditional projections

Each operator is the actual normalized Wilson integral with its specified
retained coordinates. Iterating these continuous operators derives the
support recurrence for the resulting marks. For the SU(2) assembly, the
first two operators are identified with its staged elimination route,
including the generated intermediate density.
-/
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
open scoped Topology Classical
namespace Mettapedia.QuantumTheory.YangMills
namespace WilsonDyadicObservableFlow
open StrongCouplingCrossing InhomogeneousWilsonCrossing WilsonLocalResponse
open WilsonPinnedIntegral WilsonDyadicLocality WilsonDyadicProjection WilsonProductLocality

variable {E : Type*} [TopologicalSpace E] [CompactSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {d n : ℕ}

export WilsonPinnedIntegral (pinMap)

/-- The actual conditional integral as a continuous boundary mark, lifted to
the original coordinate space by ignoring unretained coordinates. -/
def projectMap (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held : Finset (Link d M.n)) (F : C(Link d M.n → E, ℝ)) : C(Link d M.n → E, ℝ) :=
  weightedProject ν₀ (realDensity M hφ β) (realDensity_pos M hφ β) held F

theorem projectMap_apply (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held : Finset (Link d M.n)) (F : C(Link d M.n → E, ℝ)) (b : Link d M.n → E) :
    projectMap ν₀ M hφ β held F b = WilsonConditionalProjection.project ν₀ M hφ β held F b := rfl

/-- Successive original-law conditional projections at doubled separator meshes. -/
def observableSequence (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (F : C(Link d M.n → E, ℝ)) : ℕ → C(Link d M.n → E, ℝ)
  | 0 => F
  | j + 1 => projectMap ν₀ M hφ β (retainedSet (2^(j+1)))
      (observableSequence ν₀ M hφ β F j)

/-- Any finite dyadic prefix is exactly the direct original-law conditional
integral at its final separator. This is not a change of lattice scale. -/
theorem observableSequence_eq_direct (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (F : C(Link d M.n → E, ℝ)) :
    ∀ j, observableSequence ν₀ M hφ β F (j + 1) =
      projectMap ν₀ M hφ β (retainedSet (2 ^ (j + 1))) F := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    change projectMap ν₀ M hφ β (retainedSet (2 ^ (j + 1 + 1)))
      (observableSequence ν₀ M hφ β F (j + 1)) = _
    rw [ih]
    exact weightedProject_nested_original ν₀ _ (realDensity_pos M hφ β)
      (dyadic_retained_nested j) F

/-- The older original-law sequence agrees with integration under the
successive generated densities, at every finite depth. -/
theorem observableSequence_eq_generated (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (F : C(Link d M.n → E, ℝ)) (j : ℕ) :
    observableSequence ν₀ M hφ β F j =
      markSequence ν₀ (realDensity M hφ β) (realDensity_pos M hφ β)
        (fun k ↦ retainedSet (2 ^ (k + 1))) F j := by
  cases j with
  | zero => rfl
  | succ j =>
    rw [observableSequence_eq_direct,
      markSequence_eq_direct ν₀ _ (realDensity_pos M hφ β) _ dyadic_retained_nested F j]
    rfl

/-- The support recurrence is proved for these explicitly defined integral
operators at every stage, with no support-growth hypothesis on a black box. -/
theorem observableSequence_locality (ν₀ : Measure E) [IsProbabilityMeasure ν₀] (base : E)
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (S : Finset (Link d M.n)) (F : C(Link d M.n → E, ℝ)) (hF : DependsOn S F) :
    ∀ j, DependsOn (supportSequence S j) (observableSequence ν₀ M hφ β F j) := by
  intro j
  induction j with
  | zero => exact hF
  | succ j ih =>
    intro b b' hb
    change projectMap ν₀ M hφ β (retainedSet (2^(j+1)))
      (observableSequence ν₀ M hφ β F j) b =
      projectMap ν₀ M hφ β (retainedSet (2^(j+1)))
        (observableSequence ν₀ M hφ β F j) b'
    rw [projectMap_apply, projectMap_apply]
    exact project_dependsOn ν₀ base M hφ β (2^(j+1)) (supportSequence S j)
      (observableSequence ν₀ M hφ β F j) ih b b' hb

/-- Each actual projected mark has an explicit dependency set contained in a
uniform collar in the successively rescaled metric. -/
theorem observableSequence_uniform_collar (ν₀ : Measure E) [IsProbabilityMeasure ν₀] (base : E)
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (S : Finset (Link d M.n)) (F : C(Link d M.n → E, ℝ)) (hF : DependsOn S F)
    (c : Link d M.n) (r : ℝ) (hS : ∀ l ∈ S, dist l c ≤ r) (j : ℕ) :
    DependsOn (supportSequence S j) (observableSequence ν₀ M hφ β F j) ∧
      ∀ l ∈ supportSequence S j, dist l c / (2 : ℝ)^j ≤ r / (2 : ℝ)^j + 4 :=
  ⟨observableSequence_locality ν₀ base M hφ β S F hF j,
    fun l hl => supportSequence_uniform_collar S c r hS j l hl⟩

end WilsonDyadicObservableFlow

namespace SU2WilsonAssemblyLocality
open SU2WilsonAssembly SU2WilsonBlockPilot WilsonDyadicObservableFlow WilsonDyadicProjection

/-- Repeated marginalization of one strong-coupling Wilson law preserves
the original-label second/third moment contract uniformly in elimination
depth. Exact direct integration avoids accumulating absolute stage budgets.
The metric and marks are still those of the original lattice. -/
theorem uniform_nestedResponseContract {β B : ℝ} (hβ : 0 ≤ β)
    (hβ0 : β ≤ StrongCouplingCrossing.beta0 4) (hB : 0 ≤ B) :
    ∃ η > 0, ∃ C₂ ≥ 0, ∃ C₃ ≥ 0,
      ∀ (M : InhomogeneousWilsonCrossing.Model 4 SU2)
        (hφ : ∀ p, Continuous (M.φ p))
        (held : ℕ → Finset (StrongCouplingCrossing.Link 4 M.n)),
        (∀ j, held (j + 1) ⊆ held j) →
        ∀ (F : StrongCouplingCrossing.Link 4 M.n →
          C(StrongCouplingCrossing.Link 4 M.n → SU2, ℝ)),
        (∀ l, WilsonLocalResponse.DependsOn (WilsonPatchGeometry.collar {l}) (F l)) →
        (∀ l ω, |F l ω| ≤ B) → ∀ j,
        WilsonEliminationRoutes.boundaryContract η B C₂ C₃
          (WilsonProjectionComposition.coordinateResponseState (volume : Measure SU2)
            (WilsonLocalResponse.realDensity M hφ β) (WilsonLocalResponse.realDensity_pos M hφ β)
            held F j) := by
  obtain ⟨η, hη, C₂, hC₂, C₃, hC₃, hc⟩ :=
    WilsonLocalResponse.uniform_collar_response_bounds (volume : Measure SU2) (1 : SU2)
      hβ hβ0 hB
  refine ⟨η, hη, C₂, hC₂, C₃, hC₃, ?_⟩
  intro M hφ held hnested F hlocal hF j
  refine ⟨hη, hB, hC₂, hC₃, ?_, ?_, ?_⟩
  · intro l b
    exact WilsonEliminationRoutes.action_contract
      (WilsonProjectionComposition.coordinateRoute (volume : Measure SU2)
        (WilsonLocalResponse.realDensity M hφ β) (WilsonLocalResponse.realDensity_pos M hφ β)
        held j) (F l) B (hF l) b
  · intro b
    cases j with
    | zero =>
      change WilsonBoundaryResponse.weightedResponseSeminorm η
        (fun i k ↦ (WilsonEliminationRoutes.ResponseData.initial F).pair i k b) ≤ C₂
      simp only [WilsonEliminationRoutes.ResponseData.pair_initial, ContinuousMap.zero_apply]
      change WilsonBoundaryResponse.weightedResponseSeminorm η 0 ≤ C₂
      simpa only [map_zero] using hC₂
    | succ j =>
      have h := hc (M.pinned (held j) b) (WilsonLocalResponse.continuous_pinned M hφ (held j) b)
        (fun l ↦ WilsonConditionalProjection.pinnedMark (held j) b (F l))
        (fun l ↦ WilsonConditionalProjection.pinnedMark_local _ _ _ _ (hlocal l))
        (fun l _ ↦ hF l _)
      convert h.1 using 1
      congr 1
      funext i k
      rw [WilsonProjectionComposition.coordinateResponseState_pair _ _ _ held hnested F j i k]
      rfl
  · intro b
    cases j with
    | zero =>
      change WilsonBoundaryResponse.weightedThirdSeminorm η
        (fun i k l ↦ (WilsonEliminationRoutes.ResponseData.initial F).triple i k l b) ≤ C₃
      simp only [WilsonEliminationRoutes.ResponseData.triple_initial, ContinuousMap.zero_apply]
      change WilsonBoundaryResponse.weightedThirdSeminorm η 0 ≤ C₃
      simpa only [map_zero] using hC₃
    | succ j =>
      have h := hc (M.pinned (held j) b) (WilsonLocalResponse.continuous_pinned M hφ (held j) b)
        (fun l ↦ WilsonConditionalProjection.pinnedMark (held j) b (F l))
        (fun l ↦ WilsonConditionalProjection.pinnedMark_local _ _ _ _ (hlocal l))
        (fun l _ ↦ hF l _)
      convert h.2 using 1
      congr 1
      funext i k l
      rw [WilsonProjectionComposition.coordinateResponseState_triple _ _ _ held hnested F j i k l]
      rfl

/-- The first generic dyadic operator is the assembly's actual first mark. -/
theorem observableSequence_one (N : ℕ) (β : ℝ) (F : C(FullField N, ℝ)) :
    observableSequence (volume : Measure SU2) (SU2BoundaryResponse.model (volumeIndex N) univ)
      (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β F 1 = firstLift N β F := by
  ext b
  change projectMap _ _ _ β (retainedSet (2^1)) F b = firstProjected N β F b
  rw [projectMap_apply, firstProjected_eq_conditional]
  rfl

/-- The second generic dyadic operator is the assembly's actual composed mark. -/
theorem observableSequence_two (N : ℕ) (β : ℝ) (F : C(FullField N, ℝ)) (b : FullField N) :
    observableSequence (volume : Measure SU2) (SU2BoundaryResponse.model (volumeIndex N) univ)
      (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β F 2 b = secondProjected N β F b := by
  change projectMap (volume : Measure SU2) (SU2BoundaryResponse.model (volumeIndex N) univ)
    (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β (retainedSet (2^2))
    (observableSequence (volume : Measure SU2) (SU2BoundaryResponse.model (volumeIndex N) univ)
      (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β F 1) b = _
  rw [observableSequence_one, projectMap_apply]
  change WilsonConditionalProjection.project (volume : Measure SU2)
    (SU2BoundaryResponse.model (volumeIndex N) univ)
    (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β (retainedSet 4)
    (firstLift N β F) b = _
  rw [← secondProjected_eq_conditional, secondProjected_firstLift]

#print axioms WilsonDyadicObservableFlow.observableSequence_uniform_collar
#print axioms observableSequence_one
#print axioms observableSequence_two
end SU2WilsonAssemblyLocality
end Mettapedia.QuantumTheory.YangMills
