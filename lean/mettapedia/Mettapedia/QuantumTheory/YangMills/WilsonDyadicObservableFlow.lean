import Mettapedia.QuantumTheory.YangMills.RGBootstrap
import Mettapedia.QuantumTheory.YangMills.SU2WilsonAssemblyLocality

/-!
# Exact observable transport and contracting SU(2) scale iteration

Original-lattice dyadic projections first derive a support recurrence and
agree with direct nested marginalization under the generated Wilson weights.

The scale-two construction changes the lattice itself. Starting at side
`2^j (n+3)`, each actual Haar step extracts the complete local interaction and
its vacuum constant. In the support-cardinality norm with weight `exp(8 |S|)`,
the radius contracts by `4 exp(-2)` inside `R <= 1/2`. The SU(2) Wilson family
enters this region at an explicit positive coupling threshold.

The complete fluctuation product gives a direct integral equal to the staged
density and every transported continuous observable. Partitions, gauge
invariance and nonzero coarse Wilson loops are preserved. The actual radii
instantiate the scalar RG bootstrap; the native OSLF forward predicate has a
concrete Haar successor with the proved gain. These function-norm estimates
do not assert higher derivative or spatial-diameter bounds.
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

namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo
open StrongCouplingCrossing WilsonBlockElimination WilsonConditionalProjection.PairedHaar
open WilsonDyadicGeometry SU2WilsonBlockPilot WilsonLocalResponse
open Mettapedia.GSLT.Ultrainfinite WilsonEliminationRoutes

namespace InteractionState

def iterate (n : ℕ) : (j : ℕ) → InteractionState (scaleIndex n j) → InteractionState n
  | 0, A => A
  | j + 1, A => iterate n j A.block

theorem norm_iterate_le (n : ℕ) : ∀ j (A : InteractionState (scaleIndex n j)),
    interactionNorm 8 (iterate n j A).terms ≤
      (4 * Real.exp (-2))^j * interactionNorm 8 A.terms := by
  intro j
  induction j with
  | zero =>
    intro A
    change interactionNorm 8 A.terms ≤ (4 * Real.exp (-2))^0 * interactionNorm 8 A.terms
    rw [pow_zero, one_mul]
  | succ j ih =>
    intro A
    calc
      _ ≤ (4 * Real.exp (-2))^j * interactionNorm 8 A.block.terms := ih A.block
      _ ≤ (4 * Real.exp (-2))^j * ((4 * Real.exp (-2)) * interactionNorm 8 A.terms) :=
        mul_le_mul_of_nonneg_left A.norm_block_le (by positivity)
      _ = _ := by rw [pow_succ]; ring


theorem spatial_norm_iterate_le {η : ℝ} (hη : 0 ≤ η) (n : ℕ) :
    ∀ j (A : InteractionState (scaleIndex n j)), spatialInteractionNorm 8 η A.terms ≤ 1/2 →
      spatialInteractionNorm 8 η (iterate n j A).terms ≤
        (4 * Real.exp (-2))^j * spatialInteractionNorm 8 η A.terms := by
  intro j
  induction j with
  | zero =>
    intro A hA
    change spatialInteractionNorm 8 η A.terms ≤ (4 * Real.exp (-2))^0 * spatialInteractionNorm 8 η A.terms
    rw [pow_zero, one_mul]
  | succ j ih =>
    intro A hA
    calc
      _ ≤ (4 * Real.exp (-2))^j * spatialInteractionNorm 8 η A.block.terms :=
        ih A.block (spatial_small_block hη A hA)
      _ ≤ (4 * Real.exp (-2))^j * ((4 * Real.exp (-2)) * spatialInteractionNorm 8 η A.terms) :=
        mul_le_mul_of_nonneg_left (spatial_norm_block_le hη A hA) (by positivity)
      _ = _ := by rw [pow_succ]; ring
/-- Every step is the conditional Haar integral for the previous generated law. -/
def route (n : ℕ) : (j : ℕ) → (A : InteractionState (scaleIndex n j)) →
    Route Step A.weightedState (iterate n j A).weightedState
  | 0, _A => .refl _
  | j + 1, A => .cons A.step (route n j A.block)

theorem expectation_iterate (n j : ℕ) (A : InteractionState (scaleIndex n j))
    (F : C(Link 4 (scaleIndex n j) → SU2, ℝ)) :
    expectation volume (iterate n j A).density (action (route n j A) F) =
      expectation volume A.density F := expectation_action (route n j A) F

theorem partition_iterate (n : ℕ) : ∀ j (A : InteractionState (scaleIndex n j)),
    (∫ U, (iterate n j A).density U) = ∫ U, A.density U := by
  intro j
  induction j with
  | zero => intro A; rfl
  | succ j ih =>
    intro A
    change (∫ U, (iterate n j (block (n := scaleIndex n j) A)).density U) = _
    rw [ih]
    have he := density_block (n := scaleIndex n j) A
    exact (congrArg (fun W : C(Link 4 (scaleIndex n j) → SU2, ℝ) ↦ ∫ U, W U) he).trans
      (PairedLinks.integral_blockedDensity volume (blockIndexEquiv 4 (scaleIndex n j)) A.density)

end InteractionState

/-- The input and every generated interaction are actual SU(2) Wilson/Haar
functions. Constants are fixed before the torus and number of scale changes. -/
theorem wilson_iteration_bound (n j : ℕ) (β : ℝ) (hβ : |β| ≤ iterationBeta) :
    interactionNorm 8 (InteractionState.iterate n j (wilsonState (scaleIndex n j) β hβ)).terms ≤
      (4 * Real.exp (-2))^j * (64 * |β| * Real.exp 32) :=
  (InteractionState.norm_iterate_le n j _).trans
    (mul_le_mul_of_nonneg_left (by simpa only [wilsonState, show (4 : ℝ)*8 = 32 by norm_num]
      using wilsonInteraction_norm_le (scaleIndex n j) β 8 (by norm_num)) (by positivity))

/-- Spatial control persists through every actual scale change. -/

theorem wilson_spatial_iteration_bound {η : ℝ} (hη : 0 ≤ η) (n j : ℕ) (β : ℝ)
    (hβ : |β| ≤ spatialIterationBeta η) :
    spatialInteractionNorm 8 η (InteractionState.iterate n j
      (wilsonState (scaleIndex n j) β (hβ.trans (spatialIterationBeta_le hη)))).terms ≤
      (4 * Real.exp (-2))^j * (64 * |β| * Real.exp (32+4*η)) := by
  apply (InteractionState.spatial_norm_iterate_le hη n j _
    (wilsonState_spatial_small hη _ β _ hβ)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [wilsonState, show (4 : ℝ)*8 = 32 by norm_num] using
    wilsonInteraction_spatial_norm_le (scaleIndex n j) β 8 η (by norm_num) hη

end Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo

namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo
open StrongCouplingCrossing WilsonBlockElimination WilsonDyadicGeometry SU2WilsonBlockPilot

/-- All fluctuation variables of a finite scale chain, without repeated integration. -/
def ScaleFiber (n : ℕ) : ℕ → Type
  | 0 => PUnit
  | j + 1 => ScaleFiber n j × Fluctuation (scaleIndex n j)

instance scaleFiberTopology (n : ℕ) : (j : ℕ) → TopologicalSpace (ScaleFiber n j)
  | 0 => inferInstanceAs (TopologicalSpace PUnit)
  | j + 1 => by
    letI := scaleFiberTopology n j
    exact inferInstanceAs (TopologicalSpace (ScaleFiber n j × Fluctuation (scaleIndex n j)))

instance scaleFiberMeasurable (n : ℕ) : (j : ℕ) → MeasurableSpace (ScaleFiber n j)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | j + 1 => by
    letI := scaleFiberMeasurable n j
    exact inferInstanceAs (MeasurableSpace (ScaleFiber n j × Fluctuation (scaleIndex n j)))

instance scaleFiberCompact (n : ℕ) : (j : ℕ) → CompactSpace (ScaleFiber n j)
  | 0 => inferInstanceAs (CompactSpace PUnit)
  | j + 1 => by
    let := scaleFiberCompact n j
    exact inferInstanceAs (CompactSpace (ScaleFiber n j × Fluctuation (scaleIndex n j)))

instance scaleFiberSecondCountable (n : ℕ) : (j : ℕ) → SecondCountableTopology (ScaleFiber n j)
  | 0 => inferInstanceAs (SecondCountableTopology PUnit)
  | j + 1 => by
    let := scaleFiberSecondCountable n j
    exact inferInstanceAs (SecondCountableTopology (ScaleFiber n j × Fluctuation (scaleIndex n j)))

instance scaleFiberBorel (n : ℕ) : (j : ℕ) → BorelSpace (ScaleFiber n j)
  | 0 => inferInstanceAs (BorelSpace PUnit)
  | j + 1 => by
    let := scaleFiberBorel n j
    exact inferInstanceAs (BorelSpace (ScaleFiber n j × Fluctuation (scaleIndex n j)))

def scaleFiberMeasure (n : ℕ) : (j : ℕ) → Measure (ScaleFiber n j)
  | 0 => Measure.dirac PUnit.unit
  | j + 1 => (scaleFiberMeasure n j).prod volume

instance scaleFiberProbability (n : ℕ) : (j : ℕ) → IsProbabilityMeasure (scaleFiberMeasure n j)
  | 0 => inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))
  | j + 1 => by
    let := scaleFiberProbability n j
    exact inferInstanceAs (IsProbabilityMeasure ((scaleFiberMeasure n j).prod (volume : Measure (Fluctuation (scaleIndex n j)))))

/-- Ordered reconstruction of the original fine configuration from the final
coarse links and all independent Haar fluctuations. -/
def scaleAssemble (n : ℕ) : (j : ℕ) → (Link 4 n → SU2) → ScaleFiber n j → (Link 4 (scaleIndex n j) → SU2)
  | 0, c, _ => c
  | j + 1, c, f => chart (scaleIndex n j) (scaleAssemble n j c f.1, f.2)

theorem continuous_scaleAssemble (n : ℕ) : ∀ j,
    Continuous (fun p : (Link 4 n → SU2) × ScaleFiber n j ↦ scaleAssemble n j p.1 p.2) := by
  intro j
  induction j with
  | zero => exact continuous_fst
  | succ j ih =>
    change Continuous (fun p : (Link 4 n → SU2) × (ScaleFiber n j × Fluctuation (scaleIndex n j)) ↦
      chart (scaleIndex n j) (scaleAssemble n j p.1 p.2.1, p.2.2))
    exact (PairedLinks.continuous_chart (blockIndexEquiv 4 (scaleIndex n j))).comp
      ((ih.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd)

/-- A single integral over the complete product of all scale fluctuations. -/
def directDensity (n j : ℕ) (W : C(Link 4 (scaleIndex n j) → SU2, ℝ)) : C(Link 4 n → SU2, ℝ) :=
  CompactTransferGap.ProductMeasure.partialIntegral (scaleFiberMeasure n j)
    (W.comp ⟨fun p ↦ scaleAssemble n j p.1 p.2, continuous_scaleAssemble n j⟩)

theorem directDensity_zero (n : ℕ) (W : C(Link 4 (scaleIndex n 0) → SU2, ℝ)) :
    directDensity n 0 W = W := by
  ext c
  change (∫ f : PUnit, W c ∂Measure.dirac PUnit.unit) = W c
  simp

theorem directDensity_succ (n j : ℕ) (W : C(Link 4 (scaleIndex n (j+1)) → SU2, ℝ)) :
    directDensity n (j+1) W = directDensity n j
      (PairedLinks.blockedDensity volume (blockIndexEquiv 4 (scaleIndex n j)) W) := by
  ext c
  change (∫ f : ScaleFiber n j × Fluctuation (scaleIndex n j),
    W (chart (scaleIndex n j) (scaleAssemble n j c f.1, f.2))
      ∂(scaleFiberMeasure n j).prod volume) = _
  have hc : Continuous (fun f : ScaleFiber n j × Fluctuation (scaleIndex n j) ↦
      W (chart (scaleIndex n j) (scaleAssemble n j c f.1, f.2))) := by
    exact W.continuous.comp ((PairedLinks.continuous_chart (blockIndexEquiv 4 (scaleIndex n j))).comp
      (((continuous_scaleAssemble n j).comp (continuous_const.prodMk continuous_fst)).prodMk continuous_snd))
  rw [integral_prod _ (CompactTransferGap.IntegralKernel.integrable_continuous_fun _ hc)]
  rfl

end Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo

namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo
open StrongCouplingCrossing WilsonBlockElimination WilsonDyadicGeometry SU2WilsonBlockPilot
open WilsonEliminationRoutes

def scaleAssembleMap (n j : ℕ) : C((Link 4 n → SU2) × ScaleFiber n j, Link 4 (scaleIndex n j) → SU2) :=
  ⟨fun p ↦ scaleAssemble n j p.1 p.2, continuous_scaleAssemble n j⟩

theorem directDensity_pos (n j : ℕ) (W : C(Link 4 (scaleIndex n j) → SU2, ℝ))
    (hW : ∀ U, 0 < W U) (c : Link 4 n → SU2) : 0 < directDensity n j W c :=
  marginal_pos (scaleFiberMeasure n j) (W.comp (scaleAssembleMap n j)) (fun _ ↦ hW _) c

def directProject (n j : ℕ) (W : C(Link 4 (scaleIndex n j) → SU2, ℝ))
    (hW : ∀ U, 0 < W U) (F : C(Link 4 (scaleIndex n j) → SU2, ℝ)) : C(Link 4 n → SU2, ℝ) :=
  project (scaleFiberMeasure n j) (W.comp (scaleAssembleMap n j)) (fun _ ↦ hW _)
    (F.comp (scaleAssembleMap n j))

theorem directProject_apply (n j : ℕ) (W : C(Link 4 (scaleIndex n j) → SU2, ℝ))
    (hW : ∀ U, 0 < W U) (F : C(Link 4 (scaleIndex n j) → SU2, ℝ)) (c : Link 4 n → SU2) :
    directProject n j W hW F c = directDensity n j (W * F) c / directDensity n j W c := rfl

namespace InteractionState

theorem density_iterate_direct (n : ℕ) : ∀ j (A : InteractionState (scaleIndex n j)),
    (iterate n j A).density = directDensity n j A.density := by
  intro j
  induction j with
  | zero => intro A; exact (directDensity_zero n A.density).symm
  | succ j ih =>
    intro A
    change (iterate n j (block (n := scaleIndex n j) A)).density = _
    rw [ih]
    have he := density_block (n := scaleIndex n j) A
    exact (congrArg (directDensity n j) he).trans (directDensity_succ n j A.density).symm

theorem density_mul_action_direct (n : ℕ) : ∀ j (A : InteractionState (scaleIndex n j))
    (F : C(Link 4 (scaleIndex n j) → SU2, ℝ)),
    directDensity n j (A.density * F) = (iterate n j A).density * action (route n j A) F := by
  intro j
  induction j with
  | zero => intro A F; exact directDensity_zero n (A.density * F)
  | succ j ih =>
    intro A F
    rw [directDensity_succ]
    have he : PairedLinks.blockedDensity volume (blockIndexEquiv 4 (scaleIndex n j))
        (A.density * F) = (block (n := scaleIndex n j) A).density * A.step.project F := by
      have hb := density_block (n := scaleIndex n j) A
      rw [hb]
      exact PairedLinks.blockedDensity_mul_project volume (blockIndexEquiv 4 (scaleIndex n j))
        A.density A.density_pos F
    rw [he]
    exact ih A.block (A.step.project F)

/-- The complete staged conditional observable is exactly one conditional
integral over all scale fluctuations under the original fine density. -/
theorem action_route_eq_direct (n j : ℕ) (A : InteractionState (scaleIndex n j))
    (F : C(Link 4 (scaleIndex n j) → SU2, ℝ)) :
    action (route n j A) F = directProject n j A.density A.density_pos F := by
  ext c
  rw [directProject_apply, density_mul_action_direct, ← density_iterate_direct]
  simp only [ContinuousMap.mul_apply]
  exact (mul_div_cancel_left₀ _ ((iterate n j A).density_pos c).ne').symm

end InteractionState

end Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo

namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo
open StrongCouplingCrossing WilsonBlockElimination WilsonConditionalProjection.PairedHaar
open WilsonDyadicGeometry SU2WilsonBlockPilot WilsonLocalResponse
open Mettapedia.GSLT.Ultrainfinite WilsonEliminationRoutes

namespace InteractionState

/-- Actual successive radii, padded by zero after the prescribed finite
chain ends. No extra lattice scale is asserted after that endpoint. -/
def radiusSequence (n : ℕ) : (j : ℕ) → InteractionState (scaleIndex n j) → ℕ → ℝ
  | 0, A, 0 => interactionNorm 8 A.terms
  | 0, _, _ + 1 => 0
  | _j + 1, A, 0 => interactionNorm 8 A.terms
  | j + 1, A, k + 1 => radiusSequence n j A.block k

theorem radiusSequence_zero (n j : ℕ) (A : InteractionState (scaleIndex n j)) :
    radiusSequence n j A 0 = interactionNorm 8 A.terms := by cases j <;> rfl

theorem radiusSequence_final (n : ℕ) : ∀ j (A : InteractionState (scaleIndex n j)),
    radiusSequence n j A j = interactionNorm 8 (iterate n j A).terms := by
  intro j
  induction j with
  | zero => intro A; rfl
  | succ j ih => intro A; exact ih A.block

theorem radiusSequence_nonneg (n : ℕ) : ∀ j (A : InteractionState (scaleIndex n j)) k,
    0 ≤ radiusSequence n j A k := by
  intro j
  induction j with
  | zero => intro A k; cases k <;> simp only [radiusSequence] <;> positivity
  | succ j ih =>
    intro A k
    cases k with
    | zero => change 0 ≤ interactionNorm 8 A.terms; positivity
    | succ k => exact ih A.block k

theorem radiusSequence_step (n : ℕ) : ∀ j (A : InteractionState (scaleIndex n j)),
    AffineRGStepBound (4 * Real.exp (-2)) 0 (radiusSequence n j A) := by
  intro j
  induction j with
  | zero =>
    intro A k
    cases k <;> simp only [radiusSequence, add_zero, mul_zero] <;> positivity
  | succ j ih =>
    intro A k
    cases k with
    | zero =>
      change radiusSequence n j A.block 0 ≤ (4 * Real.exp (-2)) * interactionNorm 8 A.terms + 0
      rw [radiusSequence_zero, add_zero]
      exact A.norm_block_le
    | succ k => exact ih A.block k

/-- The existing RG bootstrap is instantiated by the actual nonlinear
Haar-extracted interactions, with zero error and a strict explicit gain. -/
theorem radiusSequence_geometric (n j : ℕ) (A : InteractionState (scaleIndex n j)) (k : ℕ) :
    radiusSequence n j A k ≤ (4 * Real.exp (-2))^k * interactionNorm 8 A.terms := by
  have h := (radiusSequence_step n j A).bound_by_geometric_of_zero_error (by positivity) k
  simpa only [radiusSequence_zero] using h

end InteractionState

theorem nonlinearGain_contraction : IsRGContractionGain (4 * Real.exp (-2)) :=
  ⟨by positivity, exp_reserve_lt_one⟩

end Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo

namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo
open StrongCouplingCrossing WilsonBlockElimination WilsonDyadicGeometry SU2WilsonBlockPilot
open WilsonEliminationRoutes SU2BoundaryResponse

/-- Pullback along the successive ordered coarse-link product maps. -/
def scaleLift (n : ℕ) : (j : ℕ) → C(Link 4 n → SU2, ℝ) → C(Link 4 (scaleIndex n j) → SU2, ℝ)
  | 0, F => F
  | j + 1, F => (scaleLift n j F).comp (PairedLinks.blockMap (blockIndexEquiv 4 (scaleIndex n j)))

theorem scaleLift_assemble (n : ℕ) : ∀ j (F : C(Link 4 n → SU2, ℝ)) c f,
    scaleLift n j F (scaleAssemble n j c f) = F c := by
  intro j
  induction j with
  | zero => intro F c f; rfl
  | succ j ih =>
    intro F c f
    change scaleLift n j F (PairedLinks.block (blockIndexEquiv 4 (scaleIndex n j))
      (PairedLinks.chart (blockIndexEquiv 4 (scaleIndex n j)) (scaleAssemble n j c f.1, f.2))) = F c
    rw [PairedLinks.block_chart]
    exact ih F c f.1

theorem scaleLift_gauge (n : ℕ) : ∀ j (F : C(Link 4 n → SU2, ℝ)),
    (∀ (g : Site 4 n → SU2) U, F (gaugeAct g U) = F U) →
    ∀ (g : Site 4 (scaleIndex n j) → SU2) U,
      scaleLift n j F (gaugeAct g U) = scaleLift n j F U := by
  intro j
  induction j with
  | zero => intro F hF; exact hF
  | succ j ih =>
    intro F hF g U
    change scaleLift n j F (PairedLinks.block (blockIndexEquiv 4 (scaleIndex n j)) (gaugeAct g U)) =
      scaleLift n j F (PairedLinks.block (blockIndexEquiv 4 (scaleIndex n j)) U)
    dsimp only [scaleIndex] at g U ⊢
    rw [paired_block_eq, paired_block_eq, blockField_gaugeAct]
    exact ih F hF _ _

theorem directProject_scaleLift (n j : ℕ) (W : C(Link 4 (scaleIndex n j) → SU2, ℝ))
    (hW : ∀ U, 0 < W U) (F : C(Link 4 n → SU2, ℝ)) :
    directProject n j W hW (scaleLift n j F) = F := by
  ext c
  change (∫ f, W (scaleAssemble n j c f) * scaleLift n j F (scaleAssemble n j c f)
    ∂scaleFiberMeasure n j) / (∫ f, W (scaleAssemble n j c f) ∂scaleFiberMeasure n j) = F c
  simp_rw [scaleLift_assemble]
  rw [integral_mul_const]
  exact mul_div_cancel_left₀ _ (directDensity_pos n j W hW c).ne'

theorem action_scaleLift (n j : ℕ) (A : InteractionState (scaleIndex n j))
    (F : C(Link 4 n → SU2, ℝ)) :
    action (InteractionState.route n j A) (scaleLift n j F) = F := by
  rw [InteractionState.action_route_eq_direct, directProject_scaleLift]

/-- A gauge-invariant, nonzero Wilson loop survives every prescribed finite
number of blocking steps exactly. The contracting interaction sector is
compatible with nontrivial observables. -/
theorem retainedWilsonLoop_nonzero (n j : ℕ) (A : InteractionState (scaleIndex n j))
    (p : Plaquette 4 n) :
    action (InteractionState.route n j A) (scaleLift n j (plaquetteTrace p)) ≠ 0 := by
  rw [action_scaleLift]
  intro h
  have he := congrArg (fun F : C(Link 4 n → SU2, ℝ) ↦ F (fun _ ↦ 1)) h
  norm_num only [plaquetteTrace_one, ContinuousMap.zero_apply] at he

end Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo

namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo
open StrongCouplingCrossing WilsonBlockElimination WilsonConditionalProjection.PairedHaar
open WilsonDyadicGeometry SU2WilsonBlockPilot WilsonLocalResponse
open Mettapedia.GSLT.Ultrainfinite WilsonEliminationRoutes
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-- An analytic predicate on the existing weighted states. The response data
remain explicit; this predicate concerns the density's full interaction norm. -/
def interactionContract {ι : Type} (R : ℝ) (s : BoundaryState ι) : Prop :=
  ∃ (n : ℕ) (A : InteractionState n), A.weightedState = s.1 ∧ interactionNorm 8 A.terms ≤ R

/-- The forward native modality has an actual successor with the proved
strict norm gain. The transition itself contains no smallness assumption. -/
theorem haarDiamond_interactionContract {ι : Type} {n : ℕ}
    (A : InteractionState (doubleIndex n)) (D : ResponseData A.weightedState ι)
    {R : ℝ} (hR : interactionNorm 8 A.terms ≤ R) :
    gsltDiamond (haarTheory ι) (interactionContract ((4 * Real.exp (-2)) * R))
      ⟨A.weightedState, D⟩ := by
  apply (gsltDiamond_spec _ _ _).mpr
  refine ⟨_, HaarTransition.paired volume (blockIndexEquiv 4 n) A.density A.density_pos D, ?_⟩
  refine ⟨n, A.block, ?_, A.norm_block_le.trans (mul_le_mul_of_nonneg_left hR (by positivity))⟩
  exact coordinateState_congr volume _ _ _ _ A.density_block

end Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo

namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo
open WilsonConditionalProjection.PairedHaar WilsonDyadicGeometry

/-- The same explicit positive interval supplies both the established
crossing threshold and the input radius of every finite scale iteration. -/
theorem strong_coupling_iteration_bound {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ strongIterationBeta) :
    β ≤ StrongCouplingCrossing.beta0 4 ∧ ∀ n j,
      interactionNorm 8 (InteractionState.iterate n j
        (wilsonState (scaleIndex n j) β (abs_le_iterationBeta hβ hβ0))).terms ≤
          (4 * Real.exp (-2))^j * (64 * β * Real.exp 32) := by
  refine ⟨hβ0.trans (min_le_right _ _), ?_⟩
  intro n j
  simpa only [abs_of_nonneg hβ] using wilson_iteration_bound n j β (abs_le_iterationBeta hβ hβ0)


end Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo

namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo
open StrongCouplingCrossing WilsonBlockElimination WilsonDyadicGeometry SU2WilsonBlockPilot
open WilsonEliminationRoutes WilsonLocalResponse SU2BoundaryResponse

theorem integral_scaleLift (n : ℕ) : ∀ j (F : C(Link 4 n → SU2, ℝ)),
    (∫ U, scaleLift n j F U) = ∫ c, F c := by
  intro j
  induction j with
  | zero => intro F; rfl
  | succ j ih =>
    intro F
    have hm := measurePreserving_blockField (scaleIndex n j)
    have hi := integral_map_of_stronglyMeasurable (μ := (volume : Measure (FineConfig (scaleIndex n j))))
      hm.measurable (scaleLift n j F).continuous.stronglyMeasurable
    rw [hm.map_eq] at hi
    calc
      _ = ∫ U : FineConfig (scaleIndex n j), scaleLift n j F (blockField U) := by
        change (∫ U : FineConfig (scaleIndex n j), scaleLift n j F
          (PairedLinks.block (blockIndexEquiv 4 (scaleIndex n j)) U)) = _
        simp only [paired_block_eq]
      _ = _ := hi.symm.trans (ih F)

theorem integral_retainedWilsonLoop_zero (n j : ℕ) (p : Plaquette 4 n) :
    (∫ U, scaleLift n j (plaquetteTrace p) U) = 0 :=
  (integral_scaleLift n j _).trans (integral_plaquetteTrace_zero p)

/-- The actual full Wilson density, including its vacuum normalization,
is integrated directly or by any prescribed finite chain with the same result. -/
theorem wilson_density_iterate_direct (n j : ℕ) (β : ℝ) (hβ : |β| ≤ iterationBeta) :
    (InteractionState.iterate n j (wilsonState (scaleIndex n j) β hβ)).density =
      directDensity n j (realDensity (model (scaleIndex n j) univ)
        (model_continuous (scaleIndex n j) univ) β) := by
  rw [InteractionState.density_iterate_direct, wilsonState_density]

/-- Original Wilson expectations equal expectations under every generated
law, for every continuous mark, including arbitrary finite products. -/
theorem wilson_expectation_iterate (n j : ℕ) (β : ℝ) (hβ : |β| ≤ iterationBeta)
    (F : C(Link 4 (scaleIndex n j) → SU2, ℝ)) :
    expectation volume (InteractionState.iterate n j (wilsonState (scaleIndex n j) β hβ)).density
      (action (InteractionState.route n j (wilsonState (scaleIndex n j) β hβ)) F) =
      expectation volume (realDensity (model (scaleIndex n j) univ)
        (model_continuous (scaleIndex n j) univ) β) F := by
  have h := InteractionState.expectation_iterate n j (wilsonState (scaleIndex n j) β hβ) F
  simpa only [wilsonState_density] using h

end Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo
