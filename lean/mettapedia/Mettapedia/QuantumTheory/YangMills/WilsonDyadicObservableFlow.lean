import Mettapedia.QuantumTheory.YangMills.RGBootstrap
import Mettapedia.QuantumTheory.YangMills.SU2WilsonAssemblyLocality

/-!
# Exact observable transport and contracting SU(2) scale iteration

Original-lattice dyadic projections first derive a support recurrence and
agree with direct nested marginalization under the generated Wilson weights.

The scale-two construction changes the lattice itself. Starting at side
`2^j (n+3)`, each actual Haar step extracts the complete local interaction and
its vacuum constant. In the support-cardinality norm with weight `exp(8 |S|)`,
the radius contracts by `4 exp(-2)` inside `R <= 1/2`. The same estimate holds
with a spatial tree-length weight. The SU(2) Wilson family enters this region
at an explicit positive coupling threshold, with a rate fixed before volume
and elimination depth.

The complete fluctuation product gives a direct integral equal to the staged
density and every transported continuous observable. Partitions, gauge
invariance and nonzero coarse Wilson loops are preserved. The actual radii
instantiate the scalar RG bootstrap; the native OSLF forward predicate has a
concrete Haar successor with the proved gain. The spatial radius supplies an
exact polymer representation and clustering for the generated law and fine
pullbacks of coarse-product observables. For arbitrary continuous marks,
the conditional-covariance remainder is retained explicitly. These
function-norm estimates do not assert higher derivative bounds.

A stopping-scale certificate identifies the actual integrated Wilson density
and fixes its spatial rate and physical scale before cutoff and volume.
Anchored local decompositions of transported marks and the discarded
conditional covariance give an explicit physical clustering bound. The
weak-coupling entrance, observable budgets and continuum construction remain
separate obligations.
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
/-- The same spatial radius is valid at every finite scale. -/
theorem spatial_small_iterate {η : ℝ} (hη : 0 ≤ η) (n : ℕ) :
    ∀ j (A : InteractionState (scaleIndex n j)), spatialInteractionNorm 8 η A.terms ≤ 1/2 →
      spatialInteractionNorm 8 η (iterate n j A).terms ≤ 1/2 := by
  intro j
  induction j with
  | zero => intro A hA; exact hA
  | succ j ih => intro A hA; exact ih A.block (A.spatial_small_block hη hA)


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
open WilsonLocalResponse SU2BoundaryResponse

/-- Original plaquette energy centered under the original Wilson law. The
scalar z records any cutoff-dependent normalization rather than hiding it
inside a uniform observable bound. Centering the trace score and the energy
gives the same mark, since they differ by one. -/
def wilsonPlaquetteMark (n : ℕ) (β z : ℝ) (p : Plaquette 4 n) : C(Link 4 n → SU2, ℝ) :=
  z • centered volume (realDensity (model n univ) (model_continuous n univ) β) (plaquetteTrace p)

theorem wilsonPlaquetteMark_local (n : ℕ) (β z : ℝ) (p : Plaquette 4 n) :
    DependsOn (support p) (wilsonPlaquetteMark n β z p) := by
  intro U V h
  simp only [wilsonPlaquetteMark, centered, ContinuousMap.smul_apply,
    ContinuousMap.sub_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
  rw [plaquetteTrace_local p U V h]

theorem wilsonPlaquetteMark_gauge (n : ℕ) (β z : ℝ) (p : Plaquette 4 n)
    (g : Site 4 n → SU2) (U : Link 4 n → SU2) :
    wilsonPlaquetteMark n β z p (gaugeAct g U) = wilsonPlaquetteMark n β z p U := by
  simp only [wilsonPlaquetteMark, centered, ContinuousMap.smul_apply,
    ContinuousMap.sub_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
  rw [plaquetteTrace_gauge]

theorem expectation_wilsonPlaquetteMark (n : ℕ) (β z : ℝ) (p : Plaquette 4 n) :
    expectation volume (realDensity (model n univ) (model_continuous n univ) β)
      (wilsonPlaquetteMark n β z p) = 0 := by
  change expectationLinear volume _ (z • centered volume _ (plaquetteTrace p)) = 0
  rw [map_smul]
  change z * expectation volume _ (centered volume _ (plaquetteTrace p)) = 0
  rw [WilsonBlockElimination.expectation_centered volume
    (realDensity (model n univ) (model_continuous n univ) β) (plaquetteTrace p)
    (realDensity_pos _ _ _), mul_zero]

theorem abs_wilsonPlaquetteMark_le (n : ℕ) (β z : ℝ) (p : Plaquette 4 n)
    (U : Link 4 n → SU2) : |wilsonPlaquetteMark n β z p U| ≤ 2*|z| := by
  have h := abs_centered_le volume (realDensity (model n univ) (model_continuous n univ) β)
    (plaquetteTrace p) (realDensity_pos _ _ _) (B := 1) (abs_plaquetteTrace_le p) U
  change |z * centered volume _ (plaquetteTrace p) U| ≤ _
  rw [abs_mul]
  nlinarith [abs_nonneg z]

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

/-- Direct integration preserves the full finite-volume partition. -/
theorem integral_directDensity (n : ℕ) : ∀ j (W : C(Link 4 (scaleIndex n j) → SU2, ℝ)),
    (∫ c, directDensity n j W c) = ∫ U, W U := by
  intro j
  induction j with
  | zero => intro W; rw [directDensity_zero]; rfl
  | succ j ih =>
    intro W
    rw [directDensity_succ, ih]
    exact PairedLinks.integral_blockedDensity volume (blockIndexEquiv 4 (scaleIndex n j)) W

theorem directDensity_mul_directProject (n j : ℕ)
    (W : C(Link 4 (scaleIndex n j) → SU2, ℝ)) (hW : ∀ U, 0 < W U)
    (F : C(Link 4 (scaleIndex n j) → SU2, ℝ)) :
    directDensity n j W * directProject n j W hW F = directDensity n j (W * F) := by
  ext c
  rw [ContinuousMap.mul_apply, directProject_apply]
  exact mul_div_cancel₀ _ (directDensity_pos n j W hW c).ne'

theorem expectation_directProject (n j : ℕ)
    (W : C(Link 4 (scaleIndex n j) → SU2, ℝ)) (hW : ∀ U, 0 < W U)
    (F : C(Link 4 (scaleIndex n j) → SU2, ℝ)) :
    expectation volume (directDensity n j W) (directProject n j W hW F) = expectation volume W F := by
  unfold expectation
  change (∫ c, (directDensity n j W * directProject n j W hW F) c) /
    (∫ c, directDensity n j W c) = (∫ U, (W * F) U) / (∫ U, W U)
  rw [directDensity_mul_directProject, integral_directDensity, integral_directDensity]

/-- Staged transport under the generated density agrees with one integral
at every coupling; no interaction smallness is used. -/
theorem directProject_succ (n j : ℕ)
    (W : C(Link 4 (scaleIndex n (j+1)) → SU2, ℝ)) (hW : ∀ U, 0 < W U)
    (F : C(Link 4 (scaleIndex n (j+1)) → SU2, ℝ)) :
    directProject n (j+1) W hW F = directProject n j
      (PairedLinks.blockedDensity volume (blockIndexEquiv 4 (scaleIndex n j)) W)
      (PairedLinks.blockedDensity_pos volume (blockIndexEquiv 4 (scaleIndex n j)) W hW)
      (PairedLinks.blockedProject volume (blockIndexEquiv 4 (scaleIndex n j)) W hW F) := by
  ext c
  rw [directProject_apply, directProject_apply, directDensity_succ, directDensity_succ]
  apply congrArg (fun z : ℝ => z / directDensity n j
    (PairedLinks.blockedDensity volume (blockIndexEquiv 4 (scaleIndex n j)) W) c)
  exact congrArg (fun H => directDensity n j H c)
    (PairedLinks.blockedDensity_mul_project volume (blockIndexEquiv 4 (scaleIndex n j)) W hW F)

def directProjectLinear (n j : ℕ) (W : C(Link 4 (scaleIndex n j) → SU2, ℝ))
    (hW : ∀ U, 0 < W U) : C(Link 4 (scaleIndex n j) → SU2, ℝ) →ₗ[ℝ] C(Link 4 n → SU2, ℝ) where
  toFun := directProject n j W hW
  map_add' F G := by
    ext c
    exact expectation_add _ ((W.comp (scaleAssembleMap n j)).curry c)
      ((F.comp (scaleAssembleMap n j)).curry c) ((G.comp (scaleAssembleMap n j)).curry c)
  map_smul' a F := by
    ext c
    exact expectation_const_mul _ ((W.comp (scaleAssembleMap n j)).curry c)
      ((F.comp (scaleAssembleMap n j)).curry c) a

theorem abs_directProject_le (n j : ℕ) (W : C(Link 4 (scaleIndex n j) → SU2, ℝ))
    (hW : ∀ U, 0 < W U) (F : C(Link 4 (scaleIndex n j) → SU2, ℝ))
    {B : ℝ} (hF : ∀ U, |F U| ≤ B) : ∀ c, |directProject n j W hW F c| ≤ B :=
  abs_project_le _ _ _ _ (fun _ => hF _)

def directStep (n j : ℕ) (W : C(Link 4 (scaleIndex n j) → SU2, ℝ)) (hW : ∀ U, 0 < W U) :
    Step (WilsonProjectionComposition.coordinateState volume W hW)
      (WilsonProjectionComposition.coordinateState volume (directDensity n j W) (directDensity_pos n j W hW)) where
  project := directProjectLinear n j W hW
  expectation := expectation_directProject n j W hW
  contract := fun F _ hF => abs_directProject_le n j W hW F hF

theorem covariance_directProject (n j : ℕ)
    (W : C(Link 4 (scaleIndex n j) → SU2, ℝ)) (hW : ∀ U, 0 < W U)
    (F G : C(Link 4 (scaleIndex n j) → SU2, ℝ)) :
    covariance volume W F G = covariance volume (directDensity n j W)
      (directProject n j W hW F) (directProject n j W hW G) +
      expectation volume (directDensity n j W)
        (directProject n j W hW (F*G) - directProject n j W hW F * directProject n j W hW G) :=
  covariance_action (.cons (directStep n j W hW) (.refl _)) F G

theorem abs_directRemainder_le (n j : ℕ)
    (W : C(Link 4 (scaleIndex n j) → SU2, ℝ)) (hW : ∀ U, 0 < W U)
    (F G : C(Link 4 (scaleIndex n j) → SU2, ℝ))
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hF : ∀ U, |F U| ≤ B) (hG : ∀ U, |G U| ≤ C) (c : Link 4 n → SU2) :
    |directProject n j W hW (F*G) c - directProject n j W hW F c * directProject n j W hW G c| ≤ 2 * B * C :=
  abs_remainder_le (.cons (directStep n j W hW) (.refl _)) F G hB hC hF hG c

/-- The zero-depth conditional expectation is the original mark. -/
theorem directProject_zero (n : ℕ) (W : C(Link 4 (scaleIndex n 0) → SU2, ℝ)) (hW : ∀ U, 0 < W U)
    (F : C(Link 4 (scaleIndex n 0) → SU2, ℝ)) : directProject n 0 W hW F = F := by
  ext U
  rw [directProject_apply, directDensity_zero, directDensity_zero]
  exact mul_div_cancel_left₀ _ (hW U).ne'

/-- Contributions are ordered from the finest eliminated scale to the
coarsest. Each entry is averaged under the density generated at that step;
subsequent entries use the actually transported marks. This construction
requires positivity, but no strong-coupling hypothesis. -/
def scaleCovarianceContribution (n : ℕ) : (j : ℕ) →
    (W : C(Link 4 (scaleIndex n j) → SU2, ℝ)) → (hW : ∀ U, 0 < W U) →
    C(Link 4 (scaleIndex n j) → SU2, ℝ) → C(Link 4 (scaleIndex n j) → SU2, ℝ) → Fin j → ℝ
  | 0, _, _, _, _ => Fin.elim0
  | j+1, W, hW, F, G =>
      let e := blockIndexEquiv 4 (scaleIndex n j)
      let V := PairedLinks.blockedDensity volume e W
      let hV := PairedLinks.blockedDensity_pos volume e W hW
      let P := PairedLinks.blockedProject volume e W hW
      Fin.cases (expectation volume V (P (F*G) - P F * P G))
        (scaleCovarianceContribution n j V hV (P F) (P G))

/-- Exact finite-depth covariance ledger, including all discarded-scale
contributions and the final normalized generated law. -/
theorem covariance_eq_direct_add_scaleContributions (n : ℕ) : ∀ j
    (W : C(Link 4 (scaleIndex n j) → SU2, ℝ)) (hW : ∀ U, 0 < W U)
    (F G : C(Link 4 (scaleIndex n j) → SU2, ℝ)),
    covariance volume W F G =
      covariance volume (directDensity n j W) (directProject n j W hW F) (directProject n j W hW G) +
        ∑ i, scaleCovarianceContribution n j W hW F G i := by
  intro j
  induction j with
  | zero =>
    intro W hW F G
    simp only [directDensity_zero, directProject_zero, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    rfl
  | succ j ih =>
    intro W hW F G
    let e := blockIndexEquiv 4 (scaleIndex n j)
    let V := PairedLinks.blockedDensity volume e W
    let hV := PairedLinks.blockedDensity_pos volume e W hW
    let P := PairedLinks.blockedProject volume e W hW
    have hs := covariance_action (.cons
      (WilsonProjectionComposition.blockedStep volume e W hW) (.refl _)) F G
    change covariance volume W F G = covariance volume V (P F) (P G) +
      expectation volume V (P (F*G) - P F * P G) at hs
    rw [hs, ih V hV (P F) (P G)]
    rw [directDensity_succ, directProject_succ, directProject_succ]
    simp only [scaleCovarianceContribution, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
    ring

/-- Scalar spatial budgets compose by summing the scale contributions.
A uniform depth bound requires controlling this sum, not only its entries. -/
theorem covariance_le_of_scaleContributions (n j : ℕ)
    (W : C(Link 4 (scaleIndex n j) → SU2, ℝ)) (hW : ∀ U, 0 < W U)
    (F G : C(Link 4 (scaleIndex n j) → SU2, ℝ)) (A m D : ℝ) (R : Fin j → ℝ)
    (hfinal : |covariance volume (directDensity n j W)
      (directProject n j W hW F) (directProject n j W hW G)| ≤ A*Real.exp (-m*D))
    (hscale : ∀ i, |scaleCovarianceContribution n j W hW F G i| ≤ R i * Real.exp (-m*D)) :
    |covariance volume W F G| ≤ (A + ∑ i, R i) * Real.exp (-m*D) := by
  rw [covariance_eq_direct_add_scaleContributions n j W hW F G]
  apply (abs_add_le _ _).trans
  calc
    _ ≤ A*Real.exp (-m*D) + ∑ i, R i*Real.exp (-m*D) :=
      add_le_add hfinal ((Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => hscale i))
    _ = _ := by rw [← sum_mul, add_mul]

/-- The total conditional remainder is exactly the sum of the remainders
discarded at each scale, with all intermediate laws generated by integration. -/
theorem expectation_directRemainder_eq_sum (n j : ℕ)
    (W : C(Link 4 (scaleIndex n j) → SU2, ℝ)) (hW : ∀ U, 0 < W U)
    (F G : C(Link 4 (scaleIndex n j) → SU2, ℝ)) :
    expectation volume (directDensity n j W)
      (directProject n j W hW (F*G) - directProject n j W hW F * directProject n j W hW G) =
        ∑ i, scaleCovarianceContribution n j W hW F G i := by
  have h₁ := covariance_directProject n j W hW F G
  have h₂ := covariance_eq_direct_add_scaleContributions n j W hW F G
  linarith

/-- Uniform scale amplitudes and the true dyadic separation yield a
depth-independent bound away from the diagonal. The reversal indexes scales
from the coarsest eliminated step towards the finest. The hypothesis concerns
the actual generated conditional laws and actually transported original marks. -/
theorem directRemainder_le_of_dyadicScaleBounds (n j : ℕ)
    (W : C(Link 4 (scaleIndex n j) → SU2, ℝ)) (hW : ∀ U, 0 < W U)
    (F G : C(Link 4 (scaleIndex n j) → SU2, ℝ)) {A m D δ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 < δ) (hD : δ ≤ m*D)
    (hscale : ∀ i : Fin j, |scaleCovarianceContribution n j W hW F G (Fin.rev i)| ≤
      A * Real.exp (-(m*D)*(2 : ℝ)^(i.val+1))) :
    |expectation volume (directDensity n j W)
      (directProject n j W hW (F*G) - directProject n j W hW F * directProject n j W hW G)| ≤
      (A * Real.exp (-δ) / (1-Real.exp (-δ))) * Real.exp (-m*D) := by
  rw [expectation_directRemainder_eq_sum]
  rw [← Equiv.sum_comp Fin.revPerm]
  calc
    _ ≤ ∑ i : Fin j, |scaleCovarianceContribution n j W hW F G (Fin.rev i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin j, A * Real.exp (-(m*D)*(2 : ℝ)^(i.val+1)) :=
      sum_le_sum fun i _ => hscale i
    _ = A * ∑ i : Fin j, Real.exp (-(m*D)*(2 : ℝ)^(i.val+1)) := (mul_sum _ _ _).symm
    _ ≤ A * (Real.exp (-(m*D)) * Real.exp (-δ) / (1-Real.exp (-δ))) :=
      mul_le_mul_of_nonneg_left (dyadic_exp_sum_le j hδ hD) hA
    _ = _ := by rw [neg_mul]; ring


open SU2BoundaryResponse WilsonLocalResponse
open Mettapedia.Combinatorics.PolymerGas (polymerDist)

/-- Every scale contribution for the original centered gauge-invariant
plaquettes, at arbitrary coupling and arbitrary finite depth. The factors
z and w explicitly retain any cutoff-dependent normalization. -/
theorem wilsonPlaquette_covariance_scales (n j : ℕ) (β z w : ℝ)
    (p q : Plaquette 4 (scaleIndex n j)) :
    let W := realDensity (model (scaleIndex n j) univ) (model_continuous _ univ) β
    let hW := realDensity_pos (model (scaleIndex n j) univ) (model_continuous _ univ) β
    let F := wilsonPlaquetteMark (scaleIndex n j) β z p
    let G := wilsonPlaquetteMark (scaleIndex n j) β w q
    covariance volume W F G = covariance volume (directDensity n j W)
      (directProject n j W hW F) (directProject n j W hW G) +
        ∑ i, scaleCovarianceContribution n j W hW F G i :=
  covariance_eq_direct_add_scaleContributions n j _ _ _ _

/-- A uniform spatial bound for the actual discarded plaquette covariance.
The normalization factors are visible in the prefactor, including at
coincident plaquettes and at separations smaller than two. -/
theorem conditionalCovariance_wilsonPlaquette_le {η β : ℝ} (hη : 0 ≤ η)
    (hβ : |β| ≤ conditionalCovarianceBeta η) (n : ℕ) (z w : ℝ)
    (p q : Plaquette 4 (doubleIndex n)) (c : CoarseConfig n) :
    |conditionalCovariance n β (wilsonPlaquetteMark (doubleIndex n) β z p)
      (wilsonPlaquetteMark (doubleIndex n) β w q) c| ≤
      12 * |z| * |w| * Real.exp 24 * Real.exp (-η*(polymerDist (support p) (support q)-2)) := by
  have h := conditionalCovariance_spatial_le hη hβ n (support p) (support q)
    (support_nonempty p) (support_nonempty q)
    (wilsonPlaquetteMark (doubleIndex n) β z p) (wilsonPlaquetteMark (doubleIndex n) β w q)
    (wilsonPlaquetteMark_local _ β z p) (wilsonPlaquetteMark_local _ β w q)
    (by positivity : 0 ≤ 2*|z|) (by positivity : 0 ≤ 2*|w|)
    (abs_wilsonPlaquetteMark_le _ β z p) (abs_wilsonPlaquetteMark_le _ β w q) c
  have hp : ((support p).card : ℝ) ≤ 4 := by exact_mod_cast card_support_le p
  have hq : ((support q).card : ℝ) ≤ 4 := by exact_mod_cast card_support_le q
  have he : Real.exp (3*(support p).card+3*(support q).card) ≤ Real.exp 24 :=
    Real.exp_le_exp.mpr (by linarith)
  apply h.trans
  calc
    _ ≤ 3*(2*|z|)*(2*|w|)*Real.exp 24 *
        Real.exp (-η*(polymerDist (support p) (support q)-2)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

theorem expectation_conditionalCovariance_wilsonPlaquette_le {η β : ℝ} (hη : 0 ≤ η)
    (hβ : |β| ≤ conditionalCovarianceBeta η) (n : ℕ) (z w : ℝ)
    (p q : Plaquette 4 (doubleIndex n)) :
    |expectation volume (coarseDensity n β)
      (conditionalCovariance n β (wilsonPlaquetteMark (doubleIndex n) β z p)
        (wilsonPlaquetteMark (doubleIndex n) β w q))| ≤
      12 * |z| * |w| * Real.exp 24 * Real.exp (-η*(polymerDist (support p) (support q)-2)) :=
  abs_expectation_le volume _ _ (coarseDensity_pos n β)
    (conditionalCovariance_wilsonPlaquette_le hη hβ n z w p q)

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

theorem scaleLift_mul (n : ℕ) : ∀ j (F G : C(Link 4 n → SU2, ℝ)),
    scaleLift n j (F*G) = scaleLift n j F * scaleLift n j G := by
  intro j
  induction j with
  | zero => intro F G; rfl
  | succ j ih => intro F G; simp only [scaleLift, ih]; rfl

theorem expectation_scaleLift (n j : ℕ)
    (W : C(Link 4 (scaleIndex n j) → SU2, ℝ)) (hW : ∀ U, 0 < W U) (F : C(Link 4 n → SU2, ℝ)) :
    expectation volume W (scaleLift n j F) = expectation volume (directDensity n j W) F := by
  rw [← expectation_directProject n j W hW, directProject_scaleLift]

theorem covariance_scaleLift (n j : ℕ)
    (W : C(Link 4 (scaleIndex n j) → SU2, ℝ)) (hW : ∀ U, 0 < W U) (F G : C(Link 4 n → SU2, ℝ)) :
    covariance volume W (scaleLift n j F) (scaleLift n j G) =
      covariance volume (directDensity n j W) F G := by
  simp only [covariance, ← scaleLift_mul, expectation_scaleLift n j W hW]


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

namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo
open StrongCouplingCrossing WilsonBlockElimination WilsonConditionalProjection.PairedHaar
open WilsonDyadicGeometry SU2WilsonBlockPilot WilsonLocalResponse
open Mettapedia.Combinatorics.PolymerGas (polymerDist)

/-- The radius used by the nonlinear contraction already supplies a single
crossing input for all volumes and finite elimination depths. -/
theorem crossingInput_wilson_iterates {η : ℝ} (hη : 0 < η) (β : ℝ)
    (hβ : |β| ≤ spatialIterationBeta η) :
    CrossingInput.CrossingInput (fun p : ℕ × ℕ => Link 4 p.1) SU2
      (fun p => interactionActivity (InteractionState.iterate p.1 p.2
        (wilsonState (scaleIndex p.1 p.2) β (hβ.trans (spatialIterationBeta_le hη.le)))).terms) := by
  apply crossingInput_of_spatial_norm _ _ hη
  intro p
  exact InteractionState.spatial_small_iterate hη.le p.1 p.2 _
    (wilsonState_spatial_small hη.le _ β _ hβ)

/-- The covariance of exact coarse-product pullbacks is the covariance of
the actual generated law, with no conditional-covariance error. -/
theorem covariance_scaleLift_spatial_le {η : ℝ} (hη : 0 ≤ η) (n j : ℕ)
    (W : C(Link 4 (scaleIndex n j) → SU2, ℝ)) (hW : ∀ U, 0 < W U)
    (A : InteractionState n) (hA : spatialInteractionNorm 8 η A.terms ≤ 1/2)
    (hWA : directDensity n j W = A.density)
    (S T : Finset (Link 4 n)) (hS : S.Nonempty) (F G : C(Link 4 n → SU2, ℝ))
    (hF : DependsOn S F) (hG : DependsOn T G) (B C : ℝ)
    (hB : ∀ U, |F U| ≤ B) (hC : ∀ U, |G U| ≤ C) :
    |covariance volume W (scaleLift n j F) (scaleLift n j G)| ≤
      3 * B * C * Real.exp (3 * S.card + 3 * T.card) * Real.exp (-η * polymerDist S T) := by
  rw [covariance_scaleLift n j W hW, hWA]
  exact A.covariance_spatial_le hη hA S T hS F G hF hG B C hB hC

/-- Fully instantiated spatial clustering for the actual strong-coupling
Wilson density and its nontrivial ordered-product observables. -/
theorem wilson_scaleLift_clustering {η : ℝ} (hη : 0 ≤ η) (β : ℝ)
    (hβ : |β| ≤ spatialIterationBeta η) (n j : ℕ)
    (S T : Finset (Link 4 n)) (hS : S.Nonempty) (F G : C(Link 4 n → SU2, ℝ))
    (hF : DependsOn S F) (hG : DependsOn T G) (B C : ℝ)
    (hB : ∀ U, |F U| ≤ B) (hC : ∀ U, |G U| ≤ C) :
    |covariance volume
      (realDensity (SU2BoundaryResponse.model (scaleIndex n j) univ)
        (SU2BoundaryResponse.model_continuous (scaleIndex n j) univ) β)
      (scaleLift n j F) (scaleLift n j G)| ≤
      3 * B * C * Real.exp (3 * S.card + 3 * T.card) * Real.exp (-η * polymerDist S T) := by
  apply covariance_scaleLift_spatial_le hη n j _
    (realDensity_pos (SU2BoundaryResponse.model (scaleIndex n j) univ)
      (SU2BoundaryResponse.model_continuous (scaleIndex n j) univ) β)
    (InteractionState.iterate n j (wilsonState (scaleIndex n j) β (hβ.trans (spatialIterationBeta_le hη))))
    (InteractionState.spatial_small_iterate hη n j _ (wilsonState_spatial_small hη _ β _ hβ))
    (wilson_density_iterate_direct n j β _).symm S T hS F G hF hG B C hB hC

end Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo

/-! ## Stopping-scale entrance and physical correlation decay -/

namespace Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo
open StrongCouplingCrossing WilsonBlockElimination WilsonConditionalProjection.PairedHaar
open WilsonDyadicGeometry SU2WilsonBlockPilot WilsonLocalResponse
open Mettapedia.GSLT.Ultrainfinite WilsonEliminationRoutes
open Mettapedia.Combinatorics.PolymerGas (polymerDist)

namespace InteractionState

theorem covariance_physical_le {η a rMax : ℝ} (hη : 0 ≤ η) (ha : 0 < a)
    {n : ℕ} (j : ℕ) (hr : coarseSpacing a j ≤ rMax)
    (A : InteractionState n) (hA : spatialInteractionNorm 8 η A.terms ≤ 1/2)
    (S T : Finset (Link 4 n)) (hS : S.Nonempty) (M : ℕ) (hSM : S.card ≤ M) (hTM : T.card ≤ M)
    (F G : C(Link 4 n → SU2, ℝ)) (hF : DependsOn S F) (hG : DependsOn T G)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hFB : ∀ U, |F U| ≤ B) (hGC : ∀ U, |G U| ≤ C) :
    |covariance volume A.density F G| ≤
      3 * B * C * Real.exp (6 * M) * Real.exp (-(η / rMax) * physicalSeparation a j S T) := by
  apply (A.covariance_spatial_le hη hA S T hS F G hF hG B C hFB hGC).trans
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    exact_mod_cast (show 3 * S.card + 3 * T.card ≤ 6 * M by omega)
  · exact decay_le_physical hη ha j hr S T
  · positivity
  · positivity


theorem covariance_anchored_le {η : ℝ} (hη : 0 ≤ η) {n : ℕ}
    (A : InteractionState n) (hA : spatialInteractionNorm 8 η A.terms ≤ 1/2)
    (x y : Link 4 n) {B C : ℝ} (F G : C(Link 4 n → SU2, ℝ))
    (hF : AnchoredObservableBound η x B F) (hG : AnchoredObservableBound η y C G) :
    |covariance volume A.density F G| ≤ 3*B*C*Real.exp (-η*dist x y) := by
  rw [density, covariance_smul_density volume _ _ _ (Real.exp_pos A.vacuum).ne']
  exact covariance_of_anchoredBounds A.terms volume hη A.locality A.empty hA x y F G hF hG

end InteractionState

/-- A finite stopping scale for the actual Wilson density. All rates and
physical scale bounds are fixed before cutoff and volume. Existence of such
data along a weak-coupling trajectory is a separate analytic obligation. -/
structure StoppingScaleEntrance {ι : Type*} (η rMin rMax : ℝ) (a β : ι → ℝ) where
  rate_pos : 0 < η
  lower_pos : 0 < rMin
  spacing_pos : ∀ k, 0 < a k
  coupling_nonneg : ∀ k, 0 ≤ β k
  depth : ι → ℕ
  scale_lower : ∀ k, rMin ≤ coarseSpacing (a k) (depth k)
  scale_upper : ∀ k, coarseSpacing (a k) (depth k) ≤ rMax
  state : ∀ _k : ι, (n : ℕ) → InteractionState n
  generated : ∀ k n, directDensity n (depth k)
    (realDensity (SU2BoundaryResponse.model (scaleIndex n (depth k)) univ)
      (SU2BoundaryResponse.model_continuous (scaleIndex n (depth k)) univ) (β k)) = (state k n).density
  small : ∀ k n, spatialInteractionNorm 8 η (state k n).terms ≤ 1/2

namespace StoppingScaleEntrance
variable {ι : Type*} {η rMin rMax : ℝ} {a β : ι → ℝ}
variable (h : StoppingScaleEntrance η rMin rMax a β)

/-- The original Wilson density at the fine cutoff, without a small-coupling
hypothesis on the input parameter. -/
def fineDensity (k : ι) (n : ℕ) : C(Link 4 (scaleIndex n (h.depth k)) → SU2, ℝ) :=
  realDensity (SU2BoundaryResponse.model (scaleIndex n (h.depth k)) univ)
    (SU2BoundaryResponse.model_continuous (scaleIndex n (h.depth k)) univ) (β k)

theorem fineDensity_pos (k : ι) (n : ℕ) (U : Link 4 (scaleIndex n (h.depth k)) → SU2) :
    0 < h.fineDensity k n U := realDensity_pos _ _ _ _

include h in
theorem upper_pos (k : ι) : 0 < rMax := h.lower_pos.trans_le ((h.scale_lower k).trans (h.scale_upper k))

include h in
theorem physical_rate_pos (k : ι) : 0 < η / rMax := div_pos h.rate_pos (h.upper_pos k)

theorem crossingInput : CrossingInput.CrossingInput (fun p : ι × ℕ => Link 4 p.2) SU2
    (fun p => interactionActivity (h.state p.1 p.2).terms) :=
  crossingInput_of_spatial_norm _ _ h.rate_pos (fun p => h.small p.1 p.2)

theorem generated_fineDensity (k : ι) (n : ℕ) :
    directDensity n (h.depth k) (h.fineDensity k n) = (h.state k n).density := h.generated k n

theorem partition (k : ι) (n : ℕ) : (∫ U, h.fineDensity k n U) = ∫ c, (h.state k n).density c := by
  rw [← h.generated k n]
  exact (integral_directDensity n (h.depth k) _).symm

theorem pullback_clustering (k : ι) (n : ℕ)
    (S T : Finset (Link 4 n)) (hS : S.Nonempty) (M : ℕ) (hSM : S.card ≤ M) (hTM : T.card ≤ M)
    (F G : C(Link 4 n → SU2, ℝ)) (hF : DependsOn S F) (hG : DependsOn T G)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hFB : ∀ U, |F U| ≤ B) (hGC : ∀ U, |G U| ≤ C) :
    |covariance volume (h.fineDensity k n) (scaleLift n (h.depth k) F) (scaleLift n (h.depth k) G)| ≤
      3 * B * C * Real.exp (6 * M) *
        Real.exp (-(η / rMax) * physicalSeparation (a k) (h.depth k) S T) := by
  rw [covariance_scaleLift n (h.depth k) _ (h.fineDensity_pos k n)]
  rw [h.generated_fineDensity k n]
  exact (h.state k n).covariance_physical_le h.rate_pos.le (h.spacing_pos k) (h.depth k)
    (h.scale_upper k) (h.small k n) S T hS M hSM hTM F G hF hG hB hC hFB hGC


/-- The stopping map is the actual integral over all discarded Haar
coordinates, now with the certified generated density as target. -/
def step (k : ι) (n : ℕ) : Step
    (WilsonProjectionComposition.coordinateState volume (h.fineDensity k n) (h.fineDensity_pos k n))
    (h.state k n).weightedState where
  project := directProjectLinear n (h.depth k) (h.fineDensity k n) (h.fineDensity_pos k n)
  expectation F := by
    change expectation volume (h.state k n).density _ = _
    rw [← h.generated_fineDensity k n]
    exact expectation_directProject n (h.depth k) _ (h.fineDensity_pos k n) F
  contract := fun F _ hF => abs_directProject_le n (h.depth k) _ (h.fineDensity_pos k n) F hF

def projected (k : ι) (n : ℕ) (F : C(Link 4 (scaleIndex n (h.depth k)) → SU2, ℝ)) : C(Link 4 n → SU2, ℝ) :=
  directProject n (h.depth k) (h.fineDensity k n) (h.fineDensity_pos k n) F

theorem step_project (k : ι) (n : ℕ) (F : C(Link 4 (scaleIndex n (h.depth k)) → SU2, ℝ)) :
    (h.step k n).project F = h.projected k n F := rfl

theorem projected_scaleLift (k : ι) (n : ℕ) (F : C(Link 4 n → SU2, ℝ)) :
    h.projected k n (scaleLift n (h.depth k) F) = F :=
  directProject_scaleLift n (h.depth k) _ (h.fineDensity_pos k n) F

def covarianceRemainder (k : ι) (n : ℕ) (F G : C(Link 4 (scaleIndex n (h.depth k)) → SU2, ℝ)) :
    C(Link 4 n → SU2, ℝ) := h.projected k n (F*G) - h.projected k n F * h.projected k n G

theorem covarianceRemainder_scaleLift (k : ι) (n : ℕ) (F G : C(Link 4 n → SU2, ℝ)) :
    h.covarianceRemainder k n (scaleLift n (h.depth k) F) (scaleLift n (h.depth k) G) = 0 := by
  rw [covarianceRemainder, ← scaleLift_mul, projected_scaleLift, projected_scaleLift,
    projected_scaleLift, sub_self]

theorem covariance_identity (k : ι) (n : ℕ) (F G : C(Link 4 (scaleIndex n (h.depth k)) → SU2, ℝ)) :
    covariance volume (h.fineDensity k n) F G =
      covariance volume (h.state k n).density (h.projected k n F) (h.projected k n G) +
        expectation volume (h.state k n).density (h.covarianceRemainder k n F G) := by
  simpa only [h.generated_fineDensity, projected, covarianceRemainder] using
    covariance_directProject n (h.depth k) (h.fineDensity k n) (h.fineDensity_pos k n) F G

/-- The unconditional estimate is finite but has no spatial decay. A
separated bound on this term remains an independent entrance obligation. -/
theorem covarianceRemainder_bound (k : ι) (n : ℕ)
    (F G : C(Link 4 (scaleIndex n (h.depth k)) → SU2, ℝ))
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hF : ∀ U, |F U| ≤ B) (hG : ∀ U, |G U| ≤ C) :
    |expectation volume (h.state k n).density (h.covarianceRemainder k n F G)| ≤ 2*B*C := by
  apply abs_expectation_le volume _ _ (h.state k n).density_pos
  exact abs_directRemainder_le n (h.depth k) _ (h.fineDensity_pos k n) F G hB hC hF hG

theorem covariance_le_of_local_approximation (k : ι) (n : ℕ)
    (F G : C(Link 4 (scaleIndex n (h.depth k)) → SU2, ℝ))
    (f g : C(Link 4 n → SU2, ℝ)) (S T : Finset (Link 4 n)) (hS : S.Nonempty)
    (M : ℕ) (hSM : S.card ≤ M) (hTM : T.card ≤ M) (hf : DependsOn S f) (hg : DependsOn T g)
    {B C εF εG εR δ D : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hεF : 0 ≤ εF) (hεG : 0 ≤ εG)
    (hfB : ∀ U, |f U| ≤ B) (hgC : ∀ U, |g U| ≤ C) (hGC : ∀ U, |G U| ≤ C)
    (hlocalF : ∀ c, |h.projected k n F c - f c| ≤ εF * Real.exp (-(η/rMax)*D))
    (hlocalG : ∀ c, |h.projected k n G c - g c| ≤ εG * Real.exp (-(η/rMax)*D))
    (hsep : D-δ ≤ physicalSeparation (a k) (h.depth k) S T)
    (hrem : |expectation volume (h.state k n).density (h.covarianceRemainder k n F G)| ≤
      εR * Real.exp (-(η/rMax)*D)) :
    |covariance volume (h.fineDensity k n) F G| ≤
      (3*B*C*Real.exp (6*M)*Real.exp ((η/rMax)*δ) + 2*εF*C + 2*B*εG + εR) *
        Real.exp (-(η/rMax)*D) := by
  have hrate := (h.physical_rate_pos k).le
  have hdec : Real.exp (-(η/rMax) * physicalSeparation (a k) (h.depth k) S T) ≤
      Real.exp ((η/rMax)*δ) * Real.exp (-(η/rMax)*D) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he := mul_le_mul_of_nonneg_left hsep hrate
    nlinarith
  have hcoarse : |covariance volume (h.state k n).density f g| ≤
      (3*B*C*Real.exp (6*M)*Real.exp ((η/rMax)*δ)) * Real.exp (-(η/rMax)*D) := by
    apply ((h.state k n).covariance_physical_le h.rate_pos.le (h.spacing_pos k) (h.depth k)
      (h.scale_upper k) (h.small k n) S T hS M hSM hTM f g hf hg hB hC hfB hgC).trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdec
      (show 0 ≤ 3*B*C*Real.exp (6*M) by positivity)
  have happrox := abs_covariance_sub_le volume (h.state k n).density
    (h.projected k n F) (h.projected k n G) f g (h.state k n).density_pos
    hB hC (mul_nonneg hεF (Real.exp_pos _).le) (mul_nonneg hεG (Real.exp_pos _).le) hfB
    (abs_directProject_le n (h.depth k) _ (h.fineDensity_pos k n) G hGC) hlocalF hlocalG
  have he : covariance volume (h.fineDensity k n) F G =
      covariance volume (h.state k n).density f g +
      (covariance volume (h.state k n).density (h.projected k n F) (h.projected k n G) -
        covariance volume (h.state k n).density f g) +
      expectation volume (h.state k n).density (h.covarianceRemainder k n F G) := by
    rw [h.covariance_identity k n F G]
    ring
  rw [he]
  calc
    _ ≤ |covariance volume (h.state k n).density f g| +
        |covariance volume (h.state k n).density (h.projected k n F) (h.projected k n G) -
          covariance volume (h.state k n).density f g| +
        |expectation volume (h.state k n).density (h.covarianceRemainder k n F G)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by nlinarith [hcoarse, happrox, hrem]



/-- Transported marks may be sums of local terms with arbitrarily large
supports. The exact local decompositions are charged by anchored spatial
budgets; the conditional covariance is charged separately under the actual
generated law. Every constant is fixed before cutoff and volume. -/
structure TransportControl (B C δ ε : ℝ)
    (F G : ∀ k, (n : ℕ) → C(Link 4 (scaleIndex n (h.depth k)) → SU2, ℝ))
    (D : ι → ℕ → ℝ) where
  left_nonneg : 0 ≤ B
  right_nonneg : 0 ≤ C
  slack_nonneg : 0 ≤ δ
  remainder_nonneg : 0 ≤ ε
  left_anchor : ∀ _k : ι, (n : ℕ) → Link 4 n
  right_anchor : ∀ _k : ι, (n : ℕ) → Link 4 n
  left_budget : ∀ k n, AnchoredObservableBound η (left_anchor k n) B (h.projected k n (F k n))
  right_budget : ∀ k n, AnchoredObservableBound η (right_anchor k n) C (h.projected k n (G k n))
  distance_nonneg : ∀ k n, 0 ≤ D k n
  separation : ∀ k n, D k n - δ ≤
    coarseSpacing (a k) (h.depth k) * dist (left_anchor k n) (right_anchor k n)
  conditional_covariance : ∀ k n,
    |expectation volume (h.state k n).density (h.covarianceRemainder k n (F k n) (G k n))| ≤
      ε * Real.exp (-(η/rMax) * D k n)

/-- Exact pullbacks discharge the conditional-covariance obligation with
zero error. The only observable input is their anchored local budget. -/
def transportControl_pullbacks {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (F G : ∀ _k : ι, (n : ℕ) → C(Link 4 n → SU2, ℝ))
    (x y : ∀ _k : ι, (n : ℕ) → Link 4 n)
    (hF : ∀ k n, AnchoredObservableBound η (x k n) B (F k n))
    (hG : ∀ k n, AnchoredObservableBound η (y k n) C (G k n)) :
    h.TransportControl B C 0 0
      (fun k n => scaleLift n (h.depth k) (F k n)) (fun k n => scaleLift n (h.depth k) (G k n))
      (fun k n => coarseSpacing (a k) (h.depth k) * dist (x k n) (y k n)) where
  left_nonneg := hB
  right_nonneg := hC
  slack_nonneg := le_rfl
  remainder_nonneg := le_rfl
  left_anchor := x
  right_anchor := y
  left_budget := by intro k n; rw [projected_scaleLift]; exact hF k n
  right_budget := by intro k n; rw [projected_scaleLift]; exact hG k n
  distance_nonneg := fun k n => mul_nonneg (coarseSpacing_pos (h.spacing_pos k) _).le dist_nonneg
  separation := by intro k n; simp only [sub_zero, le_refl]
  conditional_covariance := by
    intro k n
    rw [covarianceRemainder_scaleLift]
    simp [WilsonBlockElimination.expectation]

theorem transport_clustering {B C δ ε : ℝ}
    {F G : ∀ k, (n : ℕ) → C(Link 4 (scaleIndex n (h.depth k)) → SU2, ℝ)} {D : ι → ℕ → ℝ}
    (c : h.TransportControl B C δ ε F G D) : ∀ k n,
    |covariance volume (h.fineDensity k n) (F k n) (G k n)| ≤
      (3*B*C*Real.exp ((η/rMax)*δ) + ε) * Real.exp (-(η/rMax) * D k n) := by
  intro k n
  have hB := c.left_nonneg
  have hC := c.right_nonneg
  have hrate := (h.physical_rate_pos k).le
  have hdec := decay_distance_le_physical h.rate_pos.le (h.spacing_pos k) (h.depth k)
    (h.scale_upper k) (dist_nonneg (x := c.left_anchor k n) (y := c.right_anchor k n))
  have hsep : Real.exp (-(η/rMax) *
      (coarseSpacing (a k) (h.depth k) * dist (c.left_anchor k n) (c.right_anchor k n))) ≤
      Real.exp ((η/rMax)*δ) * Real.exp (-(η/rMax)*D k n) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he := mul_le_mul_of_nonneg_left (c.separation k n) hrate
    nlinarith
  have hcoarse : |covariance volume (h.state k n).density
      (h.projected k n (F k n)) (h.projected k n (G k n))| ≤
      (3*B*C*Real.exp ((η/rMax)*δ)) * Real.exp (-(η/rMax)*D k n) := by
    apply ((h.state k n).covariance_anchored_le h.rate_pos.le (h.small k n)
      (c.left_anchor k n) (c.right_anchor k n) _ _ (c.left_budget k n) (c.right_budget k n)).trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hdec.trans hsep)
      (show 0 ≤ 3*B*C by positivity)
  rw [h.covariance_identity k n]
  exact (abs_add_le _ _).trans (by nlinarith [hcoarse, c.conditional_covariance k n])

/-- The physical rate and prefactor precede both cutoff and volume. The
certificate exposes the unproved entrance and transport obligations. -/
theorem uniform_transport_clustering [Nonempty ι] {B C δ ε : ℝ}
    {F G : ∀ k, (n : ℕ) → C(Link 4 (scaleIndex n (h.depth k)) → SU2, ℝ)} {D : ι → ℕ → ℝ}
    (c : h.TransportControl B C δ ε F G D) :
    ∃ m > 0, ∃ A ≥ 0, ∀ k n,
      |covariance volume (h.fineDensity k n) (F k n) (G k n)| ≤ A * Real.exp (-m * D k n) := by
  refine ⟨η/rMax, h.physical_rate_pos (Classical.arbitrary ι),
    3*B*C*Real.exp ((η/rMax)*δ)+ε, ?_, h.transport_clustering c⟩
  have := c.left_nonneg; have := c.right_nonneg; have := c.remainder_nonneg
  positivity

/-- Exact pullbacks need only support and uniform-amplitude control. -/
theorem uniform_pullback_clustering [Nonempty ι] {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (M : ℕ) :
    0 < η/rMax ∧ ∀ k n (S T : Finset (Link 4 n)), S.Nonempty → S.card ≤ M → T.card ≤ M →
      ∀ (F G : C(Link 4 n → SU2, ℝ)), DependsOn S F → DependsOn T G →
      (∀ U, |F U| ≤ B) → (∀ U, |G U| ≤ C) →
      |covariance volume (h.fineDensity k n) (scaleLift n (h.depth k) F) (scaleLift n (h.depth k) G)| ≤
        3*B*C*Real.exp (6*M)*Real.exp (-(η/rMax)*physicalSeparation (a k) (h.depth k) S T) :=
  ⟨h.physical_rate_pos (Classical.arbitrary ι), fun k n S T hS hSM hTM F G hf hg hFB hGC =>
    h.pullback_clustering k n S T hS M hSM hTM F G hf hg hB hC hFB hGC⟩

end StoppingScaleEntrance

/-- The unproved weak-to-strong entrance target for a cutoff sequence. The
cutoff tends to zero while the Wilson inverse coupling tends to infinity;
fixed spatial rates and physical stopping scales must work for all volumes.
Observable transport remains a separate `StoppingScaleEntrance.TransportControl`.
-/
def WeakCouplingEntranceObligation (a β : ℕ → ℝ) : Prop :=
  Filter.Tendsto a Filter.atTop (𝓝 0) ∧ Filter.Tendsto β Filter.atTop Filter.atTop ∧
    ∃ η rMin rMax : ℝ, Nonempty (StoppingScaleEntrance η rMin rMax a β)

/-- A nonvacuous entrance family at fixed strong coupling: the cutoff spacing
is `2^(-k)`, the actual depth is `k`, and the stopping spacing is exactly one.
This example does not assert a weak-coupling or nontrivial continuum limit. -/
def strongCouplingEntrance {η : ℝ} (hη : 0 < η) (β : ℝ) (hβ : 0 ≤ β)
    (hsmall : |β| ≤ spatialIterationBeta η) :
    StoppingScaleEntrance η 1 1 (fun k : ℕ => 1/(2:ℝ)^k) (fun _ => β) where
  rate_pos := hη
  lower_pos := by norm_num
  spacing_pos := by intro k; positivity
  coupling_nonneg := fun _ => hβ
  depth := id
  scale_lower := by
    intro k
    dsimp [coarseSpacing]
    rw [one_div, mul_inv_cancel₀ (pow_ne_zero k (by norm_num : (2:ℝ) ≠ 0))]
  scale_upper := by
    intro k
    dsimp [coarseSpacing]
    rw [one_div, mul_inv_cancel₀ (pow_ne_zero k (by norm_num : (2:ℝ) ≠ 0))]
  state := fun k n => InteractionState.iterate n k
    (wilsonState (scaleIndex n k) β (hsmall.trans (spatialIterationBeta_le hη.le)))
  generated := fun k n => (wilson_density_iterate_direct n k β _).symm
  small := fun k n => InteractionState.spatial_small_iterate hη.le n k _
    (wilsonState_spatial_small hη.le _ β _ hsmall)

open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-- A spatial interaction predicate on the existing weighted boundary states. -/
def spatialInteractionContract {ι : Type} (η R : ℝ) (s : BoundaryState ι) : Prop :=
  ∃ (n : ℕ) (A : InteractionState n), A.weightedState = s.1 ∧ spatialInteractionNorm 8 η A.terms ≤ R

/-- The native forward modality is witnessed by the actual paired-Haar
rewrite, with a spatial gain proved separately from the rewrite definition. -/
theorem haarDiamond_spatialInteractionContract {ι : Type} {n : ℕ} {η R : ℝ}
    (hη : 0 ≤ η) (hR : R ≤ 1/2) (A : InteractionState (doubleIndex n))
    (D : ResponseData A.weightedState ι) (hA : spatialInteractionNorm 8 η A.terms ≤ R) :
    gsltDiamond (haarTheory ι) (spatialInteractionContract η ((4*Real.exp (-2))*R))
      ⟨A.weightedState, D⟩ := by
  apply (gsltDiamond_spec _ _ _).mpr
  refine ⟨_, HaarTransition.paired volume (blockIndexEquiv 4 n) A.density A.density_pos D, ?_⟩
  refine ⟨n, A.block, ?_, (A.spatial_norm_block_le hη (hA.trans hR)).trans
    (mul_le_mul_of_nonneg_left hA (by positivity))⟩
  exact coordinateState_congr volume _ _ _ _ A.density_block

end Mettapedia.QuantumTheory.YangMills.SU2WilsonAssembly.ScaleTwo
