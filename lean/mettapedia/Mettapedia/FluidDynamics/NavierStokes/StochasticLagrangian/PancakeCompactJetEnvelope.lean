import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalSixthDecay

/-!
# A common Fourier envelope constructed from compact physical regularity

Joint continuity of the field and its defined pure sixth coordinate
derivatives on a compact parameter space gives their common bound.
The resulting lattice envelope is uniform in the parameter. In time,
the parameter space can be a compact subinterval of a smooth lifespan;
this theorem does not assert the existence or length of that lifespan.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeCompactJetEnvelope

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeArbitraryDataBlocks
open PancakeContinuousCoordinateJet PancakePhysicalSixthDecay PancakeLatticeDecayEnvelope PancakeCurlOutputTail

local notation "T3" => UnitAddTorus (Fin 3)

theorem exists_finite_continuous_family_bound {ι Q : Type*} [Fintype ι]
    [TopologicalSpace Q] [CompactSpace Q] (f : ι → Q → ℂ) (hf : ∀ i, Continuous (f i)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i x, ‖f i x‖ ≤ B := by
  let F (i : ι) : C(Q, ℂ) := ⟨f i, hf i⟩
  refine ⟨∑ i, ‖F i‖, Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _), ?_⟩
  intro i x
  exact ((F i).norm_coe_le_norm x).trans
    (Finset.single_le_sum (fun a _ ↦ norm_nonneg (F a)) (Finset.mem_univ i))

variable {P : Type*} [TopologicalSpace P] [CompactSpace P]

theorem exists_uniform_sixthMoment_bound (f : P → T3 → VelocityCoefficient)
    (hf : ∀ p i, HasContinuousCoordinateJet 6 (fun x ↦ f p x i))
    (hc : ∀ i, Continuous (fun z : P × T3 ↦ f z.1 z.2 i))
    (h6 : ∀ i j, Continuous (fun z : P × T3 ↦ coordinateJet (fun x ↦ f z.1 x i) j 6 z.2)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p k, fourierMoment 6 (torusFourierVelocity (f p)) k ≤ A := by
  obtain ⟨B0, hB0, hb0⟩ := exists_finite_continuous_family_bound _ hc
  obtain ⟨B6, hB6, hb6⟩ := exists_finite_continuous_family_bound
    (fun ij : Fin 3 × Fin 3 ↦ fun z : P × T3 ↦ coordinateJet (fun x ↦ f z.1 x ij.1) ij.2 6 z.2)
    (fun ij ↦ h6 ij.1 ij.2)
  refine ⟨12288 * (B0 + B6), by positivity, ?_⟩
  intro p k
  apply vector_sixthMoment_le (f p) (hf p) (B0 + B6) (by positivity)
  · intro i
    apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ B0 + B6)).mpr
    intro x
    exact (hb0 i (p, x)).trans (le_add_of_nonneg_right hB6)
  · intro i j
    apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ B0 + B6)).mpr
    intro x
    exact (hb6 (i, j) (p, x)).trans (le_add_of_nonneg_left hB0)

theorem exists_common_secondMoment_envelope (f : P → T3 → VelocityCoefficient)
    (hf : ∀ p i, HasContinuousCoordinateJet 6 (fun x ↦ f p x i))
    (hc : ∀ i, Continuous (fun z : P × T3 ↦ f z.1 z.2 i))
    (h6 : ∀ i j, Continuous (fun z : P × T3 ↦ coordinateJet (fun x ↦ f z.1 x i) j 6 z.2)) :
    ∃ g : Wavevector → ℝ, (∀ k, 0 ≤ g k) ∧ Summable g ∧
      ∀ p k, fourierMoment 2 (torusFourierVelocity (f p)) k ≤ g k := by
  obtain ⟨A, hA, hb⟩ := exists_uniform_sixthMoment_bound f hf hc h6
  exact ⟨decayEnvelope A, decayEnvelope_nonneg A hA, summable_decayEnvelope A,
    fun p ↦ secondMoment_le_decayEnvelope _ A (hb p)⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeCompactJetEnvelope
