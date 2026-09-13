import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredProjectionSourceSplit

/-!
# Finite support of the inviscid nonlinear RHS

The sumset of the input support contains every nonlinear output. A sharp
filter containing both supports resolves the input and its instantaneous
inviscid RHS exactly. This does not assert that either support is
invariant under the nonlinear time evolution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteInviscidSupport

open scoped Pointwise ComplexConjugate
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeCoefficientLimitEquation
open PancakePeriodicVorticityEquation PancakeSobolevFiberEnvelope PancakeFilteredStrainDynamics
open InfiniteFilteredEquation FilteredProjectionSourceSplit

theorem summable_outputFiber (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ k, k ∉ P → u k = 0) (q : Wavevector) (i : Fin 3) :
    Summable (fun k ↦ outputFiber q u k i) := by
  apply summable_of_ne_finset_zero (s := P)
  intro k hk
  simp [outputFiber, hs k hk, modeDot]

theorem inviscidRHS_eq_zero_off_sumset (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ k, k ∉ P → u k = 0) (q : Wavevector) (hq : q ∉ P + P) :
    infiniteVelocityRHS 0 u q = 0 := by
  have hc : infiniteConvection u q = 0 := by
    ext i
    change (∑' k, outputFiber q u k i) = 0
    trans ∑' k : Wavevector, (0 : ℂ)
    · apply tsum_congr
      intro k
      by_cases hk : k ∈ P
      · have hl : q - k ∉ P := by
          intro hl
          have hmem := Finset.add_mem_add hk hl
          have he : k + (q - k) = q := by abel
          exact hq (he ▸ hmem)
        simp [outputFiber, hs (q - k) hl]
      · simp [outputFiber, hs k hk, modeDot]
    · simp
  ext i
  by_cases hzero : modeSquare q = 0 <;>
    simp [infiniteVelocityRHS, hc, unitTorusViscousVorticityCoeff, lerayMode, modeDot, hzero]

def resolvedModes (P : Finset Wavevector) : Finset Wavevector :=
  (P ∪ (P + P)) ∪ -(P ∪ (P + P))

theorem subset_resolvedModes (P : Finset Wavevector) : P ⊆ resolvedModes P :=
  fun _ h ↦ Finset.mem_union_left _ (Finset.mem_union_left _ h)

theorem sumset_subset_resolvedModes (P : Finset Wavevector) : P + P ⊆ resolvedModes P := by
  intro q hq
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hq)

theorem neg_resolvedModes (P : Finset Wavevector) : -resolvedModes P = resolvedModes P := by
  ext q
  simp only [Finset.mem_neg', resolvedModes, Finset.mem_union, Finset.mem_neg', neg_neg]
  tauto

theorem sharpFilter_resolved_reality (P : Finset Wavevector) (q : Wavevector) :
    sharpFilter (resolvedModes P) (-q) = conj (sharpFilter (resolvedModes P) q) := by
  have he : -q ∈ resolvedModes P ↔ q ∈ resolvedModes P := by
    rw [← Finset.mem_neg', neg_resolvedModes]
  simp only [sharpFilter, he]
  split_ifs <;> simp

theorem filtered_input_eq (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ k, k ∉ P → u k = 0) : filteredVelocity (sharpFilter (resolvedModes P)) u = u :=
  FilteredProjectionMean.restrictVelocity_eq_self (resolvedModes P) u
    (fun q hq ↦ hs q (fun hp ↦ hq (subset_resolvedModes P hp)))

theorem filtered_inviscidRHS_eq (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ k, k ∉ P → u k = 0) :
    filteredVelocity (sharpFilter (resolvedModes P)) (infiniteVelocityRHS 0 u) = infiniteVelocityRHS 0 u :=
  FilteredProjectionMean.restrictVelocity_eq_self (resolvedModes P) _
    (fun q hq ↦ inviscidRHS_eq_zero_off_sumset P u hs q
      (fun hp ↦ hq (sumset_subset_resolvedModes P hp)))

/-- There is no subgrid force for this instantaneous fully resolved pair.
Unresolved inputs in a general solution are not covered by this lemma. -/
theorem resolved_subgridForce_zero (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ k, k ∉ P → u k = 0) : subgridForce (sharpFilter (resolvedModes P)) u = 0 := by
  rw [subgridForce_eq_sub _ 1 (norm_sharpFilter_le_one _) u (summable_outputFiber P u hs),
    filtered_input_eq P u hs, filtered_inviscidRHS_eq P u hs, sub_self]

end Mettapedia.FluidDynamics.NavierStokes.FiniteInviscidSupport
