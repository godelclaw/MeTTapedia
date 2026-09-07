import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeIndexedFourierMoments
import Mathlib.Algebra.Module.ZLattice.Summable

/-!
# A summable envelope from uniform sixth-order Fourier decay

The inverse fourth power of one plus the frequency norm is summable on
the three-dimensional lattice. Multiplying this fixed weight by a uniform
sixth-order coefficient bound constructs the common second-moment envelope.
No persistence of that coefficient bound under evolution is claimed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLatticeDecayEnvelope

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeIncomingLowSourceEnergy PancakeCurlOutputTail PancakeIndexedFourierMoments
open Filter

private abbrev integerLattice : Submodule ℤ (Fin 3 → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))

private instance : DiscreteTopology integerLattice := ZSpan.discreteTopology_pi_basisFun

private def latticePoint (k : Wavevector) : integerLattice :=
  ⟨fun j ↦ (k j : ℝ), by
    apply ((Pi.basisFun ℝ (Fin 3)).mem_span_iff_repr_mem ℤ _).mpr
    intro j
    exact ⟨k j, by simp⟩⟩

private theorem latticePoint_injective : Function.Injective latticePoint := by
  intro k l h
  funext j
  have hh := congrFun (congrArg Subtype.val h) j
  change (k j : ℝ) = (l j : ℝ) at hh
  exact_mod_cast hh

private theorem latticePoint_zero : latticePoint 0 = 0 := by ext j; simp [latticePoint]

private theorem norm_latticePoint_le (k : Wavevector) : ‖latticePoint k‖ ≤ ‖frequencyVec k‖ := by
  change ‖fun j ↦ (k j : ℝ)‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  simpa using norm_frequency_coordinate_le k j

def latticeDecayWeight (k : Wavevector) : ℝ := 1 / (1 + ‖frequencyVec k‖) ^ 4

theorem latticeDecayWeight_pos (k : Wavevector) : 0 < latticeDecayWeight k := by
  unfold latticeDecayWeight
  positivity

theorem summable_latticeDecayWeight : Summable latticeDecayWeight := by
  have hr : Module.finrank ℤ integerLattice = 3 := by
    rw [ZLattice.rank ℝ integerLattice]
    simp
  have hs := (ZLattice.summable_norm_rpow integerLattice (-4) (by rw [hr]; norm_num)).comp_injective
    latticePoint_injective
  apply hs.of_norm_bounded_eventually
  filter_upwards [show ∀ᶠ k : Wavevector in cofinite, k ≠ 0 from eventually_cofinite_ne 0] with k hk
  have hn : 0 < ‖latticePoint k‖ := norm_pos_iff.mpr (fun hz ↦ hk
    (latticePoint_injective (hz.trans latticePoint_zero.symm)))
  rw [Real.norm_eq_abs, abs_of_pos (latticeDecayWeight_pos k)]
  change 1 / (1 + ‖frequencyVec k‖) ^ 4 ≤ ‖latticePoint k‖ ^ (-4 : ℝ)
  simp only [Real.rpow_neg (norm_nonneg _), Real.rpow_ofNat]
  rw [← one_div]
  apply one_div_le_one_div_of_le (pow_pos hn 4)
  gcongr
  exact (norm_latticePoint_le k).trans (le_add_of_nonneg_left zero_le_one)

def decayEnvelope (A : ℝ) (k : Wavevector) : ℝ := A * latticeDecayWeight k

theorem decayEnvelope_nonneg (A : ℝ) (hA : 0 ≤ A) (k : Wavevector) : 0 ≤ decayEnvelope A k :=
  mul_nonneg hA (latticeDecayWeight_pos k).le

theorem summable_decayEnvelope (A : ℝ) : Summable (decayEnvelope A) :=
  summable_latticeDecayWeight.mul_left A

theorem secondMoment_le_decayEnvelope (u : FourierVelocity) (A : ℝ)
    (hA : ∀ k, fourierMoment 6 u k ≤ A) (k : Wavevector) :
    fourierMoment 2 u k ≤ decayEnvelope A k := by
  have hp : 0 < 1 + ‖frequencyVec k‖ := by positivity
  change (1 + ‖frequencyVec k‖)^2 * ‖coefficientVec (u k)‖ ≤ A * (1 / (1 + ‖frequencyVec k‖)^4)
  rw [mul_one_div, le_div_iff₀ (pow_pos hp 4)]
  calc
    _ = fourierMoment 6 u k := by unfold fourierMoment; ring
    _ ≤ A := hA k

theorem summable_secondMoment_of_decay (u : FourierVelocity) (A : ℝ)
    (hA : ∀ k, fourierMoment 6 u k ≤ A) : Summable (fourierMoment 2 u) :=
  Summable.of_nonneg_of_le (fourierMoment_nonneg _ _) (secondMoment_le_decayEnvelope u A hA)
    (summable_decayEnvelope A)

end Mettapedia.FluidDynamics.NavierStokes.PancakeLatticeDecayEnvelope
