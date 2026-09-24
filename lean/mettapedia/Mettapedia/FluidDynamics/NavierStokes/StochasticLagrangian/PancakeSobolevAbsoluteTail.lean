import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalInfiniteVelocity

/-!
# Uniform absolute Fourier tails from second-order energy

Cauchy--Schwarz controls the entire coefficient tail by the summable
inverse-fourth-power lattice tail. The estimate is uniform over all fields
with the same second-order energy budget; no termwise uniform l1 envelope
is required.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSobolevAbsoluteTail

open scoped BigOperators Topology
open Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeLatticeDecayEnvelope
open PancakeFiniteConvolutionL2 PancakeIndexedFourierMoments

def decayTail (F : Finset Wavevector) : ℝ :=
  latticeMass - ∑ k ∈ F, latticeDecayWeight k

theorem decayTail_nonneg (F : Finset Wavevector) : 0 ≤ decayTail F :=
  sub_nonneg.mpr (summable_latticeDecayWeight.sum_le_tsum F
    (fun k _ ↦ (latticeDecayWeight_pos k).le))

theorem decayTail_empty : decayTail ∅ = latticeMass := by simp [decayTail]

theorem sum_decay_le_tail (F M : Finset Wavevector) (h : Disjoint M F) :
    (∑ k ∈ M, latticeDecayWeight k) ≤ decayTail F := by
  have hs := summable_latticeDecayWeight.sum_le_tsum (M ∪ F)
    (fun k _ ↦ (latticeDecayWeight_pos k).le)
  rw [Finset.sum_union h] at hs
  exact le_sub_iff_add_le.mpr hs

theorem tendsto_decayTail : Tendsto decayTail atTop (𝓝 0) := by
  change Tendsto (fun F : Finset Wavevector ↦ latticeMass - ∑ k ∈ F, latticeDecayWeight k)
    atTop (𝓝 0)
  have hc : Tendsto (fun _ : Finset Wavevector ↦ latticeMass) atTop (𝓝 latticeMass) :=
    tendsto_const_nhds
  simpa only [decayTail, latticeMass, sub_self] using hc.sub summable_latticeDecayWeight.hasSum

theorem inverse_weight_sq (k : Wavevector) : (1 / weight k)^2 = latticeDecayWeight k := by
  simp [weight, latticeDecayWeight]
  ring

theorem sum_amplitude_le_tail (u : FourierVelocity) (B : ℝ)
    (hB : ∀ M : Finset Wavevector, sobolevEnergy M u ≤ B)
    (F M : Finset Wavevector) (h : Disjoint M F) :
    (∑ k ∈ M, amplitude u k) ≤ Real.sqrt (decayTail F) * Real.sqrt B := by
  have he (k : Wavevector) :
      amplitude u k = (1 / weight k) * (weight k * amplitude u k) := by
    field_simp [(weight_pos k).ne']
  calc
    _ = ∑ k ∈ M, (1 / weight k) * (weight k * amplitude u k) :=
      Finset.sum_congr rfl (fun k _ ↦ he k)
    _ ≤ Real.sqrt (∑ k ∈ M, (1 / weight k)^2) *
        Real.sqrt (sobolevEnergy M u) :=
      Real.sum_mul_le_sqrt_mul_sqrt M _ _
    _ ≤ Real.sqrt (decayTail F) * Real.sqrt B := by
      apply mul_le_mul
      · apply Real.sqrt_le_sqrt
        simp_rw [inverse_weight_sq]
        exact sum_decay_le_tail F M h
      · exact Real.sqrt_le_sqrt (hB M)
      · exact Real.sqrt_nonneg _
      · exact Real.sqrt_nonneg _

theorem summable_amplitude (u : FourierVelocity) (B : ℝ)
    (hB : ∀ M : Finset Wavevector, sobolevEnergy M u ≤ B) :
    Summable (amplitude u) := by
  apply summable_of_sum_le (fun k ↦ norm_nonneg (coefficientVec (u k)))
  intro M
  exact sum_amplitude_le_tail u B hB ∅ M (Finset.disjoint_empty_right M)

theorem summable_norm_coefficients (u : FourierVelocity) (B : ℝ)
    (hB : ∀ M : Finset Wavevector, sobolevEnergy M u ≤ B) :
    Summable (fun k ↦ ‖u k‖) :=
  (summable_amplitude u B hB).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun k ↦ norm_coefficient_sup_le_euclidean (u k))

def tailAllowance (B : ℝ) (F : Finset Wavevector) : ℝ :=
  Real.sqrt (decayTail F) * Real.sqrt B

theorem tailAllowance_nonneg (B : ℝ) (F : Finset Wavevector) : 0 ≤ tailAllowance B F := by
  unfold tailAllowance
  positivity

theorem tendsto_tailAllowance (B : ℝ) : Tendsto (tailAllowance B) atTop (𝓝 0) := by
  change Tendsto (fun F ↦ Real.sqrt (decayTail F) * Real.sqrt B) atTop (𝓝 0)
  simpa only [tailAllowance, Real.sqrt_zero, zero_mul] using
    tendsto_decayTail.sqrt.mul_const (Real.sqrt B)

theorem exists_small_tailAllowance (B ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset Wavevector, tailAllowance B F < ε :=
  ((tendsto_tailAllowance B).eventually (gt_mem_nhds hε)).exists

end Mettapedia.FluidDynamics.NavierStokes.PancakeSobolevAbsoluteTail
