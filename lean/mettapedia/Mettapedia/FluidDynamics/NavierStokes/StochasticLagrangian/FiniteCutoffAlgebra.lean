import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureBilinearLocalization
import Mettapedia.Analysis.FiniteVectorConvolution

/-! # Collected cutoff supports and the pressure pair symmetry -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteCutoffAlgebra

open scoped BigOperators
open PeriodicFourierTriad PancakeFiniteFourierLocalization PancakeFrequencyProjectorCommutator
open ComplexPressureConvolution PressurePairInputStability
open Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem finiteCutoffOutputModes_comm (A P : Finset Wavevector) :
    finiteCutoffOutputModes A P = finiteCutoffOutputModes P A := by
  ext q
  simp only [mem_finiteCutoffOutputModes_iff]
  constructor <;> rintro ⟨a, ha, p, hp, rfl⟩ <;> exact ⟨p, hp, a, ha, add_comm _ _⟩

theorem finiteCutoffOutputModes_assoc (A P K : Finset Wavevector) :
    finiteCutoffOutputModes (finiteCutoffOutputModes A P) K =
      finiteCutoffOutputModes A (finiteCutoffOutputModes P K) := by
  ext q
  simp only [mem_finiteCutoffOutputModes_iff]
  constructor
  · rintro ⟨ap, ⟨a, ha, p, hp, rfl⟩, k, hk, rfl⟩
    exact ⟨a, ha, p + k, ⟨p, hp, k, hk, rfl⟩, (add_assoc _ _ _).symm⟩
  · rintro ⟨a, ha, pk, ⟨p, hp, k, hk, rfl⟩, rfl⟩
    exact ⟨a + p, ⟨a, ha, p, hp, rfl⟩, k, hk, add_assoc _ _ _⟩

theorem pairConvolution_swap (e : R3) (P K : Finset Wavevector)
    (w v : FourierVelocity) (q : Wavevector) :
    pairConvolution e P K w v q = pairConvolution e K P v w q := by
  unfold pairConvolution
  apply Finset.sum_equiv (Equiv.prodComm Wavevector Wavevector)
  · intro pk
    simp only [Finset.mem_filter, Finset.mem_product, Equiv.prodComm_apply,
      Prod.fst_swap, Prod.snd_swap, add_comm, and_comm]
  · intro pk _
    exact (tiltPair_swap e pk.1 pk.2 (w pk.1) (v pk.2)).symm

theorem coefficientVec_cutoff (A P : Finset Wavevector) (c : Wavevector → ℂ)
    (w : FourierVelocity) (q : Wavevector) :
    coefficientVec (finiteCutoffConvolutionCoeff A P c w q) =
      vectorConvolution A P c (fun p ↦ coefficientVec (w p)) q := by
  simp only [coefficientVec, finiteCutoffConvolutionCoeff, vectorConvolution,
    WithLp.toLp_sum, WithLp.toLp_smul]

theorem sum_norm_cutoff_le (A P : Finset Wavevector) (c : Wavevector → ℂ)
    (w : FourierVelocity) :
    (∑ q ∈ finiteCutoffOutputModes A P,
      ‖coefficientVec (finiteCutoffConvolutionCoeff A P c w q)‖) ≤
      (∑ a ∈ A, ‖c a‖) * ∑ p ∈ P, ‖coefficientVec (w p)‖ := by
  simp only [coefficientVec_cutoff]
  exact sum_norm_vectorConvolution_le A P (finiteCutoffOutputModes A P) c _
    (fun a ha p hp ↦ (mem_finiteCutoffOutputModes_iff A P _).mpr ⟨a, ha, p, hp, rfl⟩)

end Mettapedia.FluidDynamics.NavierStokes.FiniteCutoffAlgebra
