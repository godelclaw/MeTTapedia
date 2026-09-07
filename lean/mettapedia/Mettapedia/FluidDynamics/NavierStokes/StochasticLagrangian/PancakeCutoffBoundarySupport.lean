import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalizedProjectionBoundary

/-!
# Only boundary receivers can escape a retained Fourier set

The boundary is constructed from the actual finite cutoff shifts. All
interior receiver modes cancel from the exterior convolution. A buffer
containing every shifted active receiver makes this term exactly zero.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeCutoffBoundarySupport

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFiniteFourierLocalization
open PancakeLocalizedProjectionBoundary PancakeDyadicDirectionEvolution

local notation "T3" => UnitAddTorus (Fin 3)

def cutoffBoundaryReceivers (cutoff modes : Finset Wavevector) : Finset Wavevector := by
  classical
  exact modes.filter (fun k ↦ ∃ p ∈ cutoff, p + k ∉ modes)

theorem mem_cutoffBoundaryReceivers (cutoff modes : Finset Wavevector) (k : Wavevector) :
    k ∈ cutoffBoundaryReceivers cutoff modes ↔ k ∈ modes ∧ ∃ p ∈ cutoff, p + k ∉ modes := by
  classical
  exact Finset.mem_filter

theorem cutoffBoundaryReceivers_subset (cutoff modes : Finset Wavevector) :
    cutoffBoundaryReceivers cutoff modes ⊆ modes := Finset.filter_subset _ _

theorem exterior_convolution_eq_boundary_receivers (cutoff modes : Finset Wavevector)
    (c : Wavevector → ℂ) (w : FourierVelocity) (q : Wavevector) (hq : q ∉ modes) :
    finiteCutoffConvolutionCoeff cutoff modes c w q =
      finiteCutoffConvolutionCoeff cutoff (cutoffBoundaryReceivers cutoff modes) c w q := by
  classical
  simp only [finiteCutoffConvolutionCoeff, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  symm
  apply Finset.sum_subset (cutoffBoundaryReceivers_subset cutoff modes)
  intro k hk hkb
  have hneq : p + k ≠ q := by
    intro he
    apply hkb
    exact (mem_cutoffBoundaryReceivers cutoff modes k).mpr ⟨hk, p, hp, he ▸ hq⟩
  simp [hneq]

theorem cutoffOutputModes_mono (cutoff s t : Finset Wavevector) (hst : s ⊆ t) :
    finiteCutoffOutputModes cutoff s ⊆ finiteCutoffOutputModes cutoff t := by
  intro q hq
  obtain ⟨p, hp, k, hk, he⟩ := (mem_finiteCutoffOutputModes_iff cutoff s q).mp hq
  exact (mem_finiteCutoffOutputModes_iff cutoff t q).mpr ⟨p, hp, k, hst hk, he⟩

theorem localizedBoundaryField_eq_boundary_receivers (cutoff modes : Finset Wavevector)
    (c : Wavevector → ℂ) (w : FourierVelocity) (x : T3) :
    localizedBoundaryField cutoff modes c w x =
      complexRealPartEuclideanCLM (finiteFourierReconstruction
        (finiteCutoffOutputModes cutoff (cutoffBoundaryReceivers cutoff modes) \ modes)
        (finiteCutoffConvolutionCoeff cutoff (cutoffBoundaryReceivers cutoff modes) c w) x) := by
  unfold localizedBoundaryField
  congr 1
  have he : finiteFourierReconstruction (finiteCutoffOutputModes cutoff modes \ modes)
      (finiteCutoffConvolutionCoeff cutoff modes c w) x =
      finiteFourierReconstruction (finiteCutoffOutputModes cutoff modes \ modes)
        (finiteCutoffConvolutionCoeff cutoff (cutoffBoundaryReceivers cutoff modes) c w) x := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [exterior_convolution_eq_boundary_receivers cutoff modes c w q (Finset.mem_sdiff.mp hq).2]
  rw [he]
  apply reconstruction_subset_of_zero
  · exact Finset.sdiff_subset_sdiff (cutoffOutputModes_mono cutoff _ modes
      (cutoffBoundaryReceivers_subset cutoff modes)) (Finset.Subset.refl _)
  · intro q hq hsmall
    apply convolutionCoeff_eq_zero_outside
    intro hqB
    exact hsmall (Finset.mem_sdiff.mpr ⟨hqB, (Finset.mem_sdiff.mp hq).2⟩)

theorem localizedBoundaryField_eq_zero_of_buffered_support (cutoff modes : Finset Wavevector)
    (c : Wavevector → ℂ) (w : FourierVelocity)
    (hbuffer : ∀ k ∈ modes, w k ≠ 0 → ∀ p ∈ cutoff, p + k ∈ modes) (x : T3) :
    localizedBoundaryField cutoff modes c w x = 0 := by
  have hz : ∀ q, q ∉ modes → finiteCutoffConvolutionCoeff cutoff modes c w q = 0 := by
    intro q hq
    apply Finset.sum_eq_zero
    intro pk hpk
    obtain ⟨hmem, he⟩ := Finset.mem_filter.mp hpk
    obtain ⟨hp, hk⟩ := Finset.mem_product.mp hmem
    have hw : w pk.2 = 0 := by
      by_contra hn
      exact hq (he ▸ hbuffer pk.2 hk hn pk.1 hp)
    rw [hw, smul_zero]
  unfold localizedBoundaryField
  have he : finiteFourierReconstruction (finiteCutoffOutputModes cutoff modes \ modes)
      (finiteCutoffConvolutionCoeff cutoff modes c w) x = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    rw [hz q (Finset.mem_sdiff.mp hq).2, smul_zero]
  rw [he, map_zero]

end Mettapedia.FluidDynamics.NavierStokes.PancakeCutoffBoundarySupport
