import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteFilteredEquation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeGalerkinVorticityBridge

/-!
# The actual retained vorticity equation

Taking curl of the filtered infinite velocity equation leaves the curl of
the all-input subgrid force. For a sharp filter, the retained coefficients
are those of the original solution. Their sector energy equation therefore
has an explicit unresolved-input work term. No closed Galerkin evolution
is attributed to the actual solution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalFilteredVorticity

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy
open PancakeGalerkinVorticityBridge PancakeIncomingLowSourceEnergy
open PancakeSignedTransportEnergy PancakeViscousMisalignmentAbsorption
open PancakeFilteredStrainDynamics InfiniteFilteredEquation PancakeLocalInfiniteVelocity
open PancakePeriodicComplexStretch

theorem fourierCurl_add (u v : FourierVelocity) :
    fourierCurl (u + v) = fourierCurl u + fourierCurl v := by
  funext q
  exact (congrArg (unitTorusDerivativePhase • ·)
    (cross_add_right (wavevectorCoefficient q) (u q) (v q))).trans (smul_add _ _ _)

theorem fourierCurl_filteredVelocity (chi : Wavevector → ℂ) (u : FourierVelocity) :
    fourierCurl (filteredVelocity chi u) = filteredVelocity chi (fourierCurl u) := by
  funext q
  simp only [fourierCurl, filteredVelocity, coefficientCross_smul_right]
  exact smul_comm _ _ _

theorem filteredVelocity_sharp_mem (modes : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) (hq : q ∈ modes) :
    filteredVelocity (sharpFilter modes) u q = u q := by
  simp [filteredVelocity, sharpFilter, hq]

theorem incomingNonlinearCoeff_congr (sources receivers : Finset Wavevector)
    (w w' v v' : FourierVelocity)
    (hw : ∀ k ∈ sources, w k = w' k) (hv : ∀ k ∈ receivers, v k = v' k)
    (q : Wavevector) :
    incomingNonlinearCoeff sources receivers w v q =
      incomingNonlinearCoeff sources receivers w' v' q := by
  classical
  rw [PancakeExchangeSymmetricCurl.incomingNonlinearCoeff_eq_pairSum,
    PancakeExchangeSymmetricCurl.incomingNonlinearCoeff_eq_pairSum]
  apply Finset.sum_congr rfl
  intro p hp
  have hm := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  rw [hw p.1 hm.1, hv p.2 hm.2]

theorem vorticityRHS_eq_incoming_add_viscous (sources receivers : Finset Wavevector)
    (w v : FourierVelocity) (nu : ℝ) (q : Wavevector) :
    finiteUnitTorusVorticityRHS sources receivers w v nu q =
      incomingNonlinearCoeff sources receivers w v q + unitTorusViscousVorticityCoeff nu v q := by
  unfold finiteUnitTorusVorticityRHS finiteUnitTorusNonstretchingCoeff incomingNonlinearCoeff
  abel

/-- The unresolved term is an internal nonlinear feedback, not an external
body force added to the unforced Navier--Stokes equation. -/
def subgridCurl (chi : Wavevector → ℂ) (u : FourierVelocity) : FourierVelocity :=
  fourierCurl (subgridForce chi u)

variable {nu T B : ℝ} {u₀ : FourierVelocity}

theorem hasDerivAt_filtered_fourierCurl (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ k, ‖chi k‖ ≤ C)
    (modes : Finset Wavevector) (hcut : ∀ k, k ∉ modes → chi k = 0)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (q : Wavevector) (i : Fin 3) :
    HasDerivAt (fun τ ↦ fourierCurl (filteredVelocity chi (s.coefficients τ)) q i)
      ((finiteUnitTorusVorticityRHS modes modes
        (fourierCurl (filteredVelocity chi (s.coefficients t)))
        (fourierCurl (filteredVelocity chi (s.coefficients t))) nu q +
          subgridCurl chi (s.coefficients t) q) i) t := by
  have h := hasDerivAt_fourierCurl (fun τ ↦ filteredVelocity chi (s.coefficients τ))
    (velocityRHS modes (filteredVelocity chi (s.coefficients t)) nu +
      subgridForce chi (s.coefficients t)) t q
    (fun j ↦ hasDerivAt_filtered_coefficients_finite s chi C hchi modes hcut hk t ht q j) i
  rw [fourierCurl_add, Pi.add_apply, fourierCurl_velocityRHS modes _ nu q hk
    (fun k _ ↦ filteredVelocity_transverse chi _ k (s.transverse t k))] at h
  exact h

/-- The exact equation for each retained coefficient of the full solution.
Both unresolved inputs survive in the last term. -/
theorem hasDerivAt_retained_fourierCurl (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (modes : Finset Wavevector) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (q : Wavevector) (hq : q ∈ modes) (i : Fin 3) :
    HasDerivAt (fun τ ↦ fourierCurl (s.coefficients τ) q i)
      ((finiteUnitTorusVorticityRHS modes modes
        (fourierCurl (s.coefficients t)) (fourierCurl (s.coefficients t)) nu q +
          subgridCurl (sharpFilter modes) (s.coefficients t) q) i) t := by
  have h := hasDerivAt_filtered_fourierCurl s (sharpFilter modes) 1
    (norm_sharpFilter_le_one modes) modes
    (fun k hkm ↦ by simp [sharpFilter, hkm]) hk t ht q i
  simp only [fourierCurl_filteredVelocity, filteredVelocity_sharp_mem modes _ q hq] at h
  rw [vorticityRHS_eq_incoming_add_viscous,
    incomingNonlinearCoeff_congr modes modes _ (fourierCurl (s.coefficients t))
      _ (fourierCurl (s.coefficients t))
      (filteredVelocity_sharp_mem modes _) (filteredVelocity_sharp_mem modes _)] at h
  have hv : unitTorusViscousVorticityCoeff nu
      (filteredVelocity (sharpFilter modes) (fourierCurl (s.coefficients t))) q =
      unitTorusViscousVorticityCoeff nu (fourierCurl (s.coefficients t)) q := by
    unfold unitTorusViscousVorticityCoeff
    rw [filteredVelocity_sharp_mem modes _ q hq]
  rw [hv, ← vorticityRHS_eq_incoming_add_viscous] at h
  exact h

/-- Work of a general additional coefficient source on the fixed
misalignment sector. The work is signed, not silently discarded. -/
def sectorSourceWork (outputs : Finset Wavevector) (w f : FourierVelocity) : ℝ :=
  2 * ∑ q ∈ outputs, (coefficientHermitian (misalignedField w q) (f q)).re

theorem hasDerivAt_misalignedEnergy_forced
    (sources receivers outputs : Finset Wavevector) (w f : FourierVelocity)
    (v : ℝ → FourierVelocity) (nu t : ℝ)
    (he : ∀ q ∈ outputs, ∀ i, HasDerivAt (fun τ ↦ v τ q i)
      ((finiteUnitTorusVorticityRHS sources receivers w (v t) nu q + f q) i) t) :
    HasDerivAt (fun τ ↦ misalignedEnergy outputs (v τ))
      (incomingEnergyRate sources receivers outputs w (v t) -
        2 * nu * (2 * Real.pi)^2 * misalignedDissipation outputs (v t) +
          sectorSourceWork outputs (v t) f) t := by
  have h := hasDerivAt_misalignmentEnergy outputs v
    (finiteUnitTorusVorticityRHS sources receivers w (v t) nu + f) t he
  have hv : (∑ q ∈ outputs,
      (coefficientHermitian (misalignmentComponent q (v t q))
        (unitTorusViscousVorticityCoeff nu (v t) q)).re) =
      -nu * (2 * Real.pi)^2 * misalignedDissipation outputs (v t) := by
    simp_rw [viscous_misalignment_energy_pair]
    rw [misalignedDissipation, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    dsimp only [misalignedField]
    ring
  apply h.congr_deriv
  simp only [Pi.add_apply, finiteUnitTorusVorticityRHS, finiteUnitTorusNonstretchingCoeff,
    incomingEnergyRate, incomingNonlinearCoeff, sectorSourceWork, misalignedField,
    hermitian_add_right, Complex.add_re, Finset.sum_add_distrib]
  rw [hv]
  ring

theorem hasDerivAt_retained_misalignedEnergy (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (modes outputs : Finset Wavevector) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (ho : outputs ⊆ modes) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ misalignedEnergy outputs (fourierCurl (s.coefficients τ)))
      (incomingEnergyRate modes modes outputs (fourierCurl (s.coefficients t))
        (fourierCurl (s.coefficients t)) -
        2 * nu * (2 * Real.pi)^2 * misalignedDissipation outputs (fourierCurl (s.coefficients t)) +
        sectorSourceWork outputs (fourierCurl (s.coefficients t))
          (subgridCurl (sharpFilter modes) (s.coefficients t))) t :=
  hasDerivAt_misalignedEnergy_forced modes modes outputs _ _ _ nu t
    (fun q hq i ↦ hasDerivAt_retained_fourierCurl s modes hk t ht q (ho hq) i)

/-- Absorbing low sources leaves high-source work AND unresolved-input
work. This is an inequality for the actual solution, not a truncation. -/
theorem retained_misalignedEnergy_lowSource_absorption
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 < nu)
    (cutoff : ℝ) (modes outputs : Finset Wavevector)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0) (ho : outputs ⊆ modes)
    (houtput : ∀ q ∈ outputs, cutoff ≤ ‖frequencyVec q‖)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    deriv (fun τ ↦ misalignedEnergy outputs (fourierCurl (s.coefficients τ))) t +
      nu * (2 * Real.pi)^2 * misalignedDissipation outputs (fourierCurl (s.coefficients t)) ≤
        incomingEnergyRate (highSources cutoff modes) modes outputs
          (fourierCurl (s.coefficients t)) (fourierCurl (s.coefficients t)) +
        sectorSourceWork outputs (fourierCurl (s.coefficients t))
          (subgridCurl (sharpFilter modes) (s.coefficients t)) +
        lowSourceCost nu (lowSources cutoff modes) modes
          (fourierCurl (s.coefficients t)) (fourierCurl (s.coefficients t)) := by
  rw [(hasDerivAt_retained_misalignedEnergy s modes outputs hk ho t ht).deriv,
    incomingEnergyRate_low_add_high cutoff]
  have hb := incomingEnergyRate_absorb (lowSources cutoff modes) modes outputs
    (fourierCurl (s.coefficients t)) (fourierCurl (s.coefficients t))
    (fun q hq k hk ↦ (Finset.mem_filter.mp hk).2.trans (houtput q hq)) nu hnu
  have ha := le_abs_self (incomingEnergyRate (lowSources cutoff modes) modes outputs
    (fourierCurl (s.coefficients t)) (fourierCurl (s.coefficients t)))
  linarith

end Mettapedia.FluidDynamics.NavierStokes.LocalFilteredVorticity
