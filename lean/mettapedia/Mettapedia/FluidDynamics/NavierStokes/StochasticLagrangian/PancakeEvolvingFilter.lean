import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMovingBlockEvolution

/-!
# Material evolution with time-dependent Fourier weights

The moving-point hard-block theorem keeps its frame and mode set fixed.
An adaptive frequency filter also has a time derivative.  On a fixed finite
ambient support, this module differentiates all three factors: the filter,
the vorticity coefficient, and the Fourier character of the observation point.

The nonlinear material commutator has the exact multiplier difference
`weight q - weight receiver`.  The evolving-filter residual additionally
contains `weightDot q • eta q` and the weighted viscous multiplier.  No bound
on these terms, or differentiability of a changing hard selector, is assumed
as a conclusion.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeEvolvingFilter

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakePeriodicComplexStretch PancakePeriodicVorticityEquation
open PancakeMaterialTransportCommutator PancakeMovingBlockEvolution
open PancakeBilinearPeriodization

/-- Scalar Fourier filtering, before any support restriction. -/
def weightedCoefficients (weight : Wavevector → ℂ)
    (eta : FourierVelocity) : FourierVelocity := fun q ↦ weight q • eta q

/-- The coefficient derivative includes the filter's own rate. -/
def evolvingWeightedCoefficientRate (weight weightDot : Wavevector → ℂ)
    (eta etaDot : FourierVelocity) : FourierVelocity :=
  fun q ↦ weightDot q • eta q + weight q • etaDot q

theorem hasDerivAt_evolvingWeightedCoefficient
    (weightPath : ℝ → Wavevector → ℂ) (weightDot : Wavevector → ℂ)
    (etaPath : ℝ → FourierVelocity) (etaDot : FourierVelocity)
    (q : Wavevector) (i : Fin 3) (t : ℝ)
    (hw : HasDerivAt (fun tau ↦ weightPath tau q) (weightDot q) t)
    (he : HasDerivAt (fun tau ↦ etaPath tau q i) (etaDot q i) t) :
    HasDerivAt (fun tau ↦ weightedCoefficients (weightPath tau) (etaPath tau) q i)
      (evolvingWeightedCoefficientRate (weightPath t) weightDot
        (etaPath t) etaDot q i) t := by
  have hprod := (hw.hasFDerivAt.smul he.hasFDerivAt).hasDerivAt
  convert hprod using 1
  all_goals first | rfl |
    simp [evolvingWeightedCoefficientRate, add_comm]

/-- Product rule for an evolving filter along a moving observation point. -/
theorem hasDerivAt_evolvingFilterReconstruction
    (s : Finset Wavevector)
    (weightPath : ℝ → Wavevector → ℂ) (weightDot : Wavevector → ℂ)
    (etaPath : ℝ → FourierVelocity) (etaDot : FourierVelocity)
    (xPath : ℝ → UnitAddTorus (Fin 3)) (phaseDot : Wavevector → ℂ) (t : ℝ)
    (hw : ∀ q ∈ s, HasDerivAt (fun tau ↦ weightPath tau q) (weightDot q) t)
    (he : ∀ q ∈ s, ∀ i, HasDerivAt (fun tau ↦ etaPath tau q i) (etaDot q i) t)
    (hx : ∀ q ∈ s, HasDerivAt
      (fun tau ↦ UnitAddTorus.mFourier q (xPath tau)) (phaseDot q) t) :
    HasDerivAt (fun tau ↦ finiteFourierReconstruction s
        (weightedCoefficients (weightPath tau) (etaPath tau)) (xPath tau))
      (movingFiniteFourierDerivative s
        (weightedCoefficients (weightPath t) (etaPath t))
        (evolvingWeightedCoefficientRate (weightPath t) weightDot
          (etaPath t) etaDot) phaseDot (xPath t)) t := by
  apply hasDerivAt_moving_finiteFourierReconstruction
  · intro q hq i
    exact hasDerivAt_evolvingWeightedCoefficient
      weightPath weightDot etaPath etaDot q i t (hw q hq) (he q hq i)
  · exact hx

theorem transportAmp_smul_receiver (k l : Wavevector)
    (u v : VelocityCoefficient) (a : ℂ) :
    unitTorusNegativeTransportAmp k l u (a • v) =
      a • unitTorusNegativeTransportAmp k l u v := by
  rw [unitTorusNegativeTransportAmp_eq, unitTorusNegativeTransportAmp_eq]
  exact smul_comm _ _ _

theorem stretchAmp_smul_receiver (k : Wavevector)
    (u v : VelocityCoefficient) (a : ℂ) :
    unitTorusStrainStretchAmp k u (a • v) =
      a • unitTorusStrainStretchAmp k u v := by
  rw [unitTorusStrainStretchAmp_eq_neg_complexStretchAmp,
    unitTorusStrainStretchAmp_eq_neg_complexStretchAmp]
  have h := complexStretchAmp_smul_smul k u v 1 a
  simpa using congrArg Neg.neg h

@[simp] theorem stretchAmp_zero_receiver (k : Wavevector)
    (u : VelocityCoefficient) : unitTorusStrainStretchAmp k u 0 = 0 := by
  simpa using stretchAmp_smul_receiver k u 0 0

/-- Nonlinear coefficient after weighting the output and subtracting the
transport and stretching of the weighted receiver field. -/
def weightedMaterialNonlinearCoeff
    (sourceModes receiverModes : Finset Wavevector)
    (weight : Wavevector → ℂ) (omega eta : FourierVelocity)
    (q : Wavevector) : VelocityCoefficient :=
  weight q • (finiteUnitTorusNegativeTransportCoeff
      sourceModes receiverModes omega eta q +
    finiteUnitTorusStretchingCoeff sourceModes receiverModes omega eta q) -
  (finiteUnitTorusNegativeTransportCoeff sourceModes receiverModes omega
      (weightedCoefficients weight eta) q +
    finiteUnitTorusStretchingCoeff sourceModes receiverModes omega
      (weightedCoefficients weight eta) q)

/-- Both physical nonlinear channels carry the same exact filter difference. -/
theorem weightedMaterialNonlinearCoeff_eq_difference
    (sourceModes receiverModes : Finset Wavevector)
    (weight : Wavevector → ℂ) (omega eta : FourierVelocity) (q : Wavevector) :
    weightedMaterialNonlinearCoeff sourceModes receiverModes weight omega eta q =
      ∑ k ∈ sourceModes, ∑ l ∈ receiverModes,
        if k + l = q then
          (weight q - weight l) •
            (unitTorusNegativeTransportAmp k l (omega k) (eta l) +
              unitTorusStrainStretchAmp k (omega k) (eta l))
        else 0 := by
  classical
  unfold weightedMaterialNonlinearCoeff
  simp only [finiteUnitTorusNegativeTransportCoeff_eq_doubleSum,
    finiteUnitTorusStretchingCoeff_eq_doubleSum, weightedCoefficients,
    transportAmp_smul_receiver, stretchAmp_smul_receiver,
    ← Finset.sum_add_distrib, Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  by_cases h : k + l = q
  · simp only [if_pos h, smul_add, sub_smul]
    abel
  · simp [h]

/-- The scalar-weighted commutator specializes to the existing hard-block
commutator, so the two residual descriptions refer to the same operation. -/
theorem weightedMaterialNonlinearCoeff_hard_selector
    (sourceModes receiverModes blockModes : Finset Wavevector)
    (omega eta : FourierVelocity) (q : Wavevector) :
    weightedMaterialNonlinearCoeff sourceModes receiverModes
        (fun k ↦ if k ∈ blockModes then 1 else 0) omega eta q =
      finiteMaterialNonlinearBoundaryCoeff
        sourceModes receiverModes blockModes omega eta q := by
  classical
  unfold weightedMaterialNonlinearCoeff finiteMaterialNonlinearBoundaryCoeff
    finiteMaterialTransportCommutatorCoeff finiteStretchingProjectionCommutatorCoeff
  have ht : finiteUnitTorusNegativeTransportCoeff sourceModes receiverModes omega
      (weightedCoefficients (fun k ↦ if k ∈ blockModes then 1 else 0) eta) q =
      finiteUnitTorusNegativeTransportCoeff sourceModes
        (receiverModesInside receiverModes blockModes) omega eta q := by
    rw [finiteUnitTorusNegativeTransportCoeff_eq_doubleSum,
      finiteUnitTorusNegativeTransportCoeff_eq_doubleSum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [receiverModesInside, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases h : l ∈ blockModes <;> by_cases hq : k + l = q <;>
      simp [weightedCoefficients, h, hq, unitTorusNegativeTransportAmp_eq]
  have hs : finiteUnitTorusStretchingCoeff sourceModes receiverModes omega
      (weightedCoefficients (fun k ↦ if k ∈ blockModes then 1 else 0) eta) q =
      finiteUnitTorusStretchingCoeff sourceModes
        (receiverModesInside receiverModes blockModes) omega eta q := by
    rw [finiteUnitTorusStretchingCoeff_eq_doubleSum,
      finiteUnitTorusStretchingCoeff_eq_doubleSum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [receiverModesInside, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases h : l ∈ blockModes <;> by_cases hq : k + l = q <;>
      simp [weightedCoefficients, h, hq]
  rw [ht, hs]
  by_cases hq : q ∈ blockModes <;> simp [hq] <;> abel

/-- The material residual produced by differentiating an evolving filter
and inserting the physical finite vorticity equation. -/
def evolvingFilterMaterialResidualCoeff
    (sourceModes receiverModes : Finset Wavevector)
    (weight weightDot : Wavevector → ℂ) (omega eta : FourierVelocity)
    (nu : ℝ) (q : Wavevector) : VelocityCoefficient :=
  evolvingWeightedCoefficientRate weight weightDot eta
      (finiteUnitTorusVorticityRHS sourceModes receiverModes omega eta nu) q -
    finiteUnitTorusNegativeTransportCoeff sourceModes receiverModes omega
      (weightedCoefficients weight eta) q -
    finiteUnitTorusStretchingCoeff sourceModes receiverModes omega
      (weightedCoefficients weight eta) q

/-- Filter motion, nonlinear boundary transfer, and viscosity are three
distinct exact terms; a time-varying frame cannot silently omit the first. -/
theorem evolvingFilterMaterialResidualCoeff_eq
    (sourceModes receiverModes : Finset Wavevector)
    (weight weightDot : Wavevector → ℂ) (omega eta : FourierVelocity)
    (nu : ℝ) (q : Wavevector) :
    evolvingFilterMaterialResidualCoeff
        sourceModes receiverModes weight weightDot omega eta nu q =
      weightDot q • eta q +
        weightedMaterialNonlinearCoeff sourceModes receiverModes weight omega eta q +
        weight q • unitTorusViscousVorticityCoeff nu eta q := by
  unfold evolvingFilterMaterialResidualCoeff evolvingWeightedCoefficientRate
    weightedMaterialNonlinearCoeff finiteUnitTorusVorticityRHS
    finiteUnitTorusNonstretchingCoeff
  simp only [smul_add]
  abel

end Mettapedia.FluidDynamics.NavierStokes.PancakeEvolvingFilter
