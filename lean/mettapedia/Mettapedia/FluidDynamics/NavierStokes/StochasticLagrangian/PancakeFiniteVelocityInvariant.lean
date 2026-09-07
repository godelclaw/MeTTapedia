import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFiniteVelocitySmooth

/-!
# Physical invariant subspace of the retained velocity equation

Reality and incompressibility define a real linear subspace. The actual
velocity vector field preserves it on a negation-symmetric nonzero mode set.
An orthogonal projection is used only to give a smooth codomain restriction;
on this subspace it is proved to change no coefficient of the equation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeFiniteVelocityInvariant

open scoped BigOperators ComplexConjugate ContDiff
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeBlockReality PancakeGalerkinKineticEnergy
open PancakeFiniteLocalizedEvolution PancakeFiniteVelocitySmooth
open PancakeFrequencyProjectorCommutator

theorem extendCoefficients_add (M : Finset Wavevector) (v w : FiniteField M) :
    extendCoefficients M (v + w) = extendCoefficients M v + extendCoefficients M w := by
  funext q i
  by_cases hq : q ∈ M <;> simp [extendCoefficients, hq]

theorem extendCoefficients_smul (M : Finset Wavevector) (r : ℝ) (v : FiniteField M) :
    extendCoefficients M (r • v) = r • extendCoefficients M v := by
  funext q i
  by_cases hq : q ∈ M <;> simp [extendCoefficients, hq]

/-- Coefficients of real divergence-free finite fields. -/
def physicalSubspace (M : Finset Wavevector) : Submodule ℝ (FiniteField M) where
  carrier := {v | (∀ q : M, modeDot q (fun i ↦ v (q, i)) = 0) ∧
    ∀ q, extendCoefficients M v (-q) = coefficientConjugate (extendCoefficients M v q)}
  zero_mem' := by
    constructor
    · intro q; simp [modeDot]
    · intro q; ext i; simp [extendCoefficients, coefficientConjugate]
  add_mem' := by
    rintro v w ⟨hv, hvr⟩ ⟨hw, hwr⟩
    constructor
    · intro q
      change modeDot q ((fun i ↦ v (q, i)) + (fun i ↦ w (q, i))) = 0
      simpa [modeDot, mul_add, Finset.sum_add_distrib] using congrArg₂ (· + ·) (hv q) (hw q)
    · intro q
      rw [extendCoefficients_add]
      ext i
      have hvri := congrFun (hvr q) i
      have hwri := congrFun (hwr q) i
      simpa [coefficientConjugate] using congrArg₂ (· + ·) hvri hwri
  smul_mem' := by
    rintro r v ⟨hv, hvr⟩
    constructor
    · intro q
      change modeDot q ((r : ℂ) • (fun i ↦ v (q, i))) = 0
      rw [modeDot_smul, hv, mul_zero]
    · intro q
      rw [extendCoefficients_smul]
      ext i
      have h := congrFun (hvr q) i
      simpa [coefficientConjugate, Complex.real_smul] using congrArg (fun z : ℂ ↦ (r : ℂ) * z) h

theorem lerayMode_neg_conjugate (q : Wavevector) (v : VelocityCoefficient) :
    lerayMode (-q) (coefficientConjugate v) = coefficientConjugate (lerayMode q v) := by
  by_cases hq : modeSquare q = 0
  · simp [lerayMode, modeSquare_neg, hq]
  · ext i
    simp only [lerayMode, modeSquare_neg, hq, dite_false, coefficientConjugate_apply]
    simp [modeDot, modeSquare, map_sum, map_mul, map_sub]

theorem velocityRHS_real (M : Finset Wavevector) (nu : ℝ) (u : FourierVelocity)
    (hs : ∀ q, -q ∈ M ↔ q ∈ M)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (q : Wavevector) :
    velocityRHS M u nu (-q) = coefficientConjugate (velocityRHS M u nu q) := by
  rw [velocityRHS, finiteUnitTorusNegativeTransportCoeff_neg_conjugate M M hs hs
    (fourierCurl u) u (fourierCurl_real u hr) hr, lerayMode_neg_conjugate,
    unitTorusViscousVorticityCoeff_neg_conjugate nu u hr]
  ext i
  simp [velocityRHS, coefficientConjugate]

theorem velocityRHS_transverse (M : Finset Wavevector) (nu : ℝ)
    (u : FourierVelocity) (q : Wavevector) (hq : frequencyVec q ≠ 0)
    (hu : modeDot q (u q) = 0) : modeDot q (velocityRHS M u nu q) = 0 := by
  have hp := modeDot_lerayMode_eq_zero q
    (finiteUnitTorusNegativeTransportCoeff M M (fourierCurl u) u q)
    (modeSquare_ne_zero_of_frequencyVec_ne_zero hq)
  have hv : modeDot q (unitTorusViscousVorticityCoeff nu u q) = 0 := by
    rw [unitTorusViscousVorticityCoeff, modeDot_smul, hu, mul_zero]
  simpa [velocityRHS, modeDot, mul_add, Finset.sum_add_distrib] using
    congrArg₂ (· + ·) hp hv

theorem finiteVelocityRHS_mem (M : Finset Wavevector) (nu : ℝ)
    (hs : ∀ q, -q ∈ M ↔ q ∈ M) (hk : ∀ q ∈ M, frequencyVec q ≠ 0)
    (v : physicalSubspace M) : finiteVelocityRHS M nu v ∈ physicalSubspace M := by
  constructor
  · intro q
    exact velocityRHS_transverse M nu (extendCoefficients M v) q (hk q q.2)
      (by simpa [modeDot, extendCoefficients, q.2] using v.2.1 q)
  · intro q
    by_cases hq : q ∈ M
    · have hn := (hs q).mpr hq
      ext i
      simpa [finiteVelocityRHS, extendCoefficients, hq, hn, restrictCoefficients,
        coefficientConjugate] using
        congrFun (velocityRHS_real M nu (extendCoefficients M v) hs v.2.2 q) i
    · have hn : -q ∉ M := fun h ↦ hq ((hs q).mp h)
      ext i
      simp [extendCoefficients, hq, hn, coefficientConjugate]

/-- Smooth codomain restriction. On physical mode sets, the following
identity proves that the projection inserts no additional dynamics. -/
def physicalVelocityRHS (M : Finset Wavevector) (nu : ℝ) :
    physicalSubspace M → physicalSubspace M :=
  fun v ↦ (physicalSubspace M).orthogonalProjectionOnto (finiteVelocityRHS M nu v)

theorem physicalVelocityRHS_coe (M : Finset Wavevector) (nu : ℝ)
    (hs : ∀ q, -q ∈ M ↔ q ∈ M) (hk : ∀ q ∈ M, frequencyVec q ≠ 0)
    (v : physicalSubspace M) :
    (physicalVelocityRHS M nu v : FiniteField M) = finiteVelocityRHS M nu v := by
  have h := (physicalSubspace M).orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨finiteVelocityRHS M nu v, finiteVelocityRHS_mem M nu hs hk v⟩
  exact congrArg Subtype.val h

theorem contDiff_physicalVelocityRHS (M : Finset Wavevector) (nu : ℝ) :
    ContDiff ℝ ∞ (physicalVelocityRHS M nu) :=
  (physicalSubspace M).orthogonalProjectionOnto.contDiff.comp
    ((contDiff_finiteVelocityRHS M nu).comp (physicalSubspace M).subtypeL.contDiff)

end Mettapedia.FluidDynamics.NavierStokes.PancakeFiniteVelocityInvariant
