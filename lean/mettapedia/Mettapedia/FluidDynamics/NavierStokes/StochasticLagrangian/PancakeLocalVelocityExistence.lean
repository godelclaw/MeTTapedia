import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFiniteVelocityInvariant

/-!
# Constructed local retained velocity solutions

Picard--Lindelöf is applied to the actual physical invariant subspace.
The output curve supplies the coefficient equation, reality and transversality;
none is assumed of a previously supplied evolution. The lifespan here may
depend on the finite mode set.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalVelocityExistence

open scoped BigOperators ComplexConjugate ContDiff
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeBlockReality
open PancakeGalerkinKineticEnergy PancakeFiniteLocalizedEvolution
open PancakeFiniteVelocitySmooth PancakeFiniteVelocityInvariant
open PancakeFrequencyProjectorCommutator

/-- A local solution of the existing retained physical equation. Initial
data are truncated to the retained set; excluded initial modes are not preserved. -/
structure LocalVelocitySolution (M : Finset Wavevector) (nu : ℝ)
    (u₀ : FourierVelocity) (T : ℝ) where
  coefficients : ℝ → FourierVelocity
  initial : ∀ q ∈ M, coefficients 0 q = u₀ q
  support : ∀ t q, q ∉ M → coefficients t q = 0
  reality : ∀ t q, coefficients t (-q) = coefficientConjugate (coefficients t q)
  transverse : ∀ t q, q ∈ M → modeDot q (coefficients t q) = 0
  equation : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ M, ∀ i,
    HasDerivAt (fun tau ↦ coefficients tau q i) (velocityRHS M (coefficients t) nu q i) t

theorem restrictCoefficients_mem_physical (M : Finset Wavevector) (u₀ : FourierVelocity)
    (hs : ∀ q, -q ∈ M ↔ q ∈ M)
    (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q ∈ M, modeDot q (u₀ q) = 0) :
    restrictCoefficients M u₀ ∈ physicalSubspace M := by
  constructor
  · intro q
    exact hd q q.2
  · intro q
    ext i
    by_cases hq : q ∈ M
    · have hn := (hs q).mpr hq
      simpa [extendCoefficients, restrictCoefficients, hq, hn, coefficientConjugate] using
        congrFun (hr q) i
    · have hn : -q ∉ M := fun h ↦ hq ((hs q).mp h)
      simp [extendCoefficients, hq, hn, coefficientConjugate]

theorem hasDerivAt_extended_physical_curve (M : Finset Wavevector) (nu : ℝ)
    (hs : ∀ q, -q ∈ M ↔ q ∈ M) (hk : ∀ q ∈ M, frequencyVec q ≠ 0)
    (a : ℝ → physicalSubspace M) (t : ℝ)
    (ha : HasDerivAt a (physicalVelocityRHS M nu (a t)) t)
    (q : Wavevector) (hq : q ∈ M) (i : Fin 3) :
    HasDerivAt (fun tau ↦ extendCoefficients M (a tau) q i)
      (velocityRHS M (extendCoefficients M (a t)) nu q i) t := by
  have hv := (physicalSubspace M).subtypeL.hasFDerivAt.comp_hasDerivAt t ha
  have hproj := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : M × Fin 3 ↦ ℂ) (⟨q, hq⟩, i)).hasFDerivAt.comp_hasDerivAt t hv
  have he := physicalVelocityRHS_coe M nu hs hk (a t)
  change HasDerivAt (fun tau ↦ (a tau).val (⟨q, hq⟩, i))
    ((physicalVelocityRHS M nu (a t)).val (⟨q, hq⟩, i)) t at hproj
  simpa [extendCoefficients, hq, he, finiteVelocityRHS, restrictCoefficients] using hproj

/-- Arbitrary physical initial coefficients produce an actual positive-time
solution, with all physical constraints preserved by construction. -/
theorem exists_localVelocitySolution (M : Finset Wavevector) (nu : ℝ)
    (u₀ : FourierVelocity) (hs : ∀ q, -q ∈ M ↔ q ∈ M)
    (hk : ∀ q ∈ M, frequencyVec q ≠ 0)
    (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q ∈ M, modeDot q (u₀ q) = 0) :
    ∃ T > (0 : ℝ), Nonempty (LocalVelocitySolution M nu u₀ T) := by
  let v₀ : physicalSubspace M :=
    ⟨restrictCoefficients M u₀, restrictCoefficients_mem_physical M u₀ hs hr hd⟩
  have hc : ContDiffAt ℝ 1 (physicalVelocityRHS M nu) v₀ :=
    (contDiff_physicalVelocityRHS M nu).contDiffAt.of_le (by norm_num)
  obtain ⟨a, ha0, ε, hε, ha⟩ :=
    hc.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  refine ⟨ε / 2, by linarith, ⟨{
    coefficients := fun t ↦ extendCoefficients M (a t)
    initial := ?_
    support := ?_
    reality := fun t ↦ (a t).2.2
    transverse := ?_
    equation := ?_
  }⟩⟩
  · intro q hq
    rw [ha0]
    ext i
    simp [v₀, extendCoefficients, hq]
  · intro t q hq
    ext i
    simp [extendCoefficients, hq]
  · intro t q hq
    simpa [modeDot, extendCoefficients, hq] using (a t).2.1 ⟨q, hq⟩
  · intro t ht q hq i
    apply hasDerivAt_extended_physical_curve M nu hs hk a t _ q hq i
    apply ha t
    constructor <;> linarith [ht.1, ht.2]

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalVelocityExistence
