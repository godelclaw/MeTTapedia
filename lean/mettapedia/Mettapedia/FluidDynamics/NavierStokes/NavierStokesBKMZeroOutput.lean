import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMTargetTransfersApplications
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMTargetTransfersMillennium
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMTargetTransfersUniform
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityZeroOutput

/-!
# Zero-data operational consequences, zero-output transfers, and false unrepaired BKM target result.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- The unrepaired BKM continuation clause is directly inhabitable at zero
initial data: any finite-time witness with an integrable vorticity envelope may
be discarded in favor of the explicit global zero solution. -/
theorem ExplicitBKMContinuationClause_zero
    (ν T : ℝ) :
    ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitBKMContinuationClause
      (T := T) (ExplicitConcreteNavierStokesRegularityClause_zero ν)

/-- The repaired finite-energy BKM continuation clause is likewise directly
inhabitable at zero initial data. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_zero
    (ν T : ℝ) :
    ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyBKMContinuationClause
      (T := T) (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero ν)

/-- Clause-level operational consequence at zero initial data: applying a
BKM-style continuation clause to the canonical zero slab witness and its
explicit envelope data yields a global explicit output. -/
theorem ExplicitBKMContinuationClause_implies_zeroGlobalOutput
    {ν T : ℝ}
    (hClause : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  rcases zeroFiniteTimeRegularityWitness_exhibits_BKMContinuationPremise ν T with
    ⟨W, hEnv⟩
  exact hClause hν smoothInitialVelocityData_zero hdiv0 W hEnv

/-- Nontrivial operational pressure-gauge sanity check: a smaller-slab BKM
continuation clause can be applied to a larger zero witness after adding any
smooth time-only pressure gauge and restricting back down. -/
theorem ExplicitBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    {ν Tsmall Tlarge : ℝ}
    (hClause : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  have hEnv :
      ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
        vorticityEnvelopeOn
          (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT).velocity
          Tsmall Ω ∧
          integrableVorticityEnvelopeOn Ω Tsmall Bint :=
    zeroFiniteTimeRegularityWitness_addPressureOfZeroSpatialGradient_restrict_has_BKMEnvelope
      ν Tsmall Tlarge q hq hq_zero hT
  exact hClause hν smoothInitialVelocityData_zero hdiv0
    (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT) hEnv

/-- Time-only special case of the zero-data BKM clause-level
zero-spatial-gradient transport theorem. -/
theorem ExplicitBKMContinuationClause_implies_zeroGlobalOutput_timeOnlyPressure
    {ν Tsmall Tlarge : ℝ}
    (hClause : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hClause hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Constant-pressure special case of the BKM clause-level pressure-gauge
sanity check at zero initial data. -/
theorem ExplicitBKMContinuationClause_implies_zeroGlobalOutput_constantPressure
    {ν T : ℝ}
    (hClause : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (Tsmall := T) (Tlarge := T) hClause hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)
      le_rfl

/-- Operational consequence of the BKM-style target at zero initial data:
combining the BKM-to-uniform bridge with the zero-data uniform instantiation
gives an explicit global output for positive viscosity. -/
theorem ExplicitBKMContinuationTarget_implies_zeroGlobalOutput
    (hBKM : ExplicitBKMContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hClause : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T :=
    hBKM ν (0 : NSInitialVelocity) T
  exact ExplicitBKMContinuationClause_implies_zeroGlobalOutput hClause hν

/-- Target-level operational pressure-gauge sanity check on the unrepaired BKM
layer: the target applies on any smaller zero slab after adding a smooth
time-only pressure gauge on a larger zero witness and restricting back down. -/
theorem ExplicitBKMContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    (hBKM : ExplicitBKMContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hClause : ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) Tsmall :=
    hBKM ν (0 : NSInitialVelocity) Tsmall
  exact
    ExplicitBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hClause hν q hq hq_zero hT

/-- Time-only special case of the zero-data BKM target-level
zero-spatial-gradient transport theorem. -/
theorem ExplicitBKMContinuationTarget_implies_zeroGlobalOutput_timeOnlyPressure
    (hBKM : ExplicitBKMContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitBKMContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hBKM hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Constant-pressure special case of the BKM target-level pressure-gauge
sanity check at zero initial data. -/
theorem ExplicitBKMContinuationTarget_implies_zeroGlobalOutput_constantPressure
    (hBKM : ExplicitBKMContinuationTarget)
    {ν T : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitBKMContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (Tsmall := T) (Tlarge := T) hBKM hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)
      le_rfl

/-- The unrepaired BKM continuation target is false as stated. For a negative
horizon, nonzero linear shear admits a formal finite-time witness with a
vacuous BKM envelope on the empty slab, while the required global
bounded-energy output is already impossible on `ℝ^3`. -/
theorem not_ExplicitBKMContinuationTarget :
    ¬ ExplicitBKMContinuationTarget := by
  intro hBKM
  have hν : 0 < (1 : ℝ) := by positivity
  have hdiv :
      ∀ x, initialSpatialDivergence (linearShearInitialVelocity 1) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_linearShearInitialVelocity 1 x
  let W : ExplicitFiniteTimeRegularityWitness 1 (linearShearInitialVelocity 1) (-1) :=
    explicitFiniteTimeRegularityWitness_linearShearInitialVelocity_of_lt_zero
      (ν := 1) (T := -1) (a := 1) (by norm_num)
  have hΩ : vorticityEnvelopeOn W.velocity (-1) (fun _ : NSTime => 0) := by
    refine ⟨?_, ?_⟩
    · intro t ht0 htT
      exfalso
      linarith
    · intro t x ht0 htT
      exfalso
      linarith
  have hEnv :
      ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
        vorticityEnvelopeOn W.velocity (-1) Ω ∧
          integrableVorticityEnvelopeOn Ω (-1) Bint := by
    exact ⟨(fun _ : NSTime => 0), 0, hΩ, integrableVorticityEnvelopeOn_zero (-1)⟩
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearInitialVelocity one_ne_zero
      (hBKM 1 (linearShearInitialVelocity 1) (-1)
        hν
        (smoothInitialVelocityData_linearShearInitialVelocity 1)
        hdiv W hEnv)

/-- Clause-level operational consequence for the repaired finite-energy BKM
layer: zero initial data satisfy the repaired input hypothesis directly, so a
repaired BKM clause instance can be applied to the canonical zero slab witness
and its explicit envelope data without vacuity. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput
    {ν T : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  rcases zeroFiniteTimeRegularityWitness_exhibits_BKMContinuationPremise ν T with
    ⟨W, hEnv⟩
  exact hClause hν smoothInitialVelocityData_zero hdiv0 finiteInitialKineticEnergy_zero W hEnv

/-- Nontrivial operational pressure-gauge sanity check on the repaired
finite-energy BKM layer: a smaller-slab repaired clause can be applied to a
larger zero witness after adding any smooth time-only pressure gauge and
restricting back down. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    {ν Tsmall Tlarge : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  have hEnv :
      ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
        vorticityEnvelopeOn
          (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT).velocity
          Tsmall Ω ∧
          integrableVorticityEnvelopeOn Ω Tsmall Bint :=
    zeroFiniteTimeRegularityWitness_addPressureOfZeroSpatialGradient_restrict_has_BKMEnvelope
      ν Tsmall Tlarge q hq hq_zero hT
  exact hClause hν smoothInitialVelocityData_zero hdiv0 finiteInitialKineticEnergy_zero
    (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT) hEnv

/-- Time-only special case of the repaired zero-data BKM clause-level
zero-spatial-gradient transport theorem. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_timeOnlyPressure
    {ν Tsmall Tlarge : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hClause hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Constant-pressure special case of the repaired BKM clause-level
pressure-gauge sanity check at zero initial data. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_constantPressure
    {ν T : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (Tsmall := T) (Tlarge := T) hClause hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)
      le_rfl

/-- The repaired finite-energy BKM target is likewise operational at zero
initial data: the zero datum satisfies the repaired input hypothesis directly,
so the target applies to the canonical zero slab witness with its explicit BKM
envelope. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hClause : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T :=
    hBKM ν (0 : NSInitialVelocity) T
  exact ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput hClause hν

/-- Target-level repaired time-gauge sanity check: the repaired finite-energy
BKM target applies on any smaller zero slab after adding a smooth time-only
pressure gauge on a larger zero witness and restricting back down. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hClause : ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) Tsmall :=
    hBKM ν (0 : NSInitialVelocity) Tsmall
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hClause hν q hq hq_zero hT

/-- Time-only special case of the repaired zero-data BKM target-level
zero-spatial-gradient transport theorem. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput_timeOnlyPressure
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hBKM hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Constant-pressure special case of the repaired BKM target-level
pressure-gauge sanity check at zero initial data. -/
theorem ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput_constantPressure
    (hBKM : ExplicitFiniteEnergyBKMContinuationTarget)
    {ν T : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyBKMContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (Tsmall := T) (Tlarge := T) hBKM hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)
      le_rfl

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
