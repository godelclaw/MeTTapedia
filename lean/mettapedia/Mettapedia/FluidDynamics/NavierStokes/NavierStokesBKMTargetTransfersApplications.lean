import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMCandidatesConstant
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMCandidatesAffineShear
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMCandidatesHeatShear
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMCandidatesEnvelopeOperations
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityZeroWitness

/-!
# BKM Target Transfer Applications

This module contains application, monotonicity, and zero-witness baseline lemmas for BKM continuation clauses.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- A BKM continuation clause at horizon `T'` can be applied to any larger-slab
witness by restricting the witness and its explicit BKM data from `0 ≤ t ≤ T`
down to `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitBKMContinuationClause_apply_of_BKMEnvelope_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact hClause hν hsmooth hdiv (W.restrict hT) (W.BKMEnvelope_restrict hEnv hT)

/-- A BKM continuation clause can be applied equally well after changing the
witness by any smooth pressure gauge with zero spatial gradient, since the
explicit BKM data are pressure-invariant. -/
theorem ExplicitBKMContinuationClause_apply_of_BKMEnvelope_addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T)
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact hClause hν hsmooth hdiv
    (W.addPressureOfZeroSpatialGradient q hq hq_zero)
    (W.BKMEnvelope_addPressureOfZeroSpatialGradient hEnv q hq hq_zero)

/-- A BKM continuation clause can be applied equally well after changing the
witness by a smooth time-only pressure gauge, since the explicit BKM data are
pressure-invariant. -/
theorem ExplicitBKMContinuationClause_apply_of_BKMEnvelope_addTimeOnlyPressure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T)
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitBKMContinuationClause_apply_of_BKMEnvelope_addPressureOfZeroSpatialGradient
      (hClause := hClause) hν hsmooth hdiv W hEnv
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- A BKM continuation clause at horizon `T'` can also be applied after first
changing a larger-slab witness by a smooth zero-spatial-gradient pressure gauge
and then restricting to `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitBKMContinuationClause_apply_of_BKMEnvelope_addPressureOfZeroSpatialGradient_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact hClause hν hsmooth hdiv
    ((W.addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT)
    (W.BKMEnvelope_addPressureOfZeroSpatialGradient_restrict hEnv q hq hq_zero hT)

/-- A BKM continuation clause at horizon `T'` can also be applied after first
changing a larger-slab witness by a smooth time-only pressure gauge and then
restricting to `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitBKMContinuationClause_apply_of_BKMEnvelope_addTimeOnlyPressure_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitBKMContinuationClause_apply_of_BKMEnvelope_addPressureOfZeroSpatialGradient_restrict
      (hClause := hClause) hν hsmooth hdiv W hEnv
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- A BKM continuation clause at horizon `T'` can also be applied to a
larger-slab witness using only a uniform vorticity bound on the larger slab,
via the restricted uniform-to-BKM bridge. -/
theorem ExplicitBKMContinuationClause_apply_of_uniformVorticityBound_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  have hEnv :
      ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
        vorticityEnvelopeOn (W.restrict hT).velocity T' Ω ∧
          integrableVorticityEnvelopeOn Ω T' Bint := by
    simpa [ExplicitFiniteTimeRegularityWitness.restrict] using
      (uniformVorticityBoundUpTo_implies_BKMEnvelope_restrict
        (u := W.velocity) (T := T) (T' := T') (B := B) hω hT)
  exact hClause hν hsmooth hdiv (W.restrict hT) hEnv

/-- A BKM continuation clause can also be applied after changing a witness by
any smooth pressure gauge with zero spatial gradient, using only a uniform
vorticity bound on the same slab.  The pressure change leaves the velocity
unchanged, so the uniform bound still converts into explicit BKM data. -/
theorem ExplicitBKMContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity} {T B : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T)
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  have hEnv :
      ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
        vorticityEnvelopeOn (W.addPressureOfZeroSpatialGradient q hq hq_zero).velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T Bint := by
    exact
      uniformVorticityBoundUpTo_implies_BKMEnvelope
        (u := (W.addPressureOfZeroSpatialGradient q hq hq_zero).velocity) (T := T) (B := B)
        (W.uniformVorticityBound_addPressureOfZeroSpatialGradient hω q hq hq_zero)
  exact hClause hν hsmooth hdiv (W.addPressureOfZeroSpatialGradient q hq hq_zero) hEnv

/-- A BKM continuation clause can also be applied after changing a witness by a
smooth time-only pressure gauge, using only a uniform vorticity bound on the
same slab.  The pressure change leaves the velocity unchanged, so the uniform
bound still converts into explicit BKM data. -/
theorem ExplicitBKMContinuationClause_apply_of_uniformVorticityBound_addTimeOnlyPressure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T B : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T)
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitBKMContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient
      (hClause := hClause) hν hsmooth hdiv W hω
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- A BKM continuation clause at horizon `T'` can also be applied after first
changing a larger-slab witness by a smooth zero-spatial-gradient pressure gauge
and then using the resulting restricted uniform vorticity bound on
`0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitBKMContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  simpa [ExplicitFiniteTimeRegularityWitness.restrict,
    ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient] using
    (ExplicitBKMContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient
      (hClause := hClause) hν hsmooth hdiv (W := W.restrict hT)
      (hω := W.uniformVorticityBound_restrict hω hT) q hq hq_zero)

/-- A BKM continuation clause at horizon `T'` can also be applied after first
changing a larger-slab witness by a smooth time-only pressure gauge and then
using the resulting restricted uniform vorticity bound on `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitBKMContinuationClause_apply_of_uniformVorticityBound_addTimeOnlyPressure_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' B : ℝ}
    (hClause : ExplicitBKMContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact
    ExplicitBKMContinuationClause_apply_of_uniformVorticityBound_addPressureOfZeroSpatialGradient_restrict
      (hClause := hClause) hν hsmooth hdiv W hω
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Horizon monotonicity for the BKM-style continuation clause:
if the clause is available on a smaller slab `0 ≤ t ≤ Tsmall`, then it is also
available on every larger slab `0 ≤ t ≤ Tlarge` with `Tsmall ≤ Tlarge`, by
restricting the witness and its envelope data. -/
theorem ExplicitBKMContinuationClause_mono_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (hClauseSmall : ExplicitBKMContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitBKMContinuationClause ν u₀ Tlarge := by
  intro hν hsmooth hdiv W hEnv
  exact
    ExplicitBKMContinuationClause_apply_of_BKMEnvelope_restrict
      hClauseSmall hν hsmooth hdiv W hEnv hT

/-- A repaired BKM continuation clause at horizon `T'` can be applied to any
larger-slab witness by restricting the witness and its explicit BKM data from
`0 ≤ t ≤ T` down to `0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_apply_of_BKMEnvelope_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (hClause : ExplicitFiniteEnergyBKMContinuationClause ν u₀ T')
    (hν : 0 < ν)
    (hsmooth : smoothInitialVelocityData u₀)
    (hdiv : ∀ x, initialSpatialDivergence u₀ x = 0)
    (hfinite : finiteInitialKineticEnergy u₀)
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hT : T' ≤ T) :
    ExplicitConcreteNavierStokesGlobalOutput ν u₀ := by
  exact hClause hν hsmooth hdiv hfinite (W.restrict hT) (W.BKMEnvelope_restrict hEnv hT)

/-- Horizon monotonicity for the repaired BKM continuation clause:
if the clause is available on a smaller slab `0 ≤ t ≤ Tsmall`, then it is also
available on every larger slab `0 ≤ t ≤ Tlarge` with `Tsmall ≤ Tlarge`, by
restricting the witness and its envelope data. -/
theorem ExplicitFiniteEnergyBKMContinuationClause_mono_horizon
    {ν : ℝ} {u₀ : NSInitialVelocity} {Tsmall Tlarge : ℝ}
    (hClauseSmall : ExplicitFiniteEnergyBKMContinuationClause ν u₀ Tsmall)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitFiniteEnergyBKMContinuationClause ν u₀ Tlarge := by
  intro hν hsmooth hdiv hfinite W hEnv
  exact
    ExplicitFiniteEnergyBKMContinuationClause_apply_of_BKMEnvelope_restrict
      hClauseSmall hν hsmooth hdiv hfinite W hEnv hT

/-- The canonical zero slab witness carries a direct explicit BKM envelope:
`Ω(t) = 0`, with integral bound `B = 0`. -/
theorem zeroFiniteTimeRegularityWitness_has_BKMEnvelope
    (ν T : ℝ) :
    ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn (zeroFiniteTimeRegularityWitness ν T).velocity T Ω ∧
        integrableVorticityEnvelopeOn Ω T B := by
  refine ⟨fun _ => 0, 0, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [zeroFiniteTimeRegularityWitness] using (vorticityEnvelopeOn_zero T)
  · simpa using (integrableVorticityEnvelopeOn_zero T)

/-- The zero witness gives an honest inhabited premise for the concrete BKM
continuation clause on every slab.  This is the basic nonvacuity baseline that
contrasts with the impossible nonzero constant-initial-data cases. -/
theorem zeroFiniteTimeRegularityWitness_exhibits_BKMContinuationPremise
    (ν T : ℝ) :
    ∃ W : ExplicitFiniteTimeRegularityWitness ν (0 : NSInitialVelocity) T,
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B := by
  refine ⟨zeroFiniteTimeRegularityWitness ν T, ?_⟩
  exact zeroFiniteTimeRegularityWitness_has_BKMEnvelope ν T

/-- Concrete finite-slab BKM gauge baseline: after adding any smooth time-only
pressure to the zero witness on a larger slab and restricting to a shorter one,
the resulting witness still carries the explicit zero BKM envelope. -/
theorem zeroFiniteTimeRegularityWitness_addPressureOfZeroSpatialGradient_restrict_has_BKMEnvelope
    (ν Tsmall Tlarge : ℝ)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn
          (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT).velocity
          Tsmall Ω ∧
        integrableVorticityEnvelopeOn Ω Tsmall B := by
  exact
    (zeroFiniteTimeRegularityWitness ν Tlarge).BKMEnvelope_addPressureOfZeroSpatialGradient_restrict
      (zeroFiniteTimeRegularityWitness_has_BKMEnvelope ν Tlarge)
      q hq hq_zero hT

/-- Time-only special case of the zero-data zero-spatial-gradient BKM gauge
baseline on restricted slabs. -/
theorem zeroFiniteTimeRegularityWitness_addTimeOnlyPressure_restrict_has_BKMEnvelope
    (ν Tsmall Tlarge : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn
          (((zeroFiniteTimeRegularityWitness ν Tlarge).addTimeOnlyPressure π hπ).restrict hT).velocity
          Tsmall Ω ∧
        integrableVorticityEnvelopeOn Ω Tsmall B := by
  exact
    zeroFiniteTimeRegularityWitness_addPressureOfZeroSpatialGradient_restrict_has_BKMEnvelope
      ν Tsmall Tlarge
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
