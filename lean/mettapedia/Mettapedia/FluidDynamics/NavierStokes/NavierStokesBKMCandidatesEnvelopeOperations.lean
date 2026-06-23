import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMConcreteEnvelopes
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityPressureGauge

/-!
# Witness-level BKM envelope operations
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- Witness-level bridge from uniform linear-combination control on a large slab
to explicit BKM-envelope data on a shorter slab. -/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_linearCombination_implies_BKMEnvelope_restrict
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T T' B B' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (hω' : uniformVorticityBoundUpTo W'.velocity T B')
    (a b : ℝ)
    (hT : T' ≤ T) :
    ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
      vorticityEnvelopeOn
          (a • (W.restrict hT).velocity + b • (W'.restrict hT).velocity) T' Ω ∧
        integrableVorticityEnvelopeOn Ω T' Bint := by
  simpa [ExplicitFiniteTimeRegularityWitness.restrict] using
    (uniformVorticityBoundUpTo_linearCombination_implies_BKMEnvelope_restrict
      (u := W.velocity) (v := W'.velocity) (T := T) (T' := T')
      W.smooth_velocity W'.smooth_velocity hω hω' a b hT)

/-- Witness-level bridge from uniform linear-combination control on a large slab
to the explicit constant BKM envelope on a nonnegative shorter slab. -/
theorem ExplicitFiniteTimeRegularityWitness.uniformVorticityBound_linearCombination_implies_constantBKMEnvelope_restrict
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T T' B B' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hT' : 0 ≤ T')
    (hω : uniformVorticityBoundUpTo W.velocity T B)
    (hω' : uniformVorticityBoundUpTo W'.velocity T B')
    (a b : ℝ)
    (hT : T' ≤ T) :
    vorticityEnvelopeOn
        (a • (W.restrict hT).velocity + b • (W'.restrict hT).velocity) T'
        (fun _ : NSTime => |a| * B + |b| * B') ∧
      integrableVorticityEnvelopeOn
        (fun _ : NSTime => |a| * B + |b| * B') T'
        (T' * (|a| * B + |b| * B')) := by
  simpa [ExplicitFiniteTimeRegularityWitness.restrict] using
    (uniformVorticityBoundUpTo_linearCombination_implies_constantBKMEnvelope_restrict
      (u := W.velocity) (v := W'.velocity) (T := T) (T' := T')
      hT' W.smooth_velocity W'.smooth_velocity hω hω' a b hT)

/-- BKM envelope data transport along witness restriction from `T` to `T' ≤ T`.
-/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hT : T' ≤ T) :
    ∃ Ω : NSTime → ℝ, ∃ B' : ℝ,
      vorticityEnvelopeOn (W.restrict hT).velocity T' Ω ∧
        integrableVorticityEnvelopeOn Ω T' B' := by
  rcases hEnv with ⟨Ω, B, hV, hI⟩
  refine ⟨Ω, ∫ t in Set.Icc 0 T', Ω t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [ExplicitFiniteTimeRegularityWitness.restrict] using
      (vorticityEnvelopeOn_restrict (u := W.velocity) (T := T) (T' := T') (Ω := Ω) hV hT)
  · exact hV.integrable_restrict (hInt := hI) hT

/-- BKM envelope data are unchanged under adding any smooth pressure gauge with
zero spatial gradient on each slice, since the velocity field is unchanged. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_addPressureOfZeroSpatialGradient
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0) :
    ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn (W.addPressureOfZeroSpatialGradient q hq hq_zero).velocity T Ω ∧
        integrableVorticityEnvelopeOn Ω T B := by
  simpa [ExplicitFiniteTimeRegularityWitness.addPressureOfZeroSpatialGradient] using hEnv

/-- BKM envelope data are unchanged under adding a smooth time-only pressure
gauge to the witness, since the velocity field is unchanged. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_addTimeOnlyPressure
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn (W.addTimeOnlyPressure π hπ).velocity T Ω ∧
        integrableVorticityEnvelopeOn Ω T B := by
  exact
    W.BKMEnvelope_addPressureOfZeroSpatialGradient hEnv
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)

/-- BKM envelope data remain available after adding a smooth zero-spatial-gradient
pressure gauge and then restricting to a shorter slab. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_addPressureOfZeroSpatialGradient_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : T' ≤ T) :
    ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn ((W.addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT).velocity T' Ω ∧
        integrableVorticityEnvelopeOn Ω T' B := by
  exact
    (W.addPressureOfZeroSpatialGradient q hq hq_zero).BKMEnvelope_restrict
      (W.BKMEnvelope_addPressureOfZeroSpatialGradient hEnv q hq hq_zero) hT

/-- BKM envelope data remain available after adding a smooth time-only pressure
gauge and then restricting to a shorter slab. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_addTimeOnlyPressure_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : T' ≤ T) :
    ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn ((W.addTimeOnlyPressure π hπ).restrict hT).velocity T' Ω ∧
        integrableVorticityEnvelopeOn Ω T' B := by
  exact
    W.BKMEnvelope_addPressureOfZeroSpatialGradient_restrict hEnv
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Witness-level transport of BKM-envelope data under addition of velocities:
if two finite-time witnesses carry explicit BKM data on the same slab, then the
sum of their velocity fields carries explicit BKM data on that slab as well. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_add
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hEnv' :
      ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
        vorticityEnvelopeOn W'.velocity T Ω' ∧
          integrableVorticityEnvelopeOn Ω' T B') :
    ∃ Ω'' : NSTime → ℝ, ∃ B'' : ℝ,
      vorticityEnvelopeOn (W.velocity + W'.velocity) T Ω'' ∧
        integrableVorticityEnvelopeOn Ω'' T B'' := by
  rcases hEnv with ⟨Ω, B, hΩ, hInt⟩
  rcases hEnv' with ⟨Ω', B', hΩ', hInt'⟩
  refine ⟨fun t => Ω t + Ω' t, B + B', ?_⟩
  exact BKMEnvelopeData_add_of_smooth
    W.smooth_velocity W'.smooth_velocity hΩ hInt hΩ' hInt'

/-- Witness-level transport of BKM-envelope data under addition followed by
restriction to a shorter slab `0 ≤ t ≤ T'` with `T' ≤ T`. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_add_restrict
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hEnv' :
      ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
        vorticityEnvelopeOn W'.velocity T Ω' ∧
          integrableVorticityEnvelopeOn Ω' T B')
    (hT : T' ≤ T) :
    ∃ Ω'' : NSTime → ℝ, ∃ B'' : ℝ,
      vorticityEnvelopeOn (W.velocity + W'.velocity) T' Ω'' ∧
        integrableVorticityEnvelopeOn Ω'' T' B'' := by
  rcases W.BKMEnvelope_add W' hEnv hEnv' with ⟨Ω'', _B, hV, hI⟩
  refine ⟨Ω'', ∫ t in Set.Icc 0 T', Ω'' t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ?_⟩
  exact BKMEnvelopeData_restrict hV hI hT

/-- Witness-level transport of BKM-envelope data under constant rescaling of
the velocity field. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_const_smul
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (a : ℝ) :
    ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
      vorticityEnvelopeOn (a • W.velocity) T Ω' ∧
        integrableVorticityEnvelopeOn Ω' T B' := by
  rcases hEnv with ⟨Ω, B, hΩ, hInt⟩
  refine ⟨fun t => |a| * Ω t, |a| * B, ?_⟩
  exact ⟨vorticityEnvelopeOn_const_smul (a := a) hΩ,
    integrableVorticityEnvelopeOn_abs_const_smul (a := a) hInt⟩

/-- Witness-level transport of BKM-envelope data under constant rescaling
followed by restriction to a shorter slab `0 ≤ t ≤ T'` with `T' ≤ T`. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_const_smul_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (a : ℝ)
    (hT : T' ≤ T) :
    ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
      vorticityEnvelopeOn (a • W.velocity) T' Ω' ∧
        integrableVorticityEnvelopeOn Ω' T' B' := by
  rcases W.BKMEnvelope_const_smul hEnv a with ⟨Ω', _B, hV, hI⟩
  refine ⟨Ω', ∫ t in Set.Icc 0 T', Ω' t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ?_⟩
  exact BKMEnvelopeData_restrict hV hI hT

/-- Witness-level transport of BKM-envelope data under sign flip of the
velocity field. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_neg
    {ν : ℝ} {u₀ : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B) :
    ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
        vorticityEnvelopeOn (-W.velocity) T Ω' ∧
        integrableVorticityEnvelopeOn Ω' T B' := by
  simpa using W.BKMEnvelope_const_smul hEnv (-1 : ℝ)

/-- Witness-level transport of BKM-envelope data under sign flip followed by
restriction to a shorter slab `0 ≤ t ≤ T'` with `T' ≤ T`. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_neg_restrict
    {ν : ℝ} {u₀ : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hT : T' ≤ T) :
    ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
      vorticityEnvelopeOn (-W.velocity) T' Ω' ∧
        integrableVorticityEnvelopeOn Ω' T' B' := by
  simpa using W.BKMEnvelope_const_smul_restrict hEnv (-1 : ℝ) hT

/-- Witness-level transport of BKM-envelope data under subtraction of
velocities: if two finite-time witnesses carry explicit BKM data on the same
slab, then the difference of their velocity fields carries explicit BKM data on
that slab as well. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_sub
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hEnv' :
      ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
        vorticityEnvelopeOn W'.velocity T Ω' ∧
          integrableVorticityEnvelopeOn Ω' T B') :
    ∃ Ω'' : NSTime → ℝ, ∃ B'' : ℝ,
      vorticityEnvelopeOn (W.velocity - W'.velocity) T Ω'' ∧
        integrableVorticityEnvelopeOn Ω'' T B'' := by
  rcases hEnv with ⟨Ω, B, hΩ, hInt⟩
  rcases hEnv' with ⟨Ω', B', hΩ', hInt'⟩
  refine ⟨fun t => Ω t + Ω' t, B + B', ?_⟩
  exact BKMEnvelopeData_sub_of_smooth
    W.smooth_velocity W'.smooth_velocity hΩ hInt hΩ' hInt'

/-- Witness-level transport of BKM-envelope data under subtraction followed by
restriction to a shorter slab `0 ≤ t ≤ T'` with `T' ≤ T`. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_sub_restrict
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hEnv' :
      ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
        vorticityEnvelopeOn W'.velocity T Ω' ∧
          integrableVorticityEnvelopeOn Ω' T B')
    (hT : T' ≤ T) :
    ∃ Ω'' : NSTime → ℝ, ∃ B'' : ℝ,
      vorticityEnvelopeOn (W.velocity - W'.velocity) T' Ω'' ∧
        integrableVorticityEnvelopeOn Ω'' T' B'' := by
  rcases W.BKMEnvelope_sub W' hEnv hEnv' with ⟨Ω'', _B, hV, hI⟩
  refine ⟨Ω'', ∫ t in Set.Icc 0 T', Ω'' t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ?_⟩
  exact BKMEnvelopeData_restrict hV hI hT

/-- Witness-level BKM package for a linear combination on a smaller slab:
explicit BKM data for `W.velocity` and `W'.velocity` on `0 ≤ t ≤ T` induce
explicit BKM data for `a • W.velocity + b • W'.velocity` on every shorter slab
`0 ≤ t ≤ T' ≤ T`. -/
theorem ExplicitFiniteTimeRegularityWitness.BKMEnvelope_linearCombination_restrict
    {ν ν' : ℝ} {u₀ u₀' : NSInitialVelocity} {T T' : ℝ}
    (W : ExplicitFiniteTimeRegularityWitness ν u₀ T)
    (W' : ExplicitFiniteTimeRegularityWitness ν' u₀' T)
    (hEnv :
      ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
        vorticityEnvelopeOn W.velocity T Ω ∧
          integrableVorticityEnvelopeOn Ω T B)
    (hEnv' :
      ∃ Ω' : NSTime → ℝ, ∃ B' : ℝ,
        vorticityEnvelopeOn W'.velocity T Ω' ∧
          integrableVorticityEnvelopeOn Ω' T B')
    (a b : ℝ)
    (hT : T' ≤ T) :
    ∃ Ω'' : NSTime → ℝ, ∃ B'' : ℝ,
      vorticityEnvelopeOn (a • W.velocity + b • W'.velocity) T' Ω'' ∧
        integrableVorticityEnvelopeOn Ω'' T' B'' := by
  rcases hEnv with ⟨Ω, B, hΩ, hInt⟩
  rcases hEnv' with ⟨Ω', B', hΩ', hInt'⟩
  refine ⟨fun t => |a| * Ω t + |b| * Ω' t,
    ∫ t in Set.Icc 0 T', (|a| * Ω t + |b| * Ω' t)
      ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ?_⟩
  exact BKMEnvelopeData_linearCombination_restrict_of_smooth
    W.smooth_velocity W'.smooth_velocity hΩ hInt hΩ' hInt' a b hT

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
