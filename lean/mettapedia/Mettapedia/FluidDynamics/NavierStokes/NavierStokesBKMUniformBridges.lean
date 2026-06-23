import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMContinuationCore
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityBounds

/-!
# Uniform-vorticity-bound bridges into explicit BKM envelope data.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

/-- A uniform slab vorticity bound yields an explicit integrable BKM envelope by
taking `Ω` constant in time. -/
theorem uniformVorticityBoundUpTo_implies_BKMEnvelope
    {u : NSVelocityField} {T B : ℝ}
    (hω : uniformVorticityBoundUpTo u T B) :
    ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
      vorticityEnvelopeOn u T Ω ∧
        integrableVorticityEnvelopeOn Ω T Bint := by
  rcases hω with ⟨hB, hbound⟩
  refine ⟨fun _ => B, ∫ t in Set.Icc 0 T, B ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro t ht0 htT
      simpa using hB
    · intro t x ht0 htT
      simpa using hbound t x ht0 htT
  · refine ⟨?_, ?_, ?_⟩
    · exact MeasureTheory.integral_nonneg (fun _ => hB)
    · have hs : (MeasureTheory.volume (Set.Icc 0 T)) ≠ (⊤ : ENNReal) := by
        rw [Real.volume_Icc]
        exact ne_of_lt ENNReal.ofReal_lt_top
      exact
        (MeasureTheory.integrableOn_const (s := Set.Icc 0 T)
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (C := B) (hs := hs))
    · change
        (∫ t in Set.Icc 0 T, B ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) ≤
          ∫ t in Set.Icc 0 T, B ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
      exact le_rfl

/-- On a nonnegative slab, a uniform vorticity bound yields the explicit
constant BKM envelope `Ω(t) = B` with linear integral bound `T * B`. -/
theorem uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    {u : NSVelocityField} {T B : ℝ}
    (hT : 0 ≤ T)
    (hω : uniformVorticityBoundUpTo u T B) :
    vorticityEnvelopeOn u T (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T (T * B) := by
  rcases hω with ⟨hB, hbound⟩
  refine ⟨?_, integrableVorticityEnvelopeOn_const hT hB⟩
  refine ⟨?_, ?_⟩
  · intro t ht0 htT'
    simpa using hB
  · intro t x ht0 htT'
    simpa using hbound t x ht0 htT'

/-- Two smooth uniform slab bounds combine into one explicit BKM envelope for
the summed field. -/
theorem uniformVorticityBoundUpTo_add_implies_BKMEnvelope
    {u v : NSVelocityField} {T B B' : ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B') :
    ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
      vorticityEnvelopeOn (u + v) T Ω ∧
        integrableVorticityEnvelopeOn Ω T Bint := by
  exact uniformVorticityBoundUpTo_implies_BKMEnvelope
    (u := u + v) (T := T) (B := B + B')
    (uniformVorticityBoundUpTo_add hu hv hω hω')

/-- On a nonnegative slab, two smooth uniform slab bounds combine into the
explicit constant BKM envelope for the summed field. -/
theorem uniformVorticityBoundUpTo_add_implies_constantBKMEnvelope
    {u v : NSVelocityField} {T B B' : ℝ}
    (hT : 0 ≤ T)
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B') :
    vorticityEnvelopeOn (u + v) T (fun _ : NSTime => B + B') ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B + B') T (T * (B + B')) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := u + v) (T := T) (B := B + B') hT
    (uniformVorticityBoundUpTo_add hu hv hω hω')

/-- Two smooth uniform slab bounds combine into explicit BKM-envelope data for
the difference field `u - v`. -/
theorem uniformVorticityBoundUpTo_sub_implies_BKMEnvelope
    {u v : NSVelocityField} {T B B' : ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B') :
    ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
      vorticityEnvelopeOn (u - v) T Ω ∧
        integrableVorticityEnvelopeOn Ω T Bint := by
  exact uniformVorticityBoundUpTo_implies_BKMEnvelope
    (u := u - v) (T := T) (B := B + B')
    (uniformVorticityBoundUpTo_sub hu hv hω hω')

/-- On a nonnegative slab, two smooth uniform slab bounds combine into the
explicit constant BKM envelope for the difference field `u - v`. -/
theorem uniformVorticityBoundUpTo_sub_implies_constantBKMEnvelope
    {u v : NSVelocityField} {T B B' : ℝ}
    (hT : 0 ≤ T)
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B') :
    vorticityEnvelopeOn (u - v) T (fun _ : NSTime => B + B') ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B + B') T (T * (B + B')) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := u - v) (T := T) (B := B + B') hT
    (uniformVorticityBoundUpTo_sub hu hv hω hω')

/-- Two smooth uniform slab bounds combine into explicit BKM-envelope data for
the linear combination `a • u + b • v`. -/
theorem uniformVorticityBoundUpTo_linearCombination_implies_BKMEnvelope
    {u v : NSVelocityField} {T B B' : ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B')
    (a b : ℝ) :
    ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
      vorticityEnvelopeOn (a • u + b • v) T Ω ∧
        integrableVorticityEnvelopeOn Ω T Bint := by
  exact uniformVorticityBoundUpTo_implies_BKMEnvelope
    (u := a • u + b • v) (T := T) (B := |a| * B + |b| * B')
    (uniformVorticityBoundUpTo_linearCombination hu hv hω hω' a b)

/-- On a nonnegative slab, two smooth uniform slab bounds combine into the
explicit constant BKM envelope for the linear combination `a • u + b • v`. -/
theorem uniformVorticityBoundUpTo_linearCombination_implies_constantBKMEnvelope
    {u v : NSVelocityField} {T B B' : ℝ}
    (hT : 0 ≤ T)
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B')
    (a b : ℝ) :
    vorticityEnvelopeOn (a • u + b • v) T
        (fun _ : NSTime => |a| * B + |b| * B') ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => |a| * B + |b| * B') T
        (T * (|a| * B + |b| * B')) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := a • u + b • v) (T := T) (B := |a| * B + |b| * B') hT
    (uniformVorticityBoundUpTo_linearCombination hu hv hω hω' a b)

/-- The uniform-to-BKM envelope conversion also restricts to any shorter slab. -/
theorem uniformVorticityBoundUpTo_implies_BKMEnvelope_restrict
    {u : NSVelocityField} {T T' B : ℝ}
    (hω : uniformVorticityBoundUpTo u T B)
    (hT : T' ≤ T) :
    ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
      vorticityEnvelopeOn u T' Ω ∧
        integrableVorticityEnvelopeOn Ω T' Bint := by
  rcases uniformVorticityBoundUpTo_implies_BKMEnvelope (u := u) (T := T) (B := B) hω with
    ⟨Ω, Bint, hEnv, hInt⟩
  refine ⟨Ω, |∫ t in Set.Icc 0 T', Ω t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)|, ?_⟩
  exact ⟨vorticityEnvelopeOn_restrict hEnv hT, integrableVorticityEnvelopeOn_restrict hInt hT⟩

/-- On a nonnegative shorter slab, the uniform-to-BKM conversion restricts to
the explicit constant envelope `Ω(t) = B`. -/
theorem uniformVorticityBoundUpTo_implies_constantBKMEnvelope_restrict
    {u : NSVelocityField} {T T' B : ℝ}
    (hT' : 0 ≤ T')
    (hω : uniformVorticityBoundUpTo u T B)
    (hT : T' ≤ T) :
    vorticityEnvelopeOn u T' (fun _ : NSTime => B) ∧
      integrableVorticityEnvelopeOn (fun _ : NSTime => B) T' (T' * B) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope
    (u := u) (T := T') (B := B) hT'
    (uniformVorticityBoundUpTo_restrict hω hT)

/-- Uniform linear-combination control on a large slab restricts to explicit
BKM-envelope data on every shorter slab. -/
theorem uniformVorticityBoundUpTo_linearCombination_implies_BKMEnvelope_restrict
    {u v : NSVelocityField} {T T' B B' : ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B')
    (a b : ℝ)
    (hT : T' ≤ T) :
    ∃ Ω : NSTime → ℝ, ∃ Bint : ℝ,
      vorticityEnvelopeOn (a • u + b • v) T' Ω ∧
        integrableVorticityEnvelopeOn Ω T' Bint := by
  exact uniformVorticityBoundUpTo_implies_BKMEnvelope_restrict
    (u := a • u + b • v) (T := T) (T' := T')
    (B := |a| * B + |b| * B')
    (uniformVorticityBoundUpTo_linearCombination hu hv hω hω' a b) hT

/-- On a nonnegative shorter slab, uniform linear-combination control on a
large slab restricts to the explicit constant BKM envelope. -/
theorem uniformVorticityBoundUpTo_linearCombination_implies_constantBKMEnvelope_restrict
    {u v : NSVelocityField} {T T' B B' : ℝ}
    (hT' : 0 ≤ T')
    (hu : smoothSpaceTimeVelocity u)
    (hv : smoothSpaceTimeVelocity v)
    (hω : uniformVorticityBoundUpTo u T B)
    (hω' : uniformVorticityBoundUpTo v T B')
    (a b : ℝ)
    (hT : T' ≤ T) :
    vorticityEnvelopeOn (a • u + b • v) T'
        (fun _ : NSTime => |a| * B + |b| * B') ∧
      integrableVorticityEnvelopeOn
        (fun _ : NSTime => |a| * B + |b| * B') T'
        (T' * (|a| * B + |b| * B')) := by
  exact uniformVorticityBoundUpTo_implies_constantBKMEnvelope_restrict
    (u := a • u + b • v) (T := T) (T' := T')
    (B := |a| * B + |b| * B') hT'
    (uniformVorticityBoundUpTo_linearCombination hu hv hω hω' a b) hT

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
