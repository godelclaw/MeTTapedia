import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeRealCoherentPairEstimate

/-!
# Exact aperture factor in the coherent stretching symbol

This module locates the genuine aperture power used by the pancake endpoint
estimate.  It does not come from the coherent projection.  It comes from the
bilinear Biot--Savart stretching symbol after both frequencies and
polarizations are placed in the coherent pancake geometry.

For

`k₁ = (delta*a, delta*b, c)` and
`k₂ = (delta*d, delta*e, f)`,

the coherent source has Biot--Savart velocity `(0,c,-delta*b)`, and the full
coherent interaction factors exactly as

`stretchAmp k₁ (coherentW k₁) (coherentW k₂)
  = delta * coherentStretchNormalized ...`.

The normalized expression is polynomial in `delta` and the six normalized
frequency coordinates.  Thus it extends smoothly through `delta = 0`; this
is the algebraic input needed for a uniformly Schwartz-localized bilinear
symbol and the bilinear kernel scaling theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeCoherentStretchFactorization

open PancakeRealCoherentPairEstimate

/-- A frequency whose two transverse coordinates have pancake aperture
`delta`. -/
def scaledPancakeFrequency (delta a b c : ℝ) : RealVec3 :=
  (delta * a, delta * b, c)

/-- The scalar appearing after factoring `delta` from
`dot(k₁, coherentW(k₂))`. -/
def receiverCoupling (delta a b c d e f : ℝ) : ℝ :=
  f * (a * f - c * d) + delta ^ 2 * e * (a * e - b * d)

/-- The coherent stretching symbol after removal of its exact aperture
factor.  This expression contains no division and remains polynomial at
`delta = 0`. -/
def coherentStretchNormalized (delta a b c d e f : ℝ) : RealVec3 :=
  smul (1 / 2)
    (add
      (smul (delta * d * (b * f - c * e))
        (scaledPancakeFrequency delta a b c))
      (smul (receiverCoupling delta a b c d e f)
        (0, c, -(delta * b))))

/-- The normalized bilinear symbol after coherent projection of arbitrary
source and receiver amplitudes. -/
def coherentProjectedStretchNormalized
    (delta a b c d e f : ℝ) (w₁ w₂ : RealVec3) : RealVec3 :=
  smul
    (coherentCoeff (scaledPancakeFrequency delta a b c) w₁ *
      coherentCoeff (scaledPancakeFrequency delta d e f) w₂)
    (coherentStretchNormalized delta a b c d e f)

theorem normSq_scaledPancakeFrequency_ne
    (delta a b c : ℝ) (hc : c ≠ 0) :
    normSq (scaledPancakeFrequency delta a b c) ≠ 0 := by
  unfold normSq dot scaledPancakeFrequency
  nlinarith [sq_pos_of_ne_zero hc]

/-- The coherent-line denominator stays strictly positive whenever the axial
frequency is nonzero, uniformly through zero aperture. -/
theorem normSq_coherentW_scaled_pos
    (delta a b c : ℝ) (hc : c ≠ 0) :
    0 < normSq (coherentW (scaledPancakeFrequency delta a b c)) := by
  rw [normSq_coherentW]
  unfold normSq dot scaledPancakeFrequency
  nlinarith [sq_pos_of_ne_zero hc, sq_nonneg (delta * a),
    sq_nonneg (delta * b)]

/-- Quantitative axial coercivity of the coherent-line denominator.  This is
uniform in the aperture and in both transverse normalized coordinates. -/
theorem axial_pow_four_le_normSq_coherentW_scaled
    (delta a b c : ℝ) :
    c ^ 4 ≤ normSq (coherentW (scaledPancakeFrequency delta a b c)) := by
  rw [normSq_coherentW]
  unfold normSq dot scaledPancakeFrequency
  have hleft : c ^ 2 ≤
      (delta * a) * (delta * a) +
        (delta * b) * (delta * b) + c * c := by
    nlinarith [sq_nonneg (delta * a), sq_nonneg (delta * b)]
  have hright : c ^ 2 ≤
      (delta * b) * (delta * b) + c * c := by
    nlinarith [sq_nonneg (delta * b)]
  have hleft_nonneg : 0 ≤
      (delta * a) * (delta * a) +
        (delta * b) * (delta * b) + c * c := by
    nlinarith [sq_nonneg (delta * a), sq_nonneg (delta * b), sq_nonneg c]
  calc
    c ^ 4 = c ^ 2 * c ^ 2 := by ring
    _ ≤ ((delta * a) * (delta * a) +
          (delta * b) * (delta * b) + c * c) *
        ((delta * b) * (delta * b) + c * c) :=
      mul_le_mul hleft hright (sq_nonneg c) hleft_nonneg
    _ = ((delta * a) * (delta * a) +
          (delta * b) * (delta * b) + c * c) *
        ((delta * a) * (delta * a) +
          (delta * b) * (delta * b) + c * c - (delta * a) ^ 2) := by ring

/-- Exact first scalar cancellation in the coherent interaction. -/
theorem dot_biot_coherent_receiver
    (delta b c d e f : ℝ) :
    dot (0, c, -(delta * b))
        (coherentW (scaledPancakeFrequency delta d e f)) =
      delta ^ 2 * d * (b * f - c * e) := by
  simp only [scaledPancakeFrequency, coherentW, normSq, dot, add, smul, ex]
  ring

/-- Exact second scalar cancellation in the coherent interaction. -/
theorem dot_source_coherent_receiver
    (delta a b c d e f : ℝ) :
    dot (scaledPancakeFrequency delta a b c)
        (coherentW (scaledPancakeFrequency delta d e f)) =
      delta * receiverCoupling delta a b c d e f := by
  simp only [scaledPancakeFrequency, coherentW, receiverCoupling,
    normSq, dot, add, smul, ex]
  ring

/-- **Exact bilinear aperture factor.**  The complete coherent
Biot--Savart stretching interaction is divisible by `delta`, and the quotient
is the explicit polynomial `coherentStretchNormalized`. -/
theorem stretchAmp_coherent_scaled_eq_delta_smul
    (delta a b c d e f : ℝ) (hc : c ≠ 0) :
    stretchAmp (scaledPancakeFrequency delta a b c)
        (coherentW (scaledPancakeFrequency delta a b c))
        (coherentW (scaledPancakeFrequency delta d e f)) =
      smul delta (coherentStretchNormalized delta a b c d e f) := by
  have hk := normSq_scaledPancakeFrequency_ne delta a b c hc
  unfold stretchAmp
  rw [biotSavartAmp_coherentW _ hk]
  change smul (1 / 2)
      (add
        (smul (dot (0, c, -(delta * b))
            (coherentW (scaledPancakeFrequency delta d e f)))
          (scaledPancakeFrequency delta a b c))
        (smul (dot (scaledPancakeFrequency delta a b c)
            (coherentW (scaledPancakeFrequency delta d e f)))
          (0, c, -(delta * b)))) = _
  rw [dot_biot_coherent_receiver,
    dot_source_coherent_receiver]
  unfold coherentStretchNormalized scaledPancakeFrequency
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [smul, add] <;> ring

/-- **Arbitrary-amplitude projected factorization.**  After coherent
projection of both input amplitudes, the complete bilinear stretching symbol
still contains the same exact aperture factor. -/
theorem stretchAmp_coherentProject_scaled_eq_delta_smul
    (delta a b c d e f : ℝ) (w₁ w₂ : RealVec3)
    (hc : c ≠ 0) :
    stretchAmp (scaledPancakeFrequency delta a b c)
        (coherentProject (scaledPancakeFrequency delta a b c) w₁)
        (coherentProject (scaledPancakeFrequency delta d e f) w₂) =
      smul delta
        (coherentProjectedStretchNormalized delta a b c d e f w₁ w₂) := by
  rw [show coherentProject (scaledPancakeFrequency delta a b c) w₁ =
      smul (coherentCoeff (scaledPancakeFrequency delta a b c) w₁)
        (coherentW (scaledPancakeFrequency delta a b c)) from rfl,
    show coherentProject (scaledPancakeFrequency delta d e f) w₂ =
      smul (coherentCoeff (scaledPancakeFrequency delta d e f) w₂)
        (coherentW (scaledPancakeFrequency delta d e f)) from rfl,
    stretchAmp_smul,
    stretchAmp_coherent_scaled_eq_delta_smul delta a b c d e f hc]
  unfold coherentProjectedStretchNormalized
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [smul] <;> ring

/-- At zero aperture the normalized symbol has only the axial-output
component predicted by the limiting coherent geometry. -/
theorem coherentStretchNormalized_zero
    (a b c d e f : ℝ) :
    coherentStretchNormalized 0 a b c d e f =
      (0, (1 / 2) * c * f * (a * f - c * d), 0) := by
  ext <;>
    norm_num [coherentStretchNormalized, receiverCoupling,
      scaledPancakeFrequency, smul, add] <;> ring

end PancakeCoherentStretchFactorization
end NavierStokes
end FluidDynamics
end Mettapedia
