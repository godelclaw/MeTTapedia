import Mettapedia.Analysis.ScalarTripleProductEvolution
import Mettapedia.Analysis.RadialPowerEvolution
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Evolution of the complete signed radial stretching pair

The trace-free common deformation cancels from the scalar triple product,
but not from the radial amplitude pair. Kernel motion and amplitude growth
remain separate signed terms. The derivative is valid at either zero
endpoint; no direction field or division by vorticity is used.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedRadialStretch

open EuclideanCrossProduct RadialPower
open scoped RealInnerProductSpace Matrix
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def amplitudePair (p : ℕ) (a b h : R3) : ℝ :=
  ⟪h, radialPower p a - radialPower p b⟫

def density (p : ℕ) (k : ℝ) (a b h : R3) : ℝ :=
  k * tripleProduct a b h * amplitudePair p a b h

def amplitudeRate (n : ℕ) (a b h da db dh : R3) : ℝ :=
  ⟪dh, radialPower (2 * (n + 1)) a - radialPower (2 * (n + 1)) b⟫ +
    ⟪h, evenRadialRate n a da - evenRadialRate n b db⟫

def residualRate (n : ℕ) (k : ℝ) (a b h ra rb rh : R3) : ℝ :=
  k * (tripleRate a b h ra rb rh * amplitudePair (2 * (n + 1)) a b h +
    tripleProduct a b h * amplitudeRate n a b h ra rb rh)

def rate (n : ℕ) (k dk : ℝ) (a b h da db dh : R3) : ℝ :=
  dk * tripleProduct a b h * amplitudePair (2 * (n + 1)) a b h +
    residualRate n k a b h da db dh

theorem hasDerivAt_amplitudePair (n : ℕ) {a b h : ℝ → R3} {da db dh : R3} {t : ℝ}
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) (hh : HasDerivAt h dh t) :
    HasDerivAt (fun τ ↦ amplitudePair (2 * (n + 1)) (a τ) (b τ) (h τ))
      (amplitudeRate n (a t) (b t) (h t) da db dh) t := by
  simpa only [amplitudePair, amplitudeRate, Pi.sub_apply, add_comm] using
    hh.inner ℝ ((hasDerivAt_radialPower_even n ha).sub (hasDerivAt_radialPower_even n hb))

theorem hasDerivAt_density (n : ℕ) {a b h : ℝ → R3} {k : ℝ → ℝ}
    {da db dh : R3} {dk t : ℝ} (ha : HasDerivAt a da t) (hb : HasDerivAt b db t)
    (hh : HasDerivAt h dh t) (hk : HasDerivAt k dk t) :
    HasDerivAt (fun τ ↦ density (2 * (n + 1)) (k τ) (a τ) (b τ) (h τ))
      (rate n (k t) dk (a t) (b t) (h t) da db dh) t := by
  have hd := (hk.mul (hasDerivAt_tripleProduct ha hb hh)).mul
    (hasDerivAt_amplitudePair n ha hb hh)
  apply hd.congr_deriv
  simp only [rate, residualRate, Pi.mul_apply]
  ring

theorem amplitudeRate_add (n : ℕ) (a b h da db dh ra rb rh : R3) :
    amplitudeRate n a b h (da + ra) (db + rb) (dh + rh) =
      amplitudeRate n a b h da db dh + amplitudeRate n a b h ra rb rh := by
  simp only [amplitudeRate, evenRadialRate, inner_add_right, smul_add,
    inner_add_left, inner_sub_right, real_inner_smul_right]
  ring

theorem amplitudeRate_smul (n : ℕ) (c : ℝ) (a b h ra rb rh : R3) :
    amplitudeRate n a b h (c • ra) (c • rb) (c • rh) =
      c * amplitudeRate n a b h ra rb rh := by
  simp only [amplitudeRate, evenRadialRate, inner_sub_right, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, smul_smul]
  ring

theorem residualRate_add (n : ℕ) (k : ℝ) (a b h da db dh ra rb rh : R3) :
    residualRate n k a b h (da + ra) (db + rb) (dh + rh) =
      residualRate n k a b h da db dh + residualRate n k a b h ra rb rh := by
  simp only [residualRate, amplitudeRate_add, tripleRate_add]
  ring

theorem residualRate_smul (n : ℕ) (k c : ℝ) (a b h ra rb rh : R3) :
    residualRate n k a b h (c • ra) (c • rb) (c • rh) =
      c * residualRate n k a b h ra rb rh := by
  simp only [residualRate, amplitudeRate_smul, tripleRate, cross_smul_left,
    cross_smul_right, inner_add_left, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Common deformation still acts on the separation and radial amplitude.
No sign or damping property is asserted for this term. -/
def commonAmplitudeRate (n : ℕ) (A : R3 →L[ℝ] R3) (a b h : R3) : ℝ :=
  ⟪A h, radialPower (2 * (n + 1)) a - radialPower (2 * (n + 1)) b⟫ +
    ⟪h, A (radialPower (2 * (n + 1)) a - radialPower (2 * (n + 1)) b)⟫ +
    ⟪h, radialStrainExcess n A a - radialStrainExcess n A b⟫

theorem amplitudeRate_common (n : ℕ) (A : R3 →L[ℝ] R3) (a b h : R3) :
    amplitudeRate n a b h (A a) (A b) (A h) = commonAmplitudeRate n A a b h := by
  have ha := evenRadialRate_strain_add n A a 0
  have hb := evenRadialRate_strain_add n A b 0
  simp only [add_zero, evenRadialRate, inner_zero_right, mul_zero, zero_smul, smul_zero] at ha hb
  simp only [amplitudeRate, evenRadialRate, ha, hb, commonAmplitudeRate,
    map_sub, inner_sub_right, inner_add_right]
  ring

/-- Common rotations do not contribute to the amplitude rate. -/
theorem commonAmplitudeRate_eq_zero_of_skew (n : ℕ) (A : R3 →L[ℝ] R3)
    (hA : ∀ v w, ⟪A v, w⟫ = -⟪v, A w⟫) (a b h : R3) :
    commonAmplitudeRate n A a b h = 0 := by
  have hq (v : R3) : ⟪v, A v⟫ = 0 := by
    have hv := hA v v
    linarith only [hv, real_inner_comm v (A v)]
  simp only [commonAmplitudeRate, radialStrainExcess, hq, mul_zero, zero_smul, sub_self,
    inner_zero_right, add_zero, hA]
  ring

theorem rate_cancel_common (n : ℕ) (k dk : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A.trace = 0) (a b h ra rb rh : R3) :
    rate n k dk a b h (A.toEuclideanLin a + ra) (A.toEuclideanLin b + rb)
      (A.toEuclideanLin h + rh) =
        dk * tripleProduct a b h * amplitudePair (2 * (n + 1)) a b h +
        k * tripleProduct a b h * commonAmplitudeRate n
          (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A) a b h +
        residualRate n k a b h ra rb rh := by
  rw [rate, residualRate_add]
  have ht := tripleRate_common A a b h
  rw [hA, zero_mul] at ht
  have hm := amplitudeRate_common n (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A) a b h
  change amplitudeRate n a b h (A.toEuclideanLin a) (A.toEuclideanLin b)
    (A.toEuclideanLin h) = _ at hm
  simp only [residualRate, ht, hm, zero_mul, zero_add]
  ring

end Mettapedia.Analysis.SignedRadialStretch
