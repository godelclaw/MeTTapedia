import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCoherentPairEstimate

/-!
# Continuous-frequency coherent pair estimate over the reals

The exact lattice calculation ultimately feeds a smooth Fourier multiplier,
whose normalized frequency variables range over `ℝ³`.  This module instantiates
the generic polynomial core of `PancakeCoherentPairEstimate` over `ℝ` and
rebuilds the surrounding Biot--Savart identities there.

The result is the same pointwise law at arbitrary continuous frequencies:
two coherent cone directions with squared apertures `d₁,d₂ ≤ 1/4` have
normalized squared stretching at most `6(d₁+d₂)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeRealCoherentPairEstimate

open PancakeCoherentPairEstimate

abbrev RealVec3 := ℝ × ℝ × ℝ

def dot (a b : RealVec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def cross (a b : RealVec3) : RealVec3 :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1,
   a.2.2 * b.1 - a.1 * b.2.2,
   a.1 * b.2.1 - a.2.1 * b.1)

def smul (c : ℝ) (a : RealVec3) : RealVec3 :=
  (c * a.1, c * a.2.1, c * a.2.2)

def add (a b : RealVec3) : RealVec3 :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

def normSq (a : RealVec3) : ℝ := dot a a

def biotSavartAmp (k w : RealVec3) : RealVec3 :=
  smul (1 / normSq k) (cross k w)

def stretchAmp (k w₁ w₂ : RealVec3) : RealVec3 :=
  let u := biotSavartAmp k w₁
  smul (1 / 2) (add (smul (dot u w₂) k) (smul (dot k w₂) u))

def sigmaSq (k w₁ w₂ : RealVec3) : ℝ :=
  normSq (stretchAmp k w₁ w₂) / (normSq w₁ * normSq w₂)

def ex : RealVec3 := (1, 0, 0)

def coherentW (k : RealVec3) : RealVec3 :=
  add (smul (normSq k) ex) (smul (-(dot k ex)) k)

/-- Scalar coefficient of the orthogonal projection onto the coherent line. -/
def coherentCoeff (k w : RealVec3) : ℝ :=
  dot (coherentW k) w / normSq (coherentW k)

/-- Rank-one projection of a Fourier amplitude onto the coherent line. -/
def coherentProject (k w : RealVec3) : RealVec3 :=
  smul (coherentCoeff k w) (coherentW k)

theorem normSq_smul (c : ℝ) (w : RealVec3) :
    normSq (smul c w) = c ^ 2 * normSq w := by
  obtain ⟨x, y, z⟩ := w
  simp only [normSq, dot, smul]
  ring

theorem normSq_nonneg (w : RealVec3) : 0 ≤ normSq w := by
  obtain ⟨x, y, z⟩ := w
  simp only [normSq, dot]
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]

/-- Coordinate Cauchy--Schwarz, stated for the algebraic Euclidean norm used
by the coherent multiplier calculation. -/
theorem dot_sq_le_normSq_mul (a b : RealVec3) :
    dot a b ^ 2 ≤ normSq a * normSq b := by
  obtain ⟨a₁, a₂, a₃⟩ := a
  obtain ⟨b₁, b₂, b₃⟩ := b
  have hlagrange :
      (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2) * (b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2) -
          (a₁ * b₁ + a₂ * b₂ + a₃ * b₃) ^ 2 =
        (a₁ * b₂ - a₂ * b₁) ^ 2 + (a₁ * b₃ - a₃ * b₁) ^ 2 +
          (a₂ * b₃ - a₃ * b₂) ^ 2 := by ring
  simp only [dot, normSq]
  nlinarith [hlagrange, sq_nonneg (a₁ * b₂ - a₂ * b₁),
    sq_nonneg (a₁ * b₃ - a₃ * b₁), sq_nonneg (a₂ * b₃ - a₃ * b₂)]

theorem biotSavartAmp_smul_right (k w : RealVec3) (c : ℝ) :
    biotSavartAmp k (smul c w) = smul c (biotSavartAmp k w) := by
  obtain ⟨a, b, d⟩ := k
  obtain ⟨x, y, z⟩ := w
  simp only [biotSavartAmp, cross, smul, normSq, dot]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp <;> ring

theorem stretchAmp_smul (k w₁ w₂ : RealVec3) (c₁ c₂ : ℝ) :
    stretchAmp k (smul c₁ w₁) (smul c₂ w₂) =
      smul (c₁ * c₂) (stretchAmp k w₁ w₂) := by
  obtain ⟨a, b, d⟩ := k
  obtain ⟨x₁, y₁, z₁⟩ := w₁
  obtain ⟨x₂, y₂, z₂⟩ := w₂
  simp only [stretchAmp, biotSavartAmp, cross, smul, add, dot, normSq]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp <;> ring

theorem normSq_coherentW (k : RealVec3) :
    normSq (coherentW k) = normSq k * (normSq k - k.1 ^ 2) := by
  simp only [coherentW, normSq, dot, add, smul, ex]
  ring

theorem cross_coherentW (k : RealVec3) :
    cross k (coherentW k) = smul (normSq k) (0, k.2.2, -k.2.1) := by
  simp only [coherentW, cross, add, smul, normSq, dot, ex]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp <;> ring

/-- The Biot--Savart velocity of a coherent mode has an exact polynomial
form: the apparent inverse Laplacian cancels completely. -/
theorem biotSavartAmp_coherentW (k : RealVec3) (hk : normSq k ≠ 0) :
    biotSavartAmp k (coherentW k) = (0, k.2.2, -k.2.1) := by
  rw [biotSavartAmp, cross_coherentW]
  unfold smul
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp <;>
    field_simp [hk]

/-- **Continuous-frequency coherent pair estimate.** -/
theorem sigmaSq_coherent_le
    (k₁ k₂ : RealVec3) (d₁ d₂ : ℝ)
    (hk₁ : normSq k₁ ≠ 0) (hk₂ : normSq k₂ ≠ 0)
    (hcone₁ : k₁.1 ^ 2 + k₁.2.1 ^ 2 ≤ d₁ * normSq k₁)
    (hcone₂ : k₂.1 ^ 2 + k₂.2.1 ^ 2 ≤ d₂ * normSq k₂)
    (hd₁ : d₁ ≤ 1 / 4) (hd₂ : d₂ ≤ 1 / 4) :
    sigmaSq k₁ (coherentW k₁) (coherentW k₂) ≤ 6 * (d₁ + d₂) := by
  obtain ⟨a₁, b₁, c₁⟩ := k₁
  obtain ⟨a₂, b₂, c₂⟩ := k₂
  simp only [normSq, dot] at hk₁ hk₂ hcone₁ hcone₂
  have hn₁ : 0 < a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2 := by
    by_contra h
    push Not at h
    apply hk₁
    nlinarith [sq_nonneg a₁, sq_nonneg b₁, sq_nonneg c₁]
  have hn₂ : 0 < a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2 := by
    by_contra h
    push Not at h
    apply hk₂
    nlinarith [sq_nonneg a₂, sq_nonneg b₂, sq_nonneg c₂]
  have hcone₁' : a₁ ^ 2 + b₁ ^ 2 ≤
      d₁ * (a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) := by nlinarith [hcone₁]
  have hcone₂' : a₂ ^ 2 + b₂ ^ 2 ≤
      d₂ * (a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) := by nlinarith [hcone₂]
  have hcore := core_inequality a₁ b₁ c₁ a₂ b₂ c₂ d₁ d₂ hn₁ hn₂
    hcone₁' hcone₂' hd₁ hd₂
  simp only at hcore
  have hddnn : 0 ≤ d₁ + d₂ := by
    have hd₁nn : 0 ≤ d₁ := by nlinarith [sq_nonneg a₁, sq_nonneg b₁]
    have hd₂nn : 0 ≤ d₂ := by nlinarith [sq_nonneg a₂, sq_nonneg b₂]
    linarith
  have hNval : normSq (a₁, b₁, c₁) = a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2 := by
    simp only [normSq, dot]
    ring
  have hbiot : biotSavartAmp (a₁, b₁, c₁) (coherentW (a₁, b₁, c₁)) =
      ((0 : ℝ), c₁, -b₁) := by
    simp only [biotSavartAmp]
    rw [cross_coherentW, hNval]
    simp only [smul]
    have hne : a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2 ≠ 0 := ne_of_gt hn₁
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp <;> field_simp
  have hPval : dot ((0 : ℝ), c₁, -b₁) (coherentW (a₂, b₂, c₂)) =
      -a₂ * (c₁ * b₂ - b₁ * c₂) := by
    simp only [coherentW, dot, add, smul, ex, normSq]
    ring
  have hQval : dot ((a₁ : ℝ), b₁, c₁) (coherentW (a₂, b₂, c₂)) =
      (a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) * a₁ -
        a₂ * (a₁ * a₂ + b₁ * b₂ + c₁ * c₂) := by
    simp only [coherentW, dot, add, smul, ex, normSq]
    ring
  have hstretch : normSq (stretchAmp (a₁, b₁, c₁)
      (coherentW (a₁, b₁, c₁)) (coherentW (a₂, b₂, c₂))) =
      (1 / 4) * ((-a₂ * (c₁ * b₂ - b₁ * c₂)) ^ 2 *
          (a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) +
        ((a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) * a₁ -
          a₂ * (a₁ * a₂ + b₁ * b₂ + c₁ * c₂)) ^ 2 *
          (b₁ ^ 2 + c₁ ^ 2)) := by
    simp only [stretchAmp]
    rw [hbiot, hPval, hQval]
    simp only [normSq, dot, smul, add]
    ring
  have hD₁ : normSq (coherentW (a₁, b₁, c₁)) =
      (a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) *
        ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) - a₁ ^ 2) := by
    rw [normSq_coherentW, hNval]
  have hD₂ : normSq (coherentW (a₂, b₂, c₂)) =
      (a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) *
        ((a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) - a₂ ^ 2) := by
    rw [normSq_coherentW]
    simp only [normSq, dot]
    ring_nf
  have hden₁ : (3 / 4) * ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) *
      (a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2)) ≤
      (a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) *
        ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) - a₁ ^ 2) := by
    have ha₁ : a₁ ^ 2 ≤ (1 / 4) * (a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) := by
      nlinarith [sq_nonneg b₁, hcone₁', hd₁, hn₁]
    nlinarith [hn₁]
  have hden₂ : (3 / 4) * ((a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) *
      (a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2)) ≤
      (a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) *
        ((a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) - a₂ ^ 2) := by
    have ha₂ : a₂ ^ 2 ≤ (1 / 4) * (a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) := by
      nlinarith [sq_nonneg b₂, hcone₂', hd₂, hn₂]
    nlinarith [hn₂]
  have hD₁pos : 0 < (a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) *
      ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) - a₁ ^ 2) := by
    nlinarith [hden₁, mul_pos hn₁ hn₁]
  have hD₂pos : 0 < (a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) *
      ((a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) - a₂ ^ 2) := by
    nlinarith [hden₂, mul_pos hn₂ hn₂]
  rw [sigmaSq, hstretch, hD₁, hD₂, div_le_iff₀ (by positivity)]
  calc
    (1 / 4) * ((-a₂ * (c₁ * b₂ - b₁ * c₂)) ^ 2 *
        (a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) +
      ((a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) * a₁ -
        a₂ * (a₁ * a₂ + b₁ * b₂ + c₁ * c₂)) ^ 2 * (b₁ ^ 2 + c₁ ^ 2))
      ≤ (1 / 4) * (24 * (d₁ + d₂) *
          ((3 / 4) * ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) *
            (a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2)) *
          ((3 / 4) * ((a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) *
            (a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2))))) := by linarith [hcore]
    _ = 6 * (d₁ + d₂) *
        ((3 / 4) * ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) *
          (a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2))) *
        ((3 / 4) * ((a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) *
          (a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2))) := by ring
    _ ≤ 6 * (d₁ + d₂) *
        ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) *
          ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) - a₁ ^ 2)) *
        ((a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) *
          ((a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) - a₂ ^ 2)) := by
      have h6 : (0 : ℝ) ≤ 6 * (d₁ + d₂) := by linarith
      have hstep₁ : 6 * (d₁ + d₂) *
          ((3 / 4) * ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) *
            (a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2))) ≤
          6 * (d₁ + d₂) *
          ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) *
            ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) - a₁ ^ 2)) :=
        mul_le_mul_of_nonneg_left hden₁ h6
      have hlast : (0 : ℝ) ≤
          (3 / 4) * ((a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) *
            (a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2)) := by positivity
      calc
        6 * (d₁ + d₂) *
            ((3 / 4) * ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) *
              (a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2))) *
            ((3 / 4) * ((a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) *
              (a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2)))
          ≤ 6 * (d₁ + d₂) *
            ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) *
              ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) - a₁ ^ 2)) *
            ((3 / 4) * ((a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) *
              (a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2))) :=
            mul_le_mul_of_nonneg_right hstep₁ hlast
        _ ≤ 6 * (d₁ + d₂) *
            ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) *
              ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) - a₁ ^ 2)) *
            ((a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) *
              ((a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) - a₂ ^ 2)) := by
          apply mul_le_mul_of_nonneg_left hden₂
          nlinarith [h6, hD₁pos]
    _ = 6 * (d₁ + d₂) *
        ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) *
          ((a₁ ^ 2 + b₁ ^ 2 + c₁ ^ 2) - a₁ ^ 2) *
        ((a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) *
          ((a₂ ^ 2 + b₂ ^ 2 + c₂ ^ 2) - a₂ ^ 2))) := by ring

theorem normSq_coherentW_pos {k : RealVec3} {d : ℝ}
    (hk : normSq k ≠ 0)
    (hcone : k.1 ^ 2 + k.2.1 ^ 2 ≤ d * normSq k)
    (hd : d ≤ 1 / 4) :
    0 < normSq (coherentW k) := by
  have hN : 0 < normSq k := by
    obtain ⟨a, b, c⟩ := k
    simp only [normSq, dot] at hk ⊢
    by_contra h
    push Not at h
    apply hk
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hx : k.1 ^ 2 ≤ (1 / 4) * normSq k := by
    have hdN : d * normSq k ≤ (1 / 4) * normSq k :=
      mul_le_mul_of_nonneg_right hd (le_of_lt hN)
    nlinarith [hcone, sq_nonneg k.2.1]
  rw [normSq_coherentW]
  nlinarith

/-- The coherent rank-one projection does not increase Euclidean energy. -/
theorem normSq_coherentProject_le (k w : RealVec3) {d : ℝ}
    (hk : normSq k ≠ 0)
    (hcone : k.1 ^ 2 + k.2.1 ^ 2 ≤ d * normSq k)
    (hd : d ≤ 1 / 4) :
    normSq (coherentProject k w) ≤ normSq w := by
  have hp : 0 < normSq (coherentW k) :=
    normSq_coherentW_pos hk hcone hd
  rw [coherentProject, normSq_smul, coherentCoeff]
  calc
    (dot (coherentW k) w / normSq (coherentW k)) ^ 2 *
        normSq (coherentW k) =
        dot (coherentW k) w ^ 2 / normSq (coherentW k) := by
      field_simp [ne_of_gt hp]
    _ ≤ normSq w := (div_le_iff₀ hp).2 (by
      simpa [mul_comm] using dot_sq_le_normSq_mul (coherentW k) w)

/-- Non-normalized amplitude form of the continuous-frequency estimate. -/
theorem normSq_stretchAmp_coherent_le
    (k₁ k₂ : RealVec3) (d₁ d₂ : ℝ)
    (hk₁ : normSq k₁ ≠ 0) (hk₂ : normSq k₂ ≠ 0)
    (hcone₁ : k₁.1 ^ 2 + k₁.2.1 ^ 2 ≤ d₁ * normSq k₁)
    (hcone₂ : k₂.1 ^ 2 + k₂.2.1 ^ 2 ≤ d₂ * normSq k₂)
    (hd₁ : d₁ ≤ 1 / 4) (hd₂ : d₂ ≤ 1 / 4) :
    normSq (stretchAmp k₁ (coherentW k₁) (coherentW k₂)) ≤
      6 * (d₁ + d₂) * normSq (coherentW k₁) *
        normSq (coherentW k₂) := by
  have hsigma := sigmaSq_coherent_le k₁ k₂ d₁ d₂ hk₁ hk₂
    hcone₁ hcone₂ hd₁ hd₂
  have hden : 0 < normSq (coherentW k₁) * normSq (coherentW k₂) :=
    mul_pos (normSq_coherentW_pos hk₁ hcone₁ hd₁)
      (normSq_coherentW_pos hk₂ hcone₂ hd₂)
  rw [sigmaSq, div_le_iff₀ hden] at hsigma
  simpa [mul_assoc] using hsigma

/-- **Projected-amplitude coherent estimate.**  The continuous-frequency
coherent cancellation applies to the rank-one coherent parts of arbitrary
source and receiver amplitudes, with no normalization or coefficient loss. -/
theorem normSq_stretchAmp_coherentProject_le
    (k₁ k₂ w₁ w₂ : RealVec3) (d₁ d₂ : ℝ)
    (hk₁ : normSq k₁ ≠ 0) (hk₂ : normSq k₂ ≠ 0)
    (hcone₁ : k₁.1 ^ 2 + k₁.2.1 ^ 2 ≤ d₁ * normSq k₁)
    (hcone₂ : k₂.1 ^ 2 + k₂.2.1 ^ 2 ≤ d₂ * normSq k₂)
    (hd₁ : d₁ ≤ 1 / 4) (hd₂ : d₂ ≤ 1 / 4) :
    normSq (stretchAmp k₁ (coherentProject k₁ w₁)
      (coherentProject k₂ w₂)) ≤
      6 * (d₁ + d₂) * normSq (coherentProject k₁ w₁) *
        normSq (coherentProject k₂ w₂) := by
  let c₁ := coherentCoeff k₁ w₁
  let c₂ := coherentCoeff k₂ w₂
  have hbase := normSq_stretchAmp_coherent_le k₁ k₂ d₁ d₂
    hk₁ hk₂ hcone₁ hcone₂ hd₁ hd₂
  have hc : 0 ≤ (c₁ * c₂) ^ 2 := sq_nonneg _
  rw [show coherentProject k₁ w₁ = smul c₁ (coherentW k₁) from rfl,
    show coherentProject k₂ w₂ = smul c₂ (coherentW k₂) from rfl,
    stretchAmp_smul, normSq_smul, normSq_smul, normSq_smul]
  calc
    (c₁ * c₂) ^ 2 *
        normSq (stretchAmp k₁ (coherentW k₁) (coherentW k₂)) ≤
        (c₁ * c₂) ^ 2 *
          (6 * (d₁ + d₂) * normSq (coherentW k₁) *
            normSq (coherentW k₂)) :=
      mul_le_mul_of_nonneg_left hbase hc
    _ = 6 * (d₁ + d₂) * (c₁ ^ 2 * normSq (coherentW k₁)) *
        (c₂ ^ 2 * normSq (coherentW k₂)) := by ring

/-- Field-facing pointwise form: after coherent projection, stretching is
bounded by the aperture gain times the energies of the original amplitudes. -/
theorem normSq_stretchAmp_coherentProject_le_input
    (k₁ k₂ w₁ w₂ : RealVec3) (d₁ d₂ : ℝ)
    (hk₁ : normSq k₁ ≠ 0) (hk₂ : normSq k₂ ≠ 0)
    (hcone₁ : k₁.1 ^ 2 + k₁.2.1 ^ 2 ≤ d₁ * normSq k₁)
    (hcone₂ : k₂.1 ^ 2 + k₂.2.1 ^ 2 ≤ d₂ * normSq k₂)
    (hd₁ : d₁ ≤ 1 / 4) (hd₂ : d₂ ≤ 1 / 4) :
    normSq (stretchAmp k₁ (coherentProject k₁ w₁)
      (coherentProject k₂ w₂)) ≤
      6 * (d₁ + d₂) * normSq w₁ * normSq w₂ := by
  have hproject := normSq_stretchAmp_coherentProject_le
    k₁ k₂ w₁ w₂ d₁ d₂ hk₁ hk₂ hcone₁ hcone₂ hd₁ hd₂
  have hp₁ := normSq_coherentProject_le k₁ w₁ hk₁ hcone₁ hd₁
  have hp₂ := normSq_coherentProject_le k₂ w₂ hk₂ hcone₂ hd₂
  have hn₁ : 0 < normSq k₁ := by
    obtain ⟨a, b, c⟩ := k₁
    simp only [normSq, dot] at hk₁ ⊢
    by_contra h
    push Not at h
    apply hk₁
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hn₂ : 0 < normSq k₂ := by
    obtain ⟨a, b, c⟩ := k₂
    simp only [normSq, dot] at hk₂ ⊢
    by_contra h
    push Not at h
    apply hk₂
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hd₁nn : 0 ≤ d₁ := by
    nlinarith [hcone₁, sq_nonneg k₁.1, sq_nonneg k₁.2.1]
  have hd₂nn : 0 ≤ d₂ := by
    nlinarith [hcone₂, sq_nonneg k₂.1, sq_nonneg k₂.2.1]
  have hgain : 0 ≤ 6 * (d₁ + d₂) := by positivity
  calc
    normSq (stretchAmp k₁ (coherentProject k₁ w₁)
        (coherentProject k₂ w₂)) ≤
        6 * (d₁ + d₂) * normSq (coherentProject k₁ w₁) *
          normSq (coherentProject k₂ w₂) := hproject
    _ ≤ 6 * (d₁ + d₂) * normSq w₁ *
        normSq (coherentProject k₂ w₂) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp₁ hgain)
        (normSq_nonneg _)
    _ ≤ 6 * (d₁ + d₂) * normSq w₁ * normSq w₂ := by
      exact mul_le_mul_of_nonneg_left hp₂
        (mul_nonneg hgain (normSq_nonneg w₁))

end PancakeRealCoherentPairEstimate
end NavierStokes
end FluidDynamics
end Mettapedia
