import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCoherentStretchFactorization
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBilinearKernelScaling
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSmoothCoherentSymbol

/-!
# Smooth six-frequency symbol for normalized coherent stretching

The exact factorization in `PancakeCoherentStretchFactorization` removes one
aperture factor from the bilinear coherent Biot--Savart interaction.  This
module globalizes the remaining normalized symbol by the same nested-cutoff
construction used for the coherent projection.

The algebraic frequency space contains a source and a receiver frequency.
An inner compact cutoff retains a chart where both axial frequencies are
nonzero.  An outer cutoff is one on that support.  Adding
`(1 - outer)^2` to both coherent-line denominators makes every bilinear tensor
entry globally smooth without changing it on the retained chart.

Every localized entry is a genuine Schwartz function.  It is transported to
Euclidean six-space, complexified, and inverse Fourier transformed, giving an
actual nonzero integrable kernel entry with exact Fourier recovery.  Finite
chart/rotation assembly and the variable strain frame remain separate tasks.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeSmoothCoherentStretchSymbol

open MeasureTheory
open PancakeRealCoherentPairEstimate
open PancakeCoherentStretchFactorization
open PancakeBilinearKernelScaling
open PancakeSmoothCoherentSymbol
open scoped ContDiff FourierTransform SchwartzMap

/-- Algebraic source/receiver frequency coordinates. -/
abbrev FrequencyPair := RealVec3 × RealVec3

/-- Source frequency in the aperture-scaled physical chart. -/
def sourceFrequency (delta : ℝ) (p : FrequencyPair) : RealVec3 :=
  scaledPancakeFrequency delta p.1.1 p.1.2.1 p.1.2.2

/-- Receiver frequency in the aperture-scaled physical chart. -/
def receiverFrequency (delta : ℝ) (p : FrequencyPair) : RealVec3 :=
  scaledPancakeFrequency delta p.2.1 p.2.2.1 p.2.2.2

/-- Normalized coherent stretching after the exact aperture factor is
removed. -/
def normalizedStretch (delta : ℝ) (p : FrequencyPair) : RealVec3 :=
  coherentStretchNormalized delta
    p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2.1 p.2.2.2

/-- Smooth nested cutoffs and global nonvanishing certificates for both
coherent projection denominators. -/
structure BufferedStretchCutoff where
  inner : FrequencyPair → ℝ
  outer : FrequencyPair → ℝ
  inner_contDiff : ContDiff ℝ ∞ inner
  outer_contDiff : ContDiff ℝ ∞ outer
  inner_compact : HasCompactSupport inner
  outer_eq_one_on_inner : ∀ p, inner p ≠ 0 → outer p = 1
  source_denominator_ne : ∀ delta p,
    normSq (coherentW (sourceFrequency delta p)) +
      (1 - outer p) ^ 2 ≠ 0
  receiver_denominator_ne : ∀ delta p,
    normSq (coherentW (receiverFrequency delta p)) +
      (1 - outer p) ^ 2 ≠ 0

def sourceBufferedDenominator (D : BufferedStretchCutoff)
    (delta : ℝ) (p : FrequencyPair) : ℝ :=
  normSq (coherentW (sourceFrequency delta p)) + (1 - D.outer p) ^ 2

def receiverBufferedDenominator (D : BufferedStretchCutoff)
    (delta : ℝ) (p : FrequencyPair) : ℝ :=
  normSq (coherentW (receiverFrequency delta p)) + (1 - D.outer p) ^ 2

/-- One output/source/receiver tensor entry of the globally regularized,
normalized coherent stretching symbol. -/
def localizedNormalizedStretchEntry (D : BufferedStretchCutoff)
    (delta : ℝ) (i j l : Fin 3) (p : FrequencyPair) : ℝ :=
  D.inner p *
    (coordinate (coherentW (sourceFrequency delta p)) j /
      sourceBufferedDenominator D delta p) *
    (coordinate (coherentW (receiverFrequency delta p)) l /
      receiverBufferedDenominator D delta p) *
    coordinate (normalizedStretch delta p) i

theorem contDiff_coordinate_sourceCoherentW (delta : ℝ) (j : Fin 3) :
    ContDiff ℝ ∞ (fun p : FrequencyPair ↦
      coordinate (coherentW (sourceFrequency delta p)) j) := by
  fin_cases j <;>
    simp [coordinate, sourceFrequency, scaledPancakeFrequency,
      coherentW, normSq, dot, add, smul, ex] <;>
    fun_prop

theorem contDiff_coordinate_receiverCoherentW (delta : ℝ) (l : Fin 3) :
    ContDiff ℝ ∞ (fun p : FrequencyPair ↦
      coordinate (coherentW (receiverFrequency delta p)) l) := by
  fin_cases l <;>
    simp [coordinate, receiverFrequency, scaledPancakeFrequency,
      coherentW, normSq, dot, add, smul, ex] <;>
    fun_prop

theorem contDiff_coordinate_normalizedStretch (delta : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun p : FrequencyPair ↦
      coordinate (normalizedStretch delta p) i) := by
  fin_cases i <;>
    simp [coordinate, normalizedStretch, coherentStretchNormalized,
      receiverCoupling, scaledPancakeFrequency, smul, add] <;>
    fun_prop

theorem contDiff_sourceBufferedDenominator
    (D : BufferedStretchCutoff) (delta : ℝ) :
    ContDiff ℝ ∞ (sourceBufferedDenominator D delta) := by
  have h0 := contDiff_coordinate_sourceCoherentW delta 0
  have h1 := contDiff_coordinate_sourceCoherentW delta 1
  have h2 := contDiff_coordinate_sourceCoherentW delta 2
  have hout : ContDiff ℝ ∞ (fun p : FrequencyPair ↦ 1 - D.outer p) :=
    contDiff_const.sub D.outer_contDiff
  unfold sourceBufferedDenominator normSq dot
  simpa only [coordinate_zero, coordinate_one, coordinate_two, pow_two] using
    ((((h0.mul h0).add (h1.mul h1)).add (h2.mul h2)).add
      (hout.pow 2))

theorem contDiff_receiverBufferedDenominator
    (D : BufferedStretchCutoff) (delta : ℝ) :
    ContDiff ℝ ∞ (receiverBufferedDenominator D delta) := by
  have h0 := contDiff_coordinate_receiverCoherentW delta 0
  have h1 := contDiff_coordinate_receiverCoherentW delta 1
  have h2 := contDiff_coordinate_receiverCoherentW delta 2
  have hout : ContDiff ℝ ∞ (fun p : FrequencyPair ↦ 1 - D.outer p) :=
    contDiff_const.sub D.outer_contDiff
  unfold receiverBufferedDenominator normSq dot
  simpa only [coordinate_zero, coordinate_one, coordinate_two, pow_two] using
    ((((h0.mul h0).add (h1.mul h1)).add (h2.mul h2)).add
      (hout.pow 2))

theorem contDiff_localizedNormalizedStretchEntry
    (D : BufferedStretchCutoff) (delta : ℝ) (i j l : Fin 3) :
    ContDiff ℝ ∞ (localizedNormalizedStretchEntry D delta i j l) := by
  unfold localizedNormalizedStretchEntry
  have hs := (contDiff_coordinate_sourceCoherentW delta j).div
      (contDiff_sourceBufferedDenominator D delta)
      (D.source_denominator_ne delta)
  have hr := (contDiff_coordinate_receiverCoherentW delta l).div
      (contDiff_receiverBufferedDenominator D delta)
      (D.receiver_denominator_ne delta)
  exact ((D.inner_contDiff.mul hs).mul hr).mul
    (contDiff_coordinate_normalizedStretch delta i)

theorem hasCompactSupport_localizedNormalizedStretchEntry
    (D : BufferedStretchCutoff) (delta : ℝ) (i j l : Fin 3) :
    HasCompactSupport (localizedNormalizedStretchEntry D delta i j l) := by
  unfold localizedNormalizedStretchEntry
  exact D.inner_compact.mul_right.mul_right.mul_right

/-- Every normalized bilinear tensor entry is a Schwartz symbol. -/
def localizedNormalizedStretchEntrySchwartz
    (D : BufferedStretchCutoff) (delta : ℝ) (i j l : Fin 3) :
    𝓢(FrequencyPair, ℝ) :=
  (hasCompactSupport_localizedNormalizedStretchEntry D delta i j l).toSchwartzMap
    (contDiff_localizedNormalizedStretchEntry D delta i j l)

@[simp]
theorem localizedNormalizedStretchEntrySchwartz_apply
    (D : BufferedStretchCutoff) (delta : ℝ) (i j l : Fin 3)
    (p : FrequencyPair) :
    localizedNormalizedStretchEntrySchwartz D delta i j l p =
      localizedNormalizedStretchEntry D delta i j l p := rfl

/-- On the retained chart both buffers vanish and the exact normalized
coherent-projection tensor is recovered. -/
theorem localizedNormalizedStretchEntry_eq_on_inner
    (D : BufferedStretchCutoff) (delta : ℝ) (i j l : Fin 3)
    (p : FrequencyPair) (hp : D.inner p ≠ 0) :
    localizedNormalizedStretchEntry D delta i j l p =
      D.inner p *
        (coordinate (coherentW (sourceFrequency delta p)) j /
          normSq (coherentW (sourceFrequency delta p))) *
        (coordinate (coherentW (receiverFrequency delta p)) l /
          normSq (coherentW (receiverFrequency delta p))) *
        coordinate (normalizedStretch delta p) i := by
  unfold localizedNormalizedStretchEntry sourceBufferedDenominator
    receiverBufferedDenominator
  rw [D.outer_eq_one_on_inner p hp]
  ring_nf

/-! ## Explicit nonvacuous pair cutoff -/

def pairCenter : FrequencyPair := ((1, 0, 1), (0, 0, 1))

def retainedPairBump : ContDiffBump pairCenter :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

def bufferPairBump : ContDiffBump pairCenter :=
  ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩

theorem bufferPairBump_eq_one_of_retainedPairBump_ne_zero
    (p : FrequencyPair) (hp : retainedPairBump p ≠ 0) :
    bufferPairBump p = 1 := by
  apply bufferPairBump.one_of_mem_closedBall
  have hmem : p ∈ Function.support retainedPairBump := hp
  rw [retainedPairBump.support_eq] at hmem
  change dist p pairCenter < retainedPairBump.rOut at hmem
  change dist p pairCenter ≤ bufferPairBump.rIn
  exact hmem.le.trans (by norm_num [retainedPairBump, bufferPairBump])

theorem axial_pos_of_bufferPairBump_ne_zero
    (p : FrequencyPair) (hp : bufferPairBump p ≠ 0) :
    0 < p.1.2.2 ∧ 0 < p.2.2.2 := by
  have hmem : p ∈ Function.support bufferPairBump := hp
  rw [bufferPairBump.support_eq] at hmem
  have hdist : dist p pairCenter < 3 / 4 := by
    simpa [bufferPairBump] using hmem
  simp only [Prod.dist_eq, max_lt_iff] at hdist
  have hcabs : |p.1.2.2 - 1| < 3 / 4 := by
    simpa [pairCenter, Real.dist_eq] using hdist.1.2.2
  have hfabs : |p.2.2.2 - 1| < 3 / 4 := by
    simpa [pairCenter, Real.dist_eq] using hdist.2.2.2
  exact ⟨by have := (abs_lt.mp hcabs).1; linarith,
    by have := (abs_lt.mp hfabs).1; linarith⟩

/-- The chosen buffer quantitatively separates both axial coordinates from
zero.  The constant is independent of the aperture parameter. -/
theorem quarter_lt_axial_of_bufferPairBump_ne_zero
    (p : FrequencyPair) (hp : bufferPairBump p ≠ 0) :
    (1 : ℝ) / 4 < p.1.2.2 ∧ (1 : ℝ) / 4 < p.2.2.2 := by
  have hmem : p ∈ Function.support bufferPairBump := hp
  rw [bufferPairBump.support_eq] at hmem
  have hdist : dist p pairCenter < 3 / 4 := by
    simpa [bufferPairBump] using hmem
  simp only [Prod.dist_eq, max_lt_iff] at hdist
  have hcabs : |p.1.2.2 - 1| < 3 / 4 := by
    simpa [pairCenter, Real.dist_eq] using hdist.1.2.2
  have hfabs : |p.2.2.2 - 1| < 3 / 4 := by
    simpa [pairCenter, Real.dist_eq] using hdist.2.2.2
  exact ⟨by have := (abs_lt.mp hcabs).1; linarith,
    by have := (abs_lt.mp hfabs).1; linarith⟩

/-- Uniform source denominator bound for the explicit buffered chart. -/
theorem explicit_source_denominator_lower (delta : ℝ) (p : FrequencyPair) :
    (1 : ℝ) / 256 ≤
      normSq (coherentW (sourceFrequency delta p)) +
        (1 - bufferPairBump p) ^ 2 := by
  by_cases hp : bufferPairBump p = 0
  · have hnonneg := normSq_nonneg (coherentW (sourceFrequency delta p))
    rw [hp]
    norm_num
    linarith
  · have hc := (quarter_lt_axial_of_bufferPairBump_ne_zero p hp).1
    have hpow : (1 : ℝ) / 256 < p.1.2.2 ^ 4 := by
      have h := pow_lt_pow_left₀ hc (by norm_num : 0 ≤ (1 : ℝ) / 4)
        (by norm_num : (4 : ℕ) ≠ 0)
      norm_num at h ⊢
      exact h
    have hnorm := axial_pow_four_le_normSq_coherentW_scaled delta
      p.1.1 p.1.2.1 p.1.2.2
    change p.1.2.2 ^ 4 ≤
      normSq (coherentW (sourceFrequency delta p)) at hnorm
    nlinarith [sq_nonneg (1 - bufferPairBump p)]

/-- Uniform receiver denominator bound for the explicit buffered chart. -/
theorem explicit_receiver_denominator_lower (delta : ℝ) (p : FrequencyPair) :
    (1 : ℝ) / 256 ≤
      normSq (coherentW (receiverFrequency delta p)) +
        (1 - bufferPairBump p) ^ 2 := by
  by_cases hp : bufferPairBump p = 0
  · have hnonneg := normSq_nonneg (coherentW (receiverFrequency delta p))
    rw [hp]
    norm_num
    linarith
  · have hf := (quarter_lt_axial_of_bufferPairBump_ne_zero p hp).2
    have hpow : (1 : ℝ) / 256 < p.2.2.2 ^ 4 := by
      have h := pow_lt_pow_left₀ hf (by norm_num : 0 ≤ (1 : ℝ) / 4)
        (by norm_num : (4 : ℕ) ≠ 0)
      norm_num at h ⊢
      exact h
    have hnorm := axial_pow_four_le_normSq_coherentW_scaled delta
      p.2.1 p.2.2.1 p.2.2.2
    change p.2.2.2 ^ 4 ≤
      normSq (coherentW (receiverFrequency delta p)) at hnorm
    nlinarith [sq_nonneg (1 - bufferPairBump p)]

theorem explicit_source_denominator_ne (delta : ℝ) (p : FrequencyPair) :
    normSq (coherentW (sourceFrequency delta p)) +
      (1 - bufferPairBump p) ^ 2 ≠ 0 := by
  by_cases hp : bufferPairBump p = 0
  · have hnonneg := normSq_nonneg (coherentW (sourceFrequency delta p))
    rw [hp]
    norm_num
    linarith
  · have hc := (axial_pos_of_bufferPairBump_ne_zero p hp).1.ne'
    have hpos := normSq_coherentW_scaled_pos delta
      p.1.1 p.1.2.1 p.1.2.2 hc
    unfold sourceFrequency
    nlinarith [sq_nonneg (1 - bufferPairBump p)]

theorem explicit_receiver_denominator_ne (delta : ℝ) (p : FrequencyPair) :
    normSq (coherentW (receiverFrequency delta p)) +
      (1 - bufferPairBump p) ^ 2 ≠ 0 := by
  by_cases hp : bufferPairBump p = 0
  · have hnonneg := normSq_nonneg (coherentW (receiverFrequency delta p))
    rw [hp]
    norm_num
    linarith
  · have hf := (axial_pos_of_bufferPairBump_ne_zero p hp).2.ne'
    have hpos := normSq_coherentW_scaled_pos delta
      p.2.1 p.2.2.1 p.2.2.2 hf
    unfold receiverFrequency
    nlinarith [sq_nonneg (1 - bufferPairBump p)]

def explicitBufferedStretchCutoff : BufferedStretchCutoff where
  inner := retainedPairBump
  outer := bufferPairBump
  inner_contDiff := retainedPairBump.contDiff
  outer_contDiff := bufferPairBump.contDiff
  inner_compact := retainedPairBump.hasCompactSupport
  outer_eq_one_on_inner := bufferPairBump_eq_one_of_retainedPairBump_ne_zero
  source_denominator_ne := explicit_source_denominator_ne
  receiver_denominator_ne := explicit_receiver_denominator_ne

/-! ## Joint aperture/frequency control -/

theorem continuous_joint_sourceBufferedDenominator :
    Continuous (fun q : ℝ × FrequencyPair ↦
      sourceBufferedDenominator explicitBufferedStretchCutoff q.1 q.2) := by
  have hbcd : ContDiff ℝ ∞ (bufferPairBump : FrequencyPair → ℝ) :=
    bufferPairBump.contDiff
  have ho : Continuous (fun q : ℝ × FrequencyPair ↦
      explicitBufferedStretchCutoff.outer q.2) :=
    hbcd.continuous.comp continuous_snd
  have hcoord (j : Fin 3) : Continuous (fun q : ℝ × FrequencyPair ↦
      coordinate (coherentW (sourceFrequency q.1 q.2)) j) := by
    fin_cases j <;>
      simp [coordinate, sourceFrequency, scaledPancakeFrequency,
        coherentW, normSq, dot, add, smul, ex] <;>
      fun_prop
  unfold sourceBufferedDenominator normSq dot
  exact ((((hcoord 0).mul (hcoord 0)).add
      ((hcoord 1).mul (hcoord 1))).add
      ((hcoord 2).mul (hcoord 2))).add
      ((continuous_const.sub ho).pow 2)

theorem continuous_joint_receiverBufferedDenominator :
    Continuous (fun q : ℝ × FrequencyPair ↦
      receiverBufferedDenominator explicitBufferedStretchCutoff q.1 q.2) := by
  have hbcd : ContDiff ℝ ∞ (bufferPairBump : FrequencyPair → ℝ) :=
    bufferPairBump.contDiff
  have ho : Continuous (fun q : ℝ × FrequencyPair ↦
      explicitBufferedStretchCutoff.outer q.2) :=
    hbcd.continuous.comp continuous_snd
  have hcoord (j : Fin 3) : Continuous (fun q : ℝ × FrequencyPair ↦
      coordinate (coherentW (receiverFrequency q.1 q.2)) j) := by
    fin_cases j <;>
      simp [coordinate, receiverFrequency, scaledPancakeFrequency,
        coherentW, normSq, dot, add, smul, ex] <;>
      fun_prop
  unfold receiverBufferedDenominator normSq dot
  exact ((((hcoord 0).mul (hcoord 0)).add
      ((hcoord 1).mul (hcoord 1))).add
      ((hcoord 2).mul (hcoord 2))).add
      ((continuous_const.sub ho).pow 2)

/-- The explicit normalized symbol is jointly continuous in the aperture and
all six normalized frequency variables. -/
theorem continuous_joint_localizedNormalizedStretchEntry (i j l : Fin 3) :
    Continuous (fun q : ℝ × FrequencyPair ↦
      localizedNormalizedStretchEntry explicitBufferedStretchCutoff
        q.1 i j l q.2) := by
  have hinner : Continuous (fun q : ℝ × FrequencyPair ↦
      explicitBufferedStretchCutoff.inner q.2) := by
    have hcd : ContDiff ℝ ∞ (retainedPairBump : FrequencyPair → ℝ) :=
      retainedPairBump.contDiff
    exact hcd.continuous.comp continuous_snd
  have hscoord : Continuous (fun q : ℝ × FrequencyPair ↦
      coordinate (coherentW (sourceFrequency q.1 q.2)) j) := by
    fin_cases j <;>
      simp [coordinate, sourceFrequency, scaledPancakeFrequency,
        coherentW, normSq, dot, add, smul, ex] <;>
      fun_prop
  have hrcoord : Continuous (fun q : ℝ × FrequencyPair ↦
      coordinate (coherentW (receiverFrequency q.1 q.2)) l) := by
    fin_cases l <;>
      simp [coordinate, receiverFrequency, scaledPancakeFrequency,
        coherentW, normSq, dot, add, smul, ex] <;>
      fun_prop
  have hncoord : Continuous (fun q : ℝ × FrequencyPair ↦
      coordinate (normalizedStretch q.1 q.2) i) := by
    fin_cases i <;>
      simp [coordinate, normalizedStretch, coherentStretchNormalized,
        receiverCoupling, scaledPancakeFrequency, smul, add] <;>
      fun_prop
  unfold localizedNormalizedStretchEntry
  exact (((hinner.mul
      (hscoord.div continuous_joint_sourceBufferedDenominator
        (fun q ↦ explicit_source_denominator_ne q.1 q.2))).mul
      (hrcoord.div continuous_joint_receiverBufferedDenominator
        (fun q ↦ explicit_receiver_denominator_ne q.1 q.2))).mul hncoord)

/-- Joint smoothness strengthens joint continuity and supplies simultaneous
control of aperture and frequency derivatives on compact parameter sets. -/
theorem contDiff_joint_localizedNormalizedStretchEntry (i j l : Fin 3) :
    ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦
      localizedNormalizedStretchEntry explicitBufferedStretchCutoff
        q.1 i j l q.2) := by
  have hinner : ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦
      explicitBufferedStretchCutoff.inner q.2) :=
    retainedPairBump.contDiff.comp contDiff_snd
  have hscoord : ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦
      coordinate (coherentW (sourceFrequency q.1 q.2)) j) := by
    fin_cases j <;>
      simp [coordinate, sourceFrequency, scaledPancakeFrequency,
        coherentW, normSq, dot, add, smul, ex] <;>
      fun_prop
  have hrcoord : ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦
      coordinate (coherentW (receiverFrequency q.1 q.2)) l) := by
    fin_cases l <;>
      simp [coordinate, receiverFrequency, scaledPancakeFrequency,
        coherentW, normSq, dot, add, smul, ex] <;>
      fun_prop
  have hncoord : ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦
      coordinate (normalizedStretch q.1 q.2) i) := by
    fin_cases i <;>
      simp [coordinate, normalizedStretch, coherentStretchNormalized,
        receiverCoupling, scaledPancakeFrequency, smul, add] <;>
      fun_prop
  have hsden : ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦
      sourceBufferedDenominator explicitBufferedStretchCutoff q.1 q.2) := by
    have ho : ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦
        explicitBufferedStretchCutoff.outer q.2) :=
      bufferPairBump.contDiff.comp contDiff_snd
    have hcoord (r : Fin 3) : ContDiff ℝ ∞
        (fun q : ℝ × FrequencyPair ↦
          coordinate (coherentW (sourceFrequency q.1 q.2)) r) := by
      fin_cases r <;>
        simp [coordinate, sourceFrequency, scaledPancakeFrequency,
          coherentW, normSq, dot, add, smul, ex] <;>
        fun_prop
    unfold sourceBufferedDenominator normSq dot
    exact ((((hcoord 0).mul (hcoord 0)).add
      ((hcoord 1).mul (hcoord 1))).add
      ((hcoord 2).mul (hcoord 2))).add
      ((contDiff_const.sub ho).pow 2)
  have hrden : ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦
      receiverBufferedDenominator explicitBufferedStretchCutoff q.1 q.2) := by
    have ho : ContDiff ℝ ∞ (fun q : ℝ × FrequencyPair ↦
        explicitBufferedStretchCutoff.outer q.2) :=
      bufferPairBump.contDiff.comp contDiff_snd
    have hcoord (r : Fin 3) : ContDiff ℝ ∞
        (fun q : ℝ × FrequencyPair ↦
          coordinate (coherentW (receiverFrequency q.1 q.2)) r) := by
      fin_cases r <;>
        simp [coordinate, receiverFrequency, scaledPancakeFrequency,
          coherentW, normSq, dot, add, smul, ex] <;>
        fun_prop
    unfold receiverBufferedDenominator normSq dot
    exact ((((hcoord 0).mul (hcoord 0)).add
      ((hcoord 1).mul (hcoord 1))).add
      ((hcoord 2).mul (hcoord 2))).add
      ((contDiff_const.sub ho).pow 2)
  unfold localizedNormalizedStretchEntry
  exact (((hinner.mul
      (hscoord.div hsden
        (fun q ↦ explicit_source_denominator_ne q.1 q.2))).mul
      (hrcoord.div hrden
        (fun q ↦ explicit_receiver_denominator_ne q.1 q.2))).mul hncoord)

theorem tsupport_localizedNormalizedStretchEntry_subset_closedBall
    (delta : ℝ) (i j l : Fin 3) :
    tsupport (localizedNormalizedStretchEntry explicitBufferedStretchCutoff
      delta i j l) ⊆
      Metric.closedBall pairCenter retainedPairBump.rOut := by
  calc
    tsupport (localizedNormalizedStretchEntry explicitBufferedStretchCutoff
        delta i j l) ⊆ tsupport explicitBufferedStretchCutoff.inner := by
      unfold localizedNormalizedStretchEntry
      exact (tsupport_mul_subset_left.trans
        (tsupport_mul_subset_left.trans tsupport_mul_subset_left))
    _ = Metric.closedBall pairCenter retainedPairBump.rOut :=
      retainedPairBump.tsupport_eq

/-- The zeroth symbol seminorm is uniform on the physical aperture interval.
This is the first concrete member of the finite seminorm family required for
the uniform inverse-Fourier kernel bound. -/
theorem exists_uniform_localizedNormalizedStretchEntry_bound
    (i j l : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ p : FrequencyPair,
        |localizedNormalizedStretchEntry explicitBufferedStretchCutoff
          delta i j l p| ≤ C := by
  let F : ℝ × FrequencyPair → ℝ := fun q ↦
    |localizedNormalizedStretchEntry explicitBufferedStretchCutoff
      q.1 i j l q.2|
  let K : Set (ℝ × FrequencyPair) :=
    Set.Icc (0 : ℝ) (1 / 2) ×ˢ
      Metric.closedBall pairCenter retainedPairBump.rOut
  have hF : Continuous F :=
    (continuous_joint_localizedNormalizedStretchEntry i j l).abs
  have hK : IsCompact K :=
    isCompact_Icc.prod (isCompact_closedBall pairCenter retainedPairBump.rOut)
  have hbounded : BddAbove (F '' K) :=
    hK.bddAbove_image hF.continuousOn
  rcases hbounded with ⟨M, hM⟩
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro delta hdelta p
  by_cases hp : retainedPairBump p = 0
  · simp [localizedNormalizedStretchEntry, explicitBufferedStretchCutoff, hp]
  · have hpball : p ∈
        Metric.closedBall pairCenter retainedPairBump.rOut := by
      have hpsupport : p ∈ Function.support retainedPairBump := hp
      rw [retainedPairBump.support_eq] at hpsupport
      exact Metric.ball_subset_closedBall hpsupport
    have hFM : F (delta, p) ≤ M :=
      hM (Set.mem_image_of_mem F ⟨hdelta, hpball⟩)
    exact hFM.trans (le_max_left _ _)

theorem exists_uniform_localizedNormalizedStretchEntry_seminorm_zero
    (i j l : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ delta ∈ Set.Icc (0 : ℝ) (1 / 2),
        SchwartzMap.seminorm ℝ 0 0
          (localizedNormalizedStretchEntrySchwartz
            explicitBufferedStretchCutoff delta i j l) ≤ C := by
  rcases exists_uniform_localizedNormalizedStretchEntry_bound i j l with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro delta hdelta
  apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ hC
  intro p
  simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero,
    Real.norm_eq_abs, localizedNormalizedStretchEntrySchwartz_apply] using
      hbound delta hdelta p

theorem retainedPairBump_center : retainedPairBump pairCenter = 1 := by
  apply retainedPairBump.one_of_mem_closedBall
  simp [retainedPairBump]

/-- The explicit normalized bilinear symbol is genuinely nonzero, already at
zero aperture after the exact factor has been removed. -/
theorem explicit_localizedNormalizedStretchEntry_ne_zero :
    localizedNormalizedStretchEntry explicitBufferedStretchCutoff
      0 1 0 0 pairCenter ≠ 0 := by
  have hinner : explicitBufferedStretchCutoff.inner pairCenter ≠ 0 := by
    change retainedPairBump pairCenter ≠ 0
    rw [retainedPairBump_center]
    norm_num
  rw [localizedNormalizedStretchEntry_eq_on_inner _ _ _ _ _ _ hinner]
  change retainedPairBump pairCenter * _ * _ * _ ≠ 0
  rw [retainedPairBump_center]
  norm_num [explicitBufferedStretchCutoff, pairCenter, sourceFrequency,
    receiverFrequency, scaledPancakeFrequency, coherentW, normSq, dot,
    add, smul, ex, normalizedStretch, coherentStretchNormalized,
    receiverCoupling, coordinate]

/-! ## Euclidean six-space Fourier kernel -/

abbrev EuclideanFrequencyPair := EuclideanSpace ℝ (Fin 6)

def euclideanToFrequencyPairLinearEquiv :
    EuclideanFrequencyPair ≃ₗ[ℝ] FrequencyPair where
  toFun ξ := ((ξ 0, ξ 1, ξ 2), (ξ 3, ξ 4, ξ 5))
  invFun p := !₂[p.1.1, p.1.2.1, p.1.2.2,
    p.2.1, p.2.2.1, p.2.2.2]
  left_inv ξ := by ext i; fin_cases i <;> simp
  right_inv p := by ext <;> simp
  map_add' ξ η := by ext <;> simp
  map_smul' c ξ := by ext <;> simp

def euclideanToFrequencyPairEquiv :
    EuclideanFrequencyPair ≃L[ℝ] FrequencyPair :=
  euclideanToFrequencyPairLinearEquiv.toContinuousLinearEquiv

def euclideanNormalizedStretchEntrySchwartz
    (D : BufferedStretchCutoff) (delta : ℝ) (i j l : Fin 3) :
    𝓢(EuclideanFrequencyPair, ℝ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ euclideanToFrequencyPairEquiv
    (localizedNormalizedStretchEntrySchwartz D delta i j l)

def complexNormalizedStretchEntrySchwartz
    (D : BufferedStretchCutoff) (delta : ℝ) (i j l : Fin 3) :
    𝓢(EuclideanFrequencyPair, ℂ) :=
  (euclideanNormalizedStretchEntrySchwartz D delta i j l).postcompCLM
    Complex.ofRealCLM

@[simp]
theorem complexNormalizedStretchEntrySchwartz_apply
    (D : BufferedStretchCutoff) (delta : ℝ) (i j l : Fin 3)
    (ξ : EuclideanFrequencyPair) :
    complexNormalizedStretchEntrySchwartz D delta i j l ξ =
      localizedNormalizedStretchEntry D delta i j l
        (euclideanToFrequencyPairEquiv ξ) := rfl

def normalizedStretchKernelEntry
    (D : BufferedStretchCutoff) (delta : ℝ) (i j l : Fin 3) :
    𝓢(EuclideanFrequencyPair, ℂ) :=
  𝓕⁻ (complexNormalizedStretchEntrySchwartz D delta i j l)

theorem normalizedStretchKernelEntry_integrable
    (D : BufferedStretchCutoff) (delta : ℝ) (i j l : Fin 3) :
    Integrable (normalizedStretchKernelEntry D delta i j l) :=
  (normalizedStretchKernelEntry D delta i j l).integrable

theorem fourier_normalizedStretchKernelEntry
    (D : BufferedStretchCutoff) (delta : ℝ) (i j l : Fin 3) :
    𝓕 (normalizedStretchKernelEntry D delta i j l) =
      complexNormalizedStretchEntrySchwartz D delta i j l := by
  exact FourierTransform.fourier_fourierInv_eq _

/-- The explicit pair center in Euclidean coordinates. -/
def euclideanPairCenter : EuclideanFrequencyPair := !₂[1, 0, 1, 0, 0, 1]

@[simp]
theorem euclideanToFrequencyPairEquiv_pairCenter :
    euclideanToFrequencyPairEquiv euclideanPairCenter = pairCenter := by
  ext <;> simp [euclideanToFrequencyPairEquiv,
    euclideanToFrequencyPairLinearEquiv, euclideanPairCenter, pairCenter]

theorem explicit_complexNormalizedStretchEntrySchwartz_ne_zero :
    complexNormalizedStretchEntrySchwartz explicitBufferedStretchCutoff
      0 1 0 0 ≠ 0 := by
  intro hzero
  have hvalue := congrArg
    (fun f : 𝓢(EuclideanFrequencyPair, ℂ) ↦ f euclideanPairCenter) hzero
  simp only [complexNormalizedStretchEntrySchwartz_apply,
    euclideanToFrequencyPairEquiv_pairCenter, zero_apply] at hvalue
  exact explicit_localizedNormalizedStretchEntry_ne_zero
    (Complex.ofReal_injective hvalue)

/-- The explicit normalized bilinear kernel is nonzero. -/
theorem explicit_normalizedStretchKernelEntry_ne_zero :
    normalizedStretchKernelEntry explicitBufferedStretchCutoff
      0 1 0 0 ≠ 0 := by
  intro hzero
  have hfourier := congrArg
    (fun f : 𝓢(EuclideanFrequencyPair, ℂ) ↦ 𝓕 f) hzero
  rw [fourier_normalizedStretchKernelEntry] at hfourier
  have hfourierZero :
      𝓕 (0 : 𝓢(EuclideanFrequencyPair, ℂ)) =
        (0 : 𝓢(EuclideanFrequencyPair, ℂ)) :=
    FourierTransform.fourier_zero
  exact explicit_complexNormalizedStretchEntrySchwartz_ne_zero
    (hfourier.trans hfourierZero)

/-! ## Assembly of the full bilinear tensor -/

/-- Fourier transformation on Euclidean six-space commutes with bounded
complex-linear postcomposition. -/
theorem fourier_postcompCLM_pair
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : 𝓢(EuclideanFrequencyPair, ℂ)) (L : ℂ →L[ℂ] F) :
    𝓕 (f.postcompCLM L) = (𝓕 f).postcompCLM L := by
  ext ξ
  change 𝓕 (fun x : EuclideanFrequencyPair ↦ L (f x)) ξ =
    L (𝓕 (fun x : EuclideanFrequencyPair ↦ f x) ξ)
  rw [Real.fourier_eq, Real.fourier_eq]
  have hint : Integrable (fun x : EuclideanFrequencyPair ↦
      𝐞 (-(inner ℝ x ξ)) • f x) :=
    (Real.fourierIntegral_convergent_iff ξ).2 f.integrable
  rw [← L.integral_comp_comm hint]
  congr 1
  funext x
  exact (L.map_smul_of_tower (𝐞 (-(inner ℝ x ξ))) (f x)).symm

/-- Elementary bilinear coefficient tensor. -/
def elementaryBilinearTensor (i j l : Fin 3) : CoherentBilinearOperator :=
  Pi.single i (Pi.single j (Pi.single l 1))

/-- Scalar multiplication of a fixed coefficient tensor. -/
def scalarMultipleBilinearTensorCLM (A : CoherentBilinearOperator) :
    ℂ →L[ℂ] CoherentBilinearOperator :=
  (ContinuousLinearMap.lsmul ℂ ℂ).flip A

@[simp]
theorem scalarMultipleBilinearTensorCLM_apply
    (A : CoherentBilinearOperator) (c : ℂ) :
    scalarMultipleBilinearTensorCLM A c = c • A := rfl

/-- The 27 inverse-Fourier entries assembled into one bilinear
coefficient-tensor kernel. -/
def normalizedStretchTensorKernel
    (D : BufferedStretchCutoff) (delta : ℝ) :
    𝓢(EuclideanFrequencyPair, CoherentBilinearOperator) :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
    (normalizedStretchKernelEntry D delta i j l).postcompCLM
      (scalarMultipleBilinearTensorCLM (elementaryBilinearTensor i j l))

/-- The complete localized normalized coherent-stretching tensor symbol. -/
def normalizedStretchTensorSymbol
    (D : BufferedStretchCutoff) (delta : ℝ) :
    𝓢(EuclideanFrequencyPair, CoherentBilinearOperator) :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
    (complexNormalizedStretchEntrySchwartz D delta i j l).postcompCLM
      (scalarMultipleBilinearTensorCLM (elementaryBilinearTensor i j l))

/-- Exact Fourier recovery of all 27 entries simultaneously. -/
theorem fourier_normalizedStretchTensorKernel
    (D : BufferedStretchCutoff) (delta : ℝ) :
    𝓕 (normalizedStretchTensorKernel D delta) =
      normalizedStretchTensorSymbol D delta := by
  simp [normalizedStretchTensorKernel, normalizedStretchTensorSymbol,
    fourier_postcompCLM_pair,
    fourier_normalizedStretchKernelEntry]

theorem normalizedStretchTensorKernel_integrable
    (D : BufferedStretchCutoff) (delta : ℝ) :
    Integrable (normalizedStretchTensorKernel D delta) :=
  (normalizedStretchTensorKernel D delta).integrable

theorem normalizedStretchTensorKernel_continuous
    (D : BufferedStretchCutoff) (delta : ℝ) :
    Continuous (normalizedStretchTensorKernel D delta) :=
  (normalizedStretchTensorKernel D delta).continuous

end PancakeSmoothCoherentStretchSymbol
end NavierStokes
end FluidDynamics
end Mettapedia
