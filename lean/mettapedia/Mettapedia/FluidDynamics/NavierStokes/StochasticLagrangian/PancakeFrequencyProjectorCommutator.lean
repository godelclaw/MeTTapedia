import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSignedTransportEnergy
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Frequency variation of the actual misalignment projector

The signed transport identity contains the difference of the receiver and
output misalignment projectors.  This module estimates that difference by
first constructing the normalized rank-one geometry.  The denominator records
distance from degeneration of the coherent reference, not a strain eigenvalue
gap.  No dynamical time-integrability assertion is made here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeFrequencyProjectorCommutator

open scoped BigOperators ComplexConjugate
open NormedSpace PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakePeriodicComplexStretch PancakeSignedTransportEnergy
open PancakePeriodicVorticityEquation PancakeSquareDyadicSectorProjector PancakeFrameCovariance

section Normalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Quantitative normalization, with the scale of the first vector exposed. -/
theorem norm_normalize_sub_le (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖normalize u - normalize v‖ ≤ 2 * ‖u - v‖ / ‖u‖ := by
  have he : ‖u‖ • (normalize u - normalize v) =
      (u - v) + (‖v‖ - ‖u‖) • normalize v := by
    rw [smul_sub, sub_smul, norm_smul_normalize, norm_smul_normalize]
    abel
  have h : ‖u‖ * ‖normalize u - normalize v‖ ≤ 2 * ‖u - v‖ := by
    calc
      _ = ‖‖u‖ • (normalize u - normalize v)‖ := by simp [norm_smul]
      _ ≤ ‖u - v‖ + ‖(‖v‖ - ‖u‖) • normalize v‖ := by rw [he]; exact norm_add_le _ _
      _ = ‖u - v‖ + |‖v‖ - ‖u‖| := by rw [norm_smul, norm_normalize hv]; simp
      _ ≤ 2 * ‖u - v‖ := by
        have hh := abs_norm_sub_norm_le v u
        rw [norm_sub_rev v u] at hh
        linarith
  exact (le_div_iff₀ (norm_pos_iff.mpr hu)).mpr (by nlinarith)

end Normalization

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def unitLineProjector (u : E) : E →L[ℂ] E := InnerProductSpace.rankOne ℂ u u

def orthogonalLineProjector (u : E) : E →L[ℂ] E := unitLineProjector (normalize u)

theorem orthogonalLineProjector_apply (u v : E) :
    orthogonalLineProjector u v = (inner ℂ u v / (‖u‖ : ℂ) ^ 2) • u := by
  simp only [orthogonalLineProjector, unitLineProjector, InnerProductSpace.rankOne_apply,
    NormedSpace.normalize, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, smul_smul,
    Complex.coe_algebraMap, map_inv₀, Complex.conj_ofReal]
  congr 1
  ring

theorem complex_inner_self (u : E) : inner ℂ u u = (‖u‖ : ℂ) ^ 2 := by
  simp

theorem norm_unitLineProjector_sub_le (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖unitLineProjector u - unitLineProjector v‖ ≤ 2 * ‖u - v‖ := by
  have he : unitLineProjector u - unitLineProjector v =
      InnerProductSpace.rankOne ℂ (u - v) u + InnerProductSpace.rankOne ℂ v (u - v) := by
    ext x
    simp only [unitLineProjector, sub_apply, add_apply,
      InnerProductSpace.rankOne_apply, inner_sub_left, sub_smul]
    module
  rw [he]
  calc
    _ ≤ ‖InnerProductSpace.rankOne ℂ (u - v) u‖ +
        ‖InnerProductSpace.rankOne ℂ v (u - v)‖ := norm_add_le _ _
    _ = 2 * ‖u - v‖ := by
      rw [InnerProductSpace.norm_rankOne, InnerProductSpace.norm_rankOne, hu, hv]
      ring

theorem norm_orthogonalLineProjector_sub_le (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖orthogonalLineProjector u - orthogonalLineProjector v‖ ≤ 4 * ‖u - v‖ / ‖u‖ := by
  have hp := norm_unitLineProjector_sub_le (normalize u) (normalize v)
    (norm_normalize hu) (norm_normalize hv)
  have hn := norm_normalize_sub_le u v hu hv
  change ‖unitLineProjector (normalize u) - unitLineProjector (normalize v)‖ ≤ _
  calc
    _ ≤ 2 * ‖normalize u - normalize v‖ := hp
    _ ≤ 2 * (2 * ‖u - v‖ / ‖u‖) := by gcongr
    _ = _ := by ring

/-- The coherent reference after projection into the frequency-normal plane. -/
def lerayReference (e k : E) : E := e - orthogonalLineProjector k e

/-- Complement of the coherent line in the full coefficient space. -/
def coherentComplement (e k : E) : E →L[ℂ] E :=
  ContinuousLinearMap.id ℂ E - orthogonalLineProjector (lerayReference e k)

theorem norm_lerayReference_sub_le (e k l : E)
    (he : ‖e‖ = 1) (hk : k ≠ 0) (hl : l ≠ 0) :
    ‖lerayReference e k - lerayReference e l‖ ≤ 4 * ‖k - l‖ / ‖k‖ := by
  have hdiff : lerayReference e k - lerayReference e l =
      -(orthogonalLineProjector k - orthogonalLineProjector l) e := by
    simp only [lerayReference, sub_apply]
    abel
  rw [hdiff, norm_neg]
  calc
    _ ≤ ‖orthogonalLineProjector k - orthogonalLineProjector l‖ * ‖e‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 4 * ‖k - l‖ / ‖k‖ := by
      rw [he, mul_one]
      exact norm_orthogonalLineProjector_sub_le k l hk hl

/-- Frequency variation loses one inverse frequency and one inverse
coherent-reference norm, with no dependence on a mode count. -/
theorem norm_coherentComplement_sub_le (e k l : E)
    (he : ‖e‖ = 1) (hk : k ≠ 0) (hl : l ≠ 0)
    (hpk : lerayReference e k ≠ 0) (hpl : lerayReference e l ≠ 0) :
    ‖coherentComplement e k - coherentComplement e l‖ ≤
      16 * ‖k - l‖ / (‖k‖ * ‖lerayReference e k‖) := by
  have heq : coherentComplement e k - coherentComplement e l =
      -(orthogonalLineProjector (lerayReference e k) -
        orthogonalLineProjector (lerayReference e l)) := by
    unfold coherentComplement
    abel
  rw [heq, norm_neg]
  calc
    _ ≤ 4 * ‖lerayReference e k - lerayReference e l‖ / ‖lerayReference e k‖ :=
      norm_orthogonalLineProjector_sub_le _ _ hpk hpl
    _ ≤ 4 * (4 * ‖k - l‖ / ‖k‖) / ‖lerayReference e k‖ := by
      gcongr
      exact norm_lerayReference_sub_le e k l he hk hl
    _ = _ := by ring

end Geometry

section Periodic

local notation "C3" => EuclideanSpace ℂ (Fin 3)

/-- The existing coefficient vector, with its Euclidean rather than sup norm. -/
def coefficientVec (u : VelocityCoefficient) : C3 := WithLp.toLp 2 u

def frequencyVec (k : Wavevector) : C3 := coefficientVec (wavevectorCoefficient k)

def referenceVec : C3 := coefficientVec referenceCoefficient

theorem inner_coefficientVec (u v : VelocityCoefficient) :
    inner ℂ (coefficientVec u) (coefficientVec v) = coefficientHermitian u v := by
  simp [coefficientVec, EuclideanSpace.inner_toLp_toLp, coefficientHermitian,
    dotProduct, mul_comm]

theorem inner_frequencyVec (k : Wavevector) (v : VelocityCoefficient) :
    inner ℂ (frequencyVec k) (coefficientVec v) = modeDot k v := by
  rw [frequencyVec, inner_coefficientVec]
  simp [coefficientHermitian, wavevectorCoefficient, modeDot]

theorem inner_frequencyVec_self (k : Wavevector) :
    inner ℂ (frequencyVec k) (frequencyVec k) = modeSquare k := by
  rw [frequencyVec, inner_coefficientVec]
  simp [coefficientHermitian, wavevectorCoefficient, modeSquare]

theorem norm_frequencyVec_sq (k : Wavevector) :
    ‖frequencyVec k‖ ^ 2 = ∑ i : Fin 3, (k i : ℝ) ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_frequencyVec_self]
  simp [modeSquare, sq]

theorem modeSquare_eq_norm_sq (k : Wavevector) :
    modeSquare k = ((‖frequencyVec k‖ ^ 2 : ℝ) : ℂ) := by
  rw [← inner_frequencyVec_self, complex_inner_self]
  simp

theorem norm_modeSquare (k : Wavevector) : ‖modeSquare k‖ = ‖frequencyVec k‖ ^ 2 := by
  rw [modeSquare_eq_norm_sq]
  simp

theorem frequencyVec_sub (q l : Wavevector) : frequencyVec (q - l) = frequencyVec q - frequencyVec l := by
  ext i
  simp [frequencyVec, coefficientVec, wavevectorCoefficient]

theorem frequencyVec_ne_zero {k : Wavevector} (hk : k ≠ 0) : frequencyVec k ≠ 0 := by
  intro h
  apply hk
  ext i
  have hi := congrArg (fun v : C3 ↦ v i) h
  simpa [frequencyVec, coefficientVec, wavevectorCoefficient] using hi

/-- A half-aperture condition keeps the coherent denominator safely away
from zero.  It follows from the actual pancake cone when `N ≥ 2`. -/
theorem norm_periodicCoherentMode_ge_half (k : Wavevector)
    (hk : frequencyVec k ≠ 0)
    (hangle : 4 * (k 0 : ℝ) ^ 2 ≤ ‖frequencyVec k‖ ^ 2) :
    1 / 2 ≤ ‖coefficientVec (periodicCoherentMode k)‖ := by
  have hp0 : periodicCoherentMode k 0 =
      ((1 - (k 0 : ℝ) ^ 2 / ‖frequencyVec k‖ ^ 2 : ℝ) : ℂ) := by
    simp [periodicCoherentMode, lerayMode, hk, modeDot, referenceCoefficient,
      Fin.sum_univ_three, modeSquare_eq_norm_sq, Complex.ofReal_div, sq]
  have hnorm : 0 < ‖frequencyVec k‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hk)
  have hfrac : (k 0 : ℝ) ^ 2 / ‖frequencyVec k‖ ^ 2 ≤ 1 / 4 :=
    (div_le_iff₀ hnorm).mpr (by linarith)
  have hc := PiLp.norm_apply_le (coefficientVec (periodicCoherentMode k)) (0 : Fin 3)
  change ‖periodicCoherentMode k 0‖ ≤ _ at hc
  rw [hp0, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hc
  linarith

/-- All required radial and nondegeneracy bounds follow from the actual
identity-frame square-dyadic pancake cone. -/
theorem pancake_frequency_bounds {N : ℕ} (hN : 2 ≤ N) (q : Wavevector)
    (hc : InOrientedSquarePancakeConeAnnulus identityFrame N q) :
    frequencyVec q ≠ 0 ∧
      1 / 2 ≤ ‖coefficientVec (periodicCoherentMode q)‖ ∧
      (N : ℝ) ^ 2 ≤ ‖frequencyVec q‖ ∧ ‖frequencyVec q‖ < 2 * (N : ℝ) ^ 2 := by
  change InRealSquarePancakeConeAnnulus N ((q 0 : ℝ), (q 1 : ℝ), (q 2 : ℝ)) at hc
  rcases hc with ⟨_, hpos, hlow, hhigh, hcone⟩
  simp only [PancakeRealCoherentPairEstimate.normSq,
    PancakeRealCoherentPairEstimate.dot] at hpos hlow hhigh hcone
  have he : ‖frequencyVec q‖ ^ 2 = (q 0 : ℝ) ^ 2 + (q 1 : ℝ) ^ 2 + (q 2 : ℝ) ^ 2 := by
    rw [norm_frequencyVec_sq, Fin.sum_univ_three]
  have hq : frequencyVec q ≠ 0 := by
    intro hh
    rw [hh, norm_zero] at he
    nlinarith
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have ha : 4 * (q 0 : ℝ) ^ 2 ≤ ‖frequencyVec q‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn2) (sq_nonneg (q 0 : ℝ)),
      mul_nonneg (sq_nonneg (N : ℝ)) (sq_nonneg (q 1 : ℝ))]
  refine ⟨hq, norm_periodicCoherentMode_ge_half q hq ha, ?_, ?_⟩
  · nlinarith [norm_nonneg (frequencyVec q), sq_nonneg (N : ℝ)]
  · nlinarith [norm_nonneg (frequencyVec q), sq_nonneg (N : ℝ)]

theorem norm_referenceVec : ‖referenceVec‖ = 1 := by
  have h : ‖referenceVec‖ ^ 2 = 1 := by
    simp [referenceVec, coefficientVec, EuclideanSpace.norm_sq_eq,
      referenceCoefficient, Fin.sum_univ_three]
  nlinarith [norm_nonneg referenceVec]

theorem orthogonalLineProjector_frequencyVec_apply
    (k : Wavevector) (v : VelocityCoefficient) :
    orthogonalLineProjector (frequencyVec k) (coefficientVec v) =
      (modeDot k v / modeSquare k) • frequencyVec k := by
  rw [orthogonalLineProjector_apply, ← complex_inner_self,
    inner_frequencyVec_self, inner_frequencyVec]

theorem modeSquare_ne_zero_of_frequencyVec_ne_zero {k : Wavevector}
    (hk : frequencyVec k ≠ 0) : modeSquare k ≠ 0 := by
  rw [← inner_frequencyVec_self]
  exact inner_self_ne_zero.mpr hk

/-- Identification with the actual periodic Leray reference. -/
theorem coefficientVec_periodicCoherentMode {k : Wavevector}
    (hk : frequencyVec k ≠ 0) :
    coefficientVec (periodicCoherentMode k) = lerayReference referenceVec (frequencyVec k) := by
  have hs := modeSquare_ne_zero_of_frequencyVec_ne_zero hk
  unfold lerayReference referenceVec
  rw [orthogonalLineProjector_frequencyVec_apply]
  ext i
  simp [coefficientVec, frequencyVec, periodicCoherentMode, lerayMode, hs,
    wavevectorCoefficient, PiLp.sub_apply, PiLp.smul_apply]
  ring

/-- The operator estimate concerns exactly the projector in the signed
misalignment-energy identity. -/
theorem coherentComplement_apply_coefficientVec {k : Wavevector}
    (hk : frequencyVec k ≠ 0) (v : VelocityCoefficient) :
    coherentComplement referenceVec (frequencyVec k) (coefficientVec v) =
      coefficientVec (misalignmentComponent k v) := by
  unfold coherentComplement
  rw [sub_apply, ContinuousLinearMap.id_apply, ← coefficientVec_periodicCoherentMode hk,
    orthogonalLineProjector_apply, ← complex_inner_self,
    inner_coefficientVec, inner_coefficientVec]
  rfl

/-- Quantitative frequency variation of the actual periodic misalignment
component, applied to an arbitrary complex coefficient. -/
theorem norm_misalignmentComponent_sub_le
    (q l : Wavevector) (v : VelocityCoefficient)
    (hq : frequencyVec q ≠ 0) (hl : frequencyVec l ≠ 0)
    (hpq : periodicCoherentMode q ≠ 0) (hpl : periodicCoherentMode l ≠ 0) :
    ‖coefficientVec (misalignmentComponent q v - misalignmentComponent l v)‖ ≤
      (16 * ‖frequencyVec q - frequencyVec l‖ /
        (‖frequencyVec q‖ * ‖coefficientVec (periodicCoherentMode q)‖)) * ‖coefficientVec v‖ := by
  have hpq' : lerayReference referenceVec (frequencyVec q) ≠ 0 := by
    rw [← coefficientVec_periodicCoherentMode hq]
    simpa [coefficientVec] using hpq
  have hpl' : lerayReference referenceVec (frequencyVec l) ≠ 0 := by
    rw [← coefficientVec_periodicCoherentMode hl]
    simpa [coefficientVec] using hpl
  have h := norm_coherentComplement_sub_le referenceVec (frequencyVec q) (frequencyVec l)
    norm_referenceVec hq hl hpq' hpl'
  rw [← coefficientVec_periodicCoherentMode hq] at h
  have he : coefficientVec (misalignmentComponent q v - misalignmentComponent l v) =
      (coherentComplement referenceVec (frequencyVec q) -
        coherentComplement referenceVec (frequencyVec l)) (coefficientVec v) := by
    rw [sub_apply, coherentComplement_apply_coefficientVec hq,
      coherentComplement_apply_coefficientVec hl]
    rfl
  rw [he]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))

theorem norm_coefficient_apply_le (v : VelocityCoefficient) (i : Fin 3) :
    ‖v i‖ ≤ ‖coefficientVec v‖ := PiLp.norm_apply_le (coefficientVec v) i

theorem norm_frequency_apply_le (k : Wavevector) (i : Fin 3) :
    ‖(k i : ℂ)‖ ≤ ‖frequencyVec k‖ := PiLp.norm_apply_le (frequencyVec k) i

theorem norm_cross_component_le (k : Wavevector) (w : VelocityCoefficient) (i : Fin 3) :
    ‖coefficientCross (wavevectorCoefficient k) w i‖ ≤
      2 * ‖frequencyVec k‖ * ‖coefficientVec w‖ := by
  have hb (a b : Fin 3) : ‖(k a : ℂ) * w b‖ ≤ ‖frequencyVec k‖ * ‖coefficientVec w‖ := by
    rw [norm_mul]
    exact mul_le_mul (norm_frequency_apply_le k a) (norm_coefficient_apply_le w b)
      (norm_nonneg _) (norm_nonneg _)
  have hd (a b c d : Fin 3) : ‖(k a : ℂ) * w b - (k c : ℂ) * w d‖ ≤
      2 * ‖frequencyVec k‖ * ‖coefficientVec w‖ :=
    (norm_sub_le _ _).trans (by linarith [hb a b, hb c d])
  fin_cases i <;> simpa [coefficientCross, wavevectorCoefficient] using hd _ _ _ _

/-- A non-sharp but dimension-only bound for the physical transport scalar.
The source inverse frequency is kept explicit for the commutator cancellation. -/
theorem norm_transport_scalar_le (k l : Wavevector) (w : VelocityCoefficient)
    (hk : frequencyVec k ≠ 0) :
    ‖modeDot l (complexBiotSavartAmp k w)‖ ≤
      6 * ‖frequencyVec l‖ * ‖coefficientVec w‖ / ‖frequencyVec k‖ := by
  have hb : ‖modeDot l (coefficientCross (wavevectorCoefficient k) w)‖ ≤
      6 * ‖frequencyVec l‖ * ‖frequencyVec k‖ * ‖coefficientVec w‖ := by
    unfold modeDot
    calc
      _ ≤ ∑ i : Fin 3, ‖(l i : ℂ) * coefficientCross (wavevectorCoefficient k) w i‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, ‖frequencyVec l‖ *
          (2 * ‖frequencyVec k‖ * ‖coefficientVec w‖) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul]
        exact mul_le_mul (norm_frequency_apply_le l i) (norm_cross_component_le k w i)
          (norm_nonneg _) (norm_nonneg _)
      _ = _ := by simp; ring
  rw [complexBiotSavartAmp, modeDot_smul, norm_mul, norm_div, norm_one, norm_modeSquare]
  calc
    _ ≤ (1 / ‖frequencyVec k‖ ^ 2) *
        (6 * ‖frequencyVec l‖ * ‖frequencyVec k‖ * ‖coefficientVec w‖) := by gcongr
    _ = _ := by field_simp [norm_ne_zero_iff.mpr hk]

/-- The transport derivative and projector-difference scale cancel for
comparable frequencies away from coherent-reference degeneration.  These
hypotheses allow buffered modes as well as the actual pancake shell. -/
theorem transport_projector_commutator_le
    (sources : Finset Wavevector)
    (omega : FourierVelocity) (q l : Wavevector) (v : VelocityCoefficient)
    (hq0 : frequencyVec q ≠ 0) (hl0 : frequencyVec l ≠ 0)
    (hpq : 1 / 2 ≤ ‖coefficientVec (periodicCoherentMode q)‖)
    (hpl : 1 / 2 ≤ ‖coefficientVec (periodicCoherentMode l)‖)
    (hlq : ‖frequencyVec l‖ ≤ 2 * ‖frequencyVec q‖) :
    ‖coefficientVec (transportMatrix sources omega q l •
      (misalignmentComponent q v - misalignmentComponent l v))‖ ≤
        384 * ‖coefficientVec (omega (q - l))‖ * ‖coefficientVec v‖ := by
  classical
  by_cases hsame : q = l
  · subst l
    simp [coefficientVec]
    positivity
  by_cases hmem : q - l ∈ sources
  · have hk0 := frequencyVec_ne_zero (sub_ne_zero.mpr hsame)
    have hpq0 : periodicCoherentMode q ≠ 0 := by
      intro he
      simp [he, coefficientVec] at hpq
      linarith
    have hpl0 : periodicCoherentMode l ≠ 0 := by
      intro he
      simp [he, coefficientVec] at hpl
      linarith
    have hp := norm_misalignmentComponent_sub_le q l v hq0 hl0 hpq0 hpl0
    rw [← frequencyVec_sub] at hp
    have ht := norm_transport_scalar_le (q - l) l (omega (q - l)) hk0
    have hqn : 0 < ‖frequencyVec q‖ := norm_pos_iff.mpr hq0
    have hkn : 0 < ‖frequencyVec (q - l)‖ := norm_pos_iff.mpr hk0
    have hpn : 0 < ‖coefficientVec (periodicCoherentMode q)‖ := by linarith
    have hratio : 96 * ‖frequencyVec l‖ /
        (‖frequencyVec q‖ * ‖coefficientVec (periodicCoherentMode q)‖) ≤ 384 := by
      apply (div_le_iff₀ (mul_pos hqn hpn)).mpr
      nlinarith [mul_nonneg hqn.le (sub_nonneg.mpr hpq)]
    rw [transportMatrix, if_pos hmem]
    change ‖(modeDot l (complexBiotSavartAmp (q - l) (omega (q - l)))) •
      coefficientVec (misalignmentComponent q v - misalignmentComponent l v)‖ ≤ _
    rw [norm_smul]
    calc
      _ ≤ (6 * ‖frequencyVec l‖ * ‖coefficientVec (omega (q - l))‖ /
          ‖frequencyVec (q - l)‖) *
          ((16 * ‖frequencyVec (q - l)‖ /
            (‖frequencyVec q‖ * ‖coefficientVec (periodicCoherentMode q)‖)) * ‖coefficientVec v‖) :=
        mul_le_mul ht hp (norm_nonneg _) (by positivity)
      _ = (96 * ‖frequencyVec l‖ /
          (‖frequencyVec q‖ * ‖coefficientVec (periodicCoherentMode q)‖)) *
          ‖coefficientVec (omega (q - l))‖ * ‖coefficientVec v‖ := by
        field_simp [ne_of_gt hqn, ne_of_gt hkn, ne_of_gt hpn]
        ring
      _ ≤ _ := by gcongr
  · simp [transportMatrix, hmem, coefficientVec]
    positivity

/-- Specialization to the actual square-dyadic pancake shell, with no
frequency or retained-mode-count dependence in the constant. -/
theorem pancake_transport_projector_commutator_le
    {N : ℕ} (hN : 2 ≤ N) (sources : Finset Wavevector)
    (omega : FourierVelocity) (q l : Wavevector) (v : VelocityCoefficient)
    (hq : InOrientedSquarePancakeConeAnnulus identityFrame N q)
    (hl : InOrientedSquarePancakeConeAnnulus identityFrame N l) :
    ‖coefficientVec (transportMatrix sources omega q l •
      (misalignmentComponent q v - misalignmentComponent l v))‖ ≤
        384 * ‖coefficientVec (omega (q - l))‖ * ‖coefficientVec v‖ := by
  obtain ⟨hq0, hpq, hqlo, _⟩ := pancake_frequency_bounds hN q hq
  obtain ⟨hl0, hpl, _, hlhi⟩ := pancake_frequency_bounds hN l hl
  exact transport_projector_commutator_le sources omega q l v hq0 hl0 hpq hpl (by linarith)

def sourceWeight (sources : Finset Wavevector) (omega : FourierVelocity)
    (q l : Wavevector) : ℝ :=
  if q - l ∈ sources then ‖coefficientVec (omega (q - l))‖ else 0

theorem sourceWeight_nonneg (sources : Finset Wavevector) (omega : FourierVelocity)
    (q l : Wavevector) : 0 ≤ sourceWeight sources omega q l := by
  unfold sourceWeight
  split <;> positivity

theorem sum_sourceWeight_row_le (sources modes : Finset Wavevector)
    (omega : FourierVelocity) (q : Wavevector) :
    (∑ l ∈ modes, sourceWeight sources omega q l) ≤
      ∑ k ∈ sources, ‖coefficientVec (omega k)‖ := by
  classical
  let selected := modes.filter (fun l ↦ q - l ∈ sources)
  have hinj : Set.InjOn (fun l : Wavevector ↦ q - l) selected := by
    intro a ha b hb he
    exact sub_right_inj.mp he
  have hsub : selected.image (fun l ↦ q - l) ⊆ sources := by
    intro k hk
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
    exact (Finset.mem_filter.mp hl).2
  calc
    _ = ∑ k ∈ selected.image (fun l ↦ q - l), ‖coefficientVec (omega k)‖ := by
      rw [Finset.sum_image hinj]
      simp [selected, sourceWeight, Finset.sum_filter]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ norm_nonneg _)

theorem sum_sourceWeight_column_le (sources modes : Finset Wavevector)
    (omega : FourierVelocity) (l : Wavevector) :
    (∑ q ∈ modes, sourceWeight sources omega q l) ≤
      ∑ k ∈ sources, ‖coefficientVec (omega k)‖ := by
  classical
  let selected := modes.filter (fun q ↦ q - l ∈ sources)
  have hinj : Set.InjOn (fun q : Wavevector ↦ q - l) selected := by
    intro a ha b hb he
    exact sub_left_inj.mp he
  have hsub : selected.image (fun q ↦ q - l) ⊆ sources := by
    intro k hk
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
    exact (Finset.mem_filter.mp hq).2
  calc
    _ = ∑ k ∈ selected.image (fun q ↦ q - l), ‖coefficientVec (omega k)‖ := by
      rw [Finset.sum_image hinj]
      simp [selected, sourceWeight, Finset.sum_filter]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ norm_nonneg _)

/-- Finite Schur estimate with no cardinality loss. -/
theorem finite_schur_energy_bound {ι : Type*} (s : Finset ι)
    (a : ι → ι → ℝ) (b : ι → ℝ) (A : ℝ)
    (ha : ∀ q l, 0 ≤ a q l)
    (hrow : ∀ q ∈ s, ∑ l ∈ s, a q l ≤ A)
    (hcol : ∀ l ∈ s, ∑ q ∈ s, a q l ≤ A) :
    (∑ q ∈ s, ∑ l ∈ s, a q l * b q * b l) ≤ A * ∑ q ∈ s, b q ^ 2 := by
  have hp (q l : ι) : a q l * b q * b l ≤
      (a q l * b q ^ 2 + a q l * b l ^ 2) / 2 := by
    nlinarith [mul_nonneg (ha q l) (sq_nonneg (b q - b l))]
  have hsum := Finset.sum_le_sum (s := s) (fun q hq ↦
    Finset.sum_le_sum (s := s) (fun l hl ↦ hp q l))
  have hrow' : (∑ q ∈ s, ∑ l ∈ s, a q l * b q ^ 2) ≤ A * ∑ q ∈ s, b q ^ 2 := by
    simp only [← Finset.sum_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    exact mul_le_mul_of_nonneg_right (hrow q hq) (sq_nonneg _)
  have hcol' : (∑ q ∈ s, ∑ l ∈ s, a q l * b l ^ 2) ≤ A * ∑ q ∈ s, b q ^ 2 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    exact mul_le_mul_of_nonneg_right (hcol l hl) (sq_nonneg _)
  simp only [← Finset.sum_div, Finset.sum_add_distrib] at hsum
  linarith

theorem norm_coefficientVec_sq (v : VelocityCoefficient) :
    ‖coefficientVec v‖ ^ 2 = coefficientEnergy v := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_coefficientVec]
  simp [coefficientHermitian, coefficientEnergy, Complex.normSq_apply]

theorem abs_hermitian_re_le (u v : VelocityCoefficient) :
    |(coefficientHermitian u v).re| ≤ ‖coefficientVec u‖ * ‖coefficientVec v‖ := by
  rw [← inner_coefficientVec]
  exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)

theorem pancake_projector_energy_pair_le
    {N : ℕ} (hN : 2 ≤ N) (sources : Finset Wavevector)
    (omega eta : FourierVelocity) (q l : Wavevector)
    (hq : InOrientedSquarePancakeConeAnnulus identityFrame N q)
    (hl : InOrientedSquarePancakeConeAnnulus identityFrame N l) :
    |(coefficientHermitian (eta q) (transportMatrix sources omega q l •
      (misalignmentComponent q (eta l) - misalignmentComponent l (eta l)))).re| ≤
        384 * sourceWeight sources omega q l * ‖coefficientVec (eta q)‖ * ‖coefficientVec (eta l)‖ := by
  classical
  by_cases hm : q - l ∈ sources
  · have h := pancake_transport_projector_commutator_le hN sources omega q l (eta l) hq hl
    calc
      _ ≤ ‖coefficientVec (eta q)‖ * ‖coefficientVec (transportMatrix sources omega q l •
          (misalignmentComponent q (eta l) - misalignmentComponent l (eta l)))‖ :=
        abs_hermitian_re_le _ _
      _ ≤ ‖coefficientVec (eta q)‖ *
          (384 * ‖coefficientVec (omega (q - l))‖ * ‖coefficientVec (eta l)‖) := by gcongr
      _ = _ := by rw [sourceWeight, if_pos hm]; ring
  · simp [transportMatrix, sourceWeight, hm, coefficientHermitian]

/-- The complete same-shell projector-mismatch transfer is bounded by an
explicit source `ℓ¹` vorticity norm times receiver `ℓ²` energy, uniformly
in the frequency and the retained mode count.  The source time norm is not
asserted to be finite uniformly up to a possible singular time. -/
theorem pancake_projector_energy_sum_le
    {N : ℕ} (hN : 2 ≤ N) (sources modes : Finset Wavevector)
    (omega eta : FourierVelocity)
    (hmode : ∀ q ∈ modes, InOrientedSquarePancakeConeAnnulus identityFrame N q) :
    |∑ q ∈ modes, ∑ l ∈ modes,
      (coefficientHermitian (eta q) (transportMatrix sources omega q l •
        (misalignmentComponent q (eta l) - misalignmentComponent l (eta l)))).re| ≤
      384 * (∑ k ∈ sources, ‖coefficientVec (omega k)‖) *
        (∑ q ∈ modes, coefficientEnergy (eta q)) := by
  have hschur := finite_schur_energy_bound modes (sourceWeight sources omega)
    (fun q ↦ ‖coefficientVec (eta q)‖) (∑ k ∈ sources, ‖coefficientVec (omega k)‖)
    (sourceWeight_nonneg sources omega)
    (fun q _ ↦ sum_sourceWeight_row_le sources modes omega q)
    (fun l _ ↦ sum_sourceWeight_column_le sources modes omega l)
  simp only [norm_coefficientVec_sq] at hschur
  calc
    _ ≤ ∑ q ∈ modes, ∑ l ∈ modes,
        |(coefficientHermitian (eta q) (transportMatrix sources omega q l •
          (misalignmentComponent q (eta l) - misalignmentComponent l (eta l)))).re| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun q _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ q ∈ modes, ∑ l ∈ modes,
        384 * sourceWeight sources omega q l * ‖coefficientVec (eta q)‖ * ‖coefficientVec (eta l)‖ := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro l hl
      exact pancake_projector_energy_pair_le hN sources omega eta q l (hmode q hq) (hmode l hl)
    _ = 384 * (∑ q ∈ modes, ∑ l ∈ modes,
        sourceWeight sources omega q l * ‖coefficientVec (eta q)‖ * ‖coefficientVec (eta l)‖) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ ≤ _ := by nlinarith

/-- The estimate plugs directly into the signed transport contribution to
the previously proved misalignment-energy derivative. -/
theorem pancake_transport_misalignment_energy_le
    {N : ℕ} (hN : 2 ≤ N) (sources modes : Finset Wavevector)
    (omega eta : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = PancakeBlockReality.coefficientConjugate (omega k))
    (hmode : ∀ q ∈ modes, InOrientedSquarePancakeConeAnnulus identityFrame N q) :
    |2 * (∑ q ∈ modes, (coefficientHermitian (misalignmentComponent q (eta q))
      (finiteUnitTorusNegativeTransportCoeff sources modes omega eta q)).re)| ≤
      384 * (∑ k ∈ sources, ‖coefficientVec (omega k)‖) *
        (∑ q ∈ modes, coefficientEnergy (eta q)) := by
  rw [misalignment_transport_identity sources modes omega eta hs hr]
  exact pancake_projector_energy_sum_le hN sources modes omega eta hmode

end Periodic

end Mettapedia.FluidDynamics.NavierStokes.PancakeFrequencyProjectorCommutator
