import Mettapedia.QuantumTheory.YangMills.CalibrationSeparation
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The periodic Gaussian Maxwell field has no uniform crossing representation

For dimension `d = m + 3` and side `L = n + 3`, `GaussianField.law m n` is a
centred Gaussian probability measure with the periodic `F₀₁` Maxwell covariance.
The field at `x` is read from link `(x, 0)`; all directions at a base point carry
the same field value. The covariance is the normalized discrete Fourier sum of
the Maxwell symbol, with the zero mode omitted.

`Covariance.tendsto_finite` proves convergence of these sums using Riemann
integration of the bounded symbol, continuous away from zero. Gaussian
characteristic functions give the truncated correlation of `exp(i F₀₁(0)/2)`
and `exp(-i F₀₁(k)/2)` as `exp(-C_n(0)/4) (exp(C_n(k)/4) - 1)`. Its limit
dominates the Maxwell correlation with factor `8 exp(C(0)/4)`.

`false_of_phaseRepresentation` rules out a volume-uniform `CrossingInput` for
any polymer expectations matching these two phase marginals and their joint
expectation at every volume and displacement. The Gaussian construction,
covariance limit, and eventual separation of singleton supports are proved.
`false_of_expectation_eq` specializes this to agreement on every measurable
observable bounded in norm by one.
-/

set_option autoImplicit false
noncomputable section

open Finset Filter MeasureTheory Topology Complex UnitAddTorus Matrix
open scoped ComplexConjugate
open Mettapedia.Combinatorics.PolymerGas
open Mettapedia.QuantumTheory.YangMills.StrongCouplingCrossing

namespace Mettapedia.QuantumTheory.YangMills.FreeFieldNoCrossing

attribute [local instance high] instMeasureSpaceUnitAddCircle

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) := by
  infer_instance

namespace Quadrature

open BoxIntegral

/-- The real unit cube, with the half-open convention used by box integration. -/
def unitBox (ι : Type*) : Box ι := ⟨0, 1, fun _ => by norm_num⟩

theorem unitBox_integralVertices (ι : Type*) : hasIntegralVertices (unitBox ι) :=
  ⟨0, 1, fun _ => by simp [unitBox], fun _ => by simp [unitBox]⟩

variable {ι : Type*} [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Uniform Riemann sums with mesh `1/(n+3)`. -/
def gridSum (n : ℕ) (f : (ι → ℝ) → V) : V :=
  integralSum f (BoxAdditiveMap.toSMul (Measure.toBoxAdditive volume))
    (unitPartition.prepartition (n + 3) (unitBox ι))

/-- Bounded almost-everywhere continuous functions have convergent uniform grid sums. -/
theorem tendsto_gridSum {f : (ι → ℝ) → V}
    (hb : ∃ C : ℝ, ∀ x ∈ (unitBox ι).Icc, ‖f x‖ ≤ C)
    (hc : ∀ᵐ x ∂volume, ContinuousAt f x) :
    Tendsto (fun n => gridSum n f) atTop (𝓝 (∫ x in (unitBox ι : Set (ι → ℝ)), f x)) := by
  have hi := AEContinuous.hasBoxIntegral (volume : Measure (ι → ℝ)) hb hc IntegrationParams.Riemann
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨r, hr₁, hr₂⟩ := (hasIntegral_iff.mp hi) (ε / 2) (half_pos hε)
  refine ⟨⌈(r 0 0 : ℝ)⁻¹⌉₊, fun n hn => lt_of_le_of_lt ?_ (half_lt_self_iff.mpr hε)⟩
  apply hr₂ 0 _ _ (unitPartition.prepartition_isPartition (n + 3) (unitBox_integralVertices ι))
  refine ⟨?_, fun _ => ?_, fun h => ?_, fun h => ?_⟩
  · rw [show r 0 = fun _ => r 0 0 from funext_iff.mpr (hr₁ 0 rfl)]
    apply unitPartition.prepartition_isSubordinate (n + 3) (unitBox ι)
    rw [Nat.cast_add, Nat.cast_ofNat, one_div,
      inv_le_comm₀ (by positivity : (0 : ℝ) < n + 3) (r 0 0).prop]
    have hn' : (⌈(r 0 0 : ℝ)⁻¹⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    linarith [Nat.le_ceil ((r 0 0 : ℝ)⁻¹)]
  · exact unitPartition.prepartition_isHenstock _ _
  · simp only [IntegrationParams.Riemann, Bool.false_eq_true] at h
  · simp only [IntegrationParams.Riemann, Bool.false_eq_true] at h

/-- Integer momentum indices of the uniform partition. -/
abbrev Mode (ι : Type*) [Fintype ι] (n : ℕ) :=
  {ν : ι → ℤ // ν ∈ unitPartition.admissibleIndex (n + 3) (unitBox ι)}

theorem mem_mode_iff (n : ℕ) (ν : ι → ℤ) :
    ν ∈ unitPartition.admissibleIndex (n + 3) (unitBox ι) ↔
      ∀ i, 0 ≤ ν i ∧ ν i ≤ (n : ℤ) + 2 := by
  simp only [unitPartition.mem_admissibleIndex_iff, Box.le_iff_bounds,
    unitPartition.box_lower, unitPartition.box_upper, unitBox, Pi.le_def,
    Pi.zero_apply, Pi.one_apply, ← forall_and]
  have hp : (0 : ℝ) < (n + 3 : ℕ) := by positivity
  simp only [le_div_iff₀ hp, div_le_iff₀ hp, zero_mul, one_mul]
  push_cast
  norm_cast
  exact forall_congr' fun i => by omega

/-- Negation permutes the right-endpoint momentum grid, fixing its zero mode. -/
def negMode {n : ℕ} (p : Mode ι n) : Mode ι n :=
  ⟨fun i => if p.val i = (n : ℤ) + 2 then p.val i else (n : ℤ) + 1 - p.val i,
    (mem_mode_iff n _).mpr fun i => by
      have hi := (mem_mode_iff n p.val).mp p.property i
      split_ifs <;> omega⟩

theorem negMode_involutive (n : ℕ) : Function.Involutive (@negMode ι _ n) := by
  intro p
  apply Subtype.ext
  funext i
  have hi := (mem_mode_iff n p.val).mp p.property i
  simp only [negMode]
  split_ifs <;> omega

def negModeEquiv (n : ℕ) : Mode ι n ≃ Mode ι n :=
  ⟨negMode, negMode, negMode_involutive n, negMode_involutive n⟩

/-- Momentum representatives `(ν+1)/(n+3)`, with `0 ≤ νᵢ < n+3`. -/
def momentum (n : ℕ) (p : Mode ι n) : UnitAddTorus ι :=
  fun i => (unitPartition.tag (n + 3) p.val i : UnitAddCircle)

theorem momentum_negMode {n : ℕ} (p : Mode ι n) : momentum n (negMode p) = -momentum n p := by
  funext i
  have hp : (n + 3 : ℝ) ≠ 0 := by positivity
  have hone : ((1 : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨1, by simp⟩
  simp only [momentum, unitPartition.tag_apply, negMode, Pi.neg_apply]
  split_ifs with hi
  · rw [hi]
    push_cast
    have he : ((n : ℝ) + 2 + 1) / (n + 3) = 1 := by field_simp; ring
    rw [he]
    simp [hone]
  · push_cast
    have he : ((n : ℝ) + 1 - (p.val i : ℝ) + 1) / (n + 3) =
        1 - ((p.val i : ℝ) + 1) / (n + 3) := by field_simp; ring
    rw [he, AddCircle.coe_sub]
    simp [hone]

omit [CompleteSpace V] in
theorem gridSum_eq (n : ℕ) (f : (ι → ℝ) → V) :
    gridSum n f = ((1 : ℝ) / (n + 3 : ℝ) ^ Fintype.card ι) •
      ∑ p : Mode ι n, f (unitPartition.tag (n + 3) p.val) := by
  classical
  unfold gridSum integralSum
  change (∑ J ∈ (unitPartition.admissibleIndex (n + 3) (unitBox ι)).image
      (unitPartition.box (n + 3)), _) = _
  rw [sum_image]
  · rw [← Finset.sum_coe_sort, Finset.smul_sum]
    apply sum_congr rfl
    intro p _
    rw [unitPartition.prepartition_tag _ p.property]
    simp only [BoxAdditiveMap.toSMul_apply, Measure.toBoxAdditive_apply,
      measureReal_def, unitPartition.volume_box, ENNReal.toReal_div,
      ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.toReal_natCast]
    norm_cast
  · exact fun _ _ _ _ h => unitPartition.box_injective _ h

end Quadrature

namespace Covariance

open FreeMaxwellNonClustering

variable {m : ℕ}

/-- The lifted Fourier integrand of the Maxwell covariance. -/
def integrand (k : Fin (m + 3) → ℤ) (x : Fin (m + 3) → ℝ) : ℂ :=
  mFourier (-k) (fun i => (x i : UnitAddCircle)) *
    (symbol (fun i => (x i : UnitAddCircle)) : ℂ)

/-- The finite periodic Fourier covariance, including the zero symbol at zero momentum. -/
def finite (n : ℕ) (k : Fin (m + 3) → ℤ) : ℂ := Quadrature.gridSum n (integrand k)

theorem norm_integrand_le (k : Fin (m + 3) → ℤ) (x : Fin (m + 3) → ℝ) :
    ‖integrand k x‖ ≤ 1 := by
  have hs := symbol_mem_Icc (fun i => (x i : UnitAddCircle))
  have hf : ‖mFourier (-k) (fun i => (x i : UnitAddCircle))‖ ≤ 1 := by
    simpa only [mFourier_norm] using (mFourier (-k)).norm_coe_le_norm (fun i => (x i : UnitAddCircle))
  rw [integrand, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
  exact (mul_le_mul_of_nonneg_right hf hs.1).trans (by simpa using hs.2)

theorem ae_continuousAt_integrand (k : Fin (m + 3) → ℤ) :
    ∀ᵐ x : Fin (m + 3) → ℝ ∂volume, ContinuousAt (integrand k) x := by
  have hcoord : ∀ᵐ x : Fin (m + 3) → ℝ ∂volume, ∀ j : ℤ, x 0 ≠ (j : ℝ) := by
    rw [ae_all_iff]
    intro j
    rw [ae_iff]
    simp only [not_not]
    exact Measure.pi_hyperplane (fun _ : Fin (m + 3) => (volume : Measure ℝ)) 0 (j : ℝ)
  filter_upwards [hcoord] with x hx
  have hzero : (x 0 : UnitAddCircle) ≠ 0 := by
    intro he
    obtain ⟨j, hj⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp he
    exact hx j (by simpa using hj.symm)
  have hpos : 0 < momentumSqTotal (fun i => (x i : UnitAddCircle)) := by
    exact (momentumSq_pos hzero).trans_le (single_le_sum
      (fun i _ => momentumSq_nonneg i _) (mem_univ 0))
  have hq : Continuous (fun x : Fin (m + 3) → ℝ => fun i => (x i : UnitAddCircle)) := by fun_prop
  have hs := continuousOn_symbol.continuousAt (isOpen_momentumOffOrigin.mem_nhds hpos.ne')
  exact ((mFourier (-k)).continuous.comp hq).continuousAt.mul (hs.comp hq.continuousAt)

theorem tendsto_finite (k : Fin (m + 3) → ℤ) :
    Tendsto (fun n => finite n k) atTop (𝓝 (fieldStrengthCorrelation k)) := by
  have h := Quadrature.tendsto_gridSum
    ⟨1, fun x _ => norm_integrand_le k x⟩ (ae_continuousAt_integrand k)
  have he : (∫ x in (Quadrature.unitBox (Fin (m + 3)) : Set (Fin (m + 3) → ℝ)), integrand k x) =
      fieldStrengthCorrelation k := by
    rw [fieldStrengthCorrelation, mFourierCoeff_eq_integral _ _ (fun _ => 0)]
    have hset : (Quadrature.unitBox (Fin (m + 3)) : Set (Fin (m + 3) → ℝ)) =
        {x | ∀ i, x i ∈ Set.Ioc 0 (0 + 1)} := by
      ext x
      simp [Quadrature.unitBox, BoxIntegral.Box.mem_def]
    rw [hset]
    rfl
  exact he ▸ h

theorem finite_eq_sum (n : ℕ) (k : Fin (m + 3) → ℤ) :
    finite n k = ((1 : ℝ) / (n + 3 : ℝ) ^ (m + 3)) •
      ∑ p : Quadrature.Mode (Fin (m + 3)) n,
        mFourier (-k) (Quadrature.momentum n p) * (symbol (Quadrature.momentum n p) : ℂ) := by
  unfold finite
  rw [Quadrature.gridSum_eq]
  simp only [Fintype.card_fin]
  rfl

/-- The zero momentum contributes zero, so the sum is the usual zero-mode-removed covariance. -/
theorem finite_eq_sum_nonzero (n : ℕ) (k : Fin (m + 3) → ℤ) :
    finite n k = ((1 : ℝ) / (n + 3 : ℝ) ^ (m + 3)) •
      ∑ p ∈ (univ : Finset (Quadrature.Mode (Fin (m + 3)) n)).filter
        (fun p => Quadrature.momentum n p ≠ 0),
        mFourier (-k) (Quadrature.momentum n p) * (symbol (Quadrature.momentum n p) : ℂ) := by
  classical
  rw [finite_eq_sum]
  congr 1
  symm
  apply sum_subset (filter_subset _ _)
  intro p hp hn
  have hz : Quadrature.momentum n p = 0 := by simpa [hp] using hn
  simp [hz, symbol, momentumSq, momentumSqTotal]

theorem mFourier_apply_norm (k : Fin (m + 3) → ℤ) (x : UnitAddTorus (Fin (m + 3))) :
    ‖mFourier k x‖ = 1 := by
  simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply,
    Circle.norm_coe, prod_const_one]

theorem mFourier_neg_argument (k : Fin (m + 3) → ℤ) (x : UnitAddTorus (Fin (m + 3))) :
    mFourier k (-x) = conj (mFourier k x) := by
  simp [mFourier, fourier_apply, smul_neg]

theorem symbol_neg (x : UnitAddTorus (Fin (m + 3))) : symbol (-x) = symbol x := by
  have he : ∀ i, momentumSq i (-x) = momentumSq i x := by
    intro i
    have hf : fourier 1 (-(x i)) = conj (fourier 1 (x i)) := by
      simp only [fourier_apply, smul_neg, fourier_neg']
    change ‖fourier 1 (-(x i)) - 1‖ ^ 2 = ‖fourier 1 (x i) - 1‖ ^ 2
    rw [hf, show conj (fourier 1 (x i)) - 1 = conj (fourier 1 (x i) - 1) by simp,
      Complex.norm_conj]
  simp only [symbol, momentumSqTotal, he]

theorem finite_conj (n : ℕ) (k : Fin (m + 3) → ℤ) :
    conj (finite n k) = finite n k := by
  rw [finite_eq_sum]
  simp only [Complex.real_smul, map_sum, map_mul, Complex.conj_ofReal]
  congr 1
  calc
    (∑ p : Quadrature.Mode (Fin (m + 3)) n,
      conj (mFourier (-k) (Quadrature.momentum n p)) *
        (symbol (Quadrature.momentum n p) : ℂ)) =
      ∑ p : Quadrature.Mode (Fin (m + 3)) n,
        mFourier (-k) (Quadrature.momentum n (Quadrature.negModeEquiv n p)) *
          (symbol (Quadrature.momentum n (Quadrature.negModeEquiv n p)) : ℂ) := by
      apply sum_congr rfl
      intro p _
      have hp : Quadrature.momentum n (Quadrature.negModeEquiv n p) =
          -Quadrature.momentum n p := Quadrature.momentum_negMode p
      rw [hp, mFourier_neg_argument, symbol_neg]
    _ = _ := (Quadrature.negModeEquiv n).sum_comp (fun p =>
      mFourier (-k) (Quadrature.momentum n p) * (symbol (Quadrature.momentum n p) : ℂ))

theorem finite_real (n : ℕ) (k : Fin (m + 3) → ℤ) :
    ((finite n k).re : ℂ) = finite n k := by
  have h := congrArg Complex.im (finite_conj n k)
  apply Complex.ext
  · rfl
  · simp only [Complex.conj_im] at h
    simp only [Complex.ofReal_im]
    linarith

theorem correlation_conj (k : Fin (m + 3) → ℤ) :
    conj (fieldStrengthCorrelation k) = fieldStrengthCorrelation k := by
  rw [fieldStrengthCorrelation, mFourierCoeff, ← integral_conj]
  have he : (fun x : UnitAddTorus (Fin (m + 3)) =>
      conj (mFourier (-k) x • (symbol x : ℂ))) =
      (fun x => mFourier (-k) (-x) • (symbol (-x) : ℂ)) := by
    funext x
    simp [smul_eq_mul, mFourier_neg_argument, symbol_neg]
  rw [he]
  exact integral_neg_eq_self (fun x : UnitAddTorus (Fin (m + 3)) =>
    mFourier (-k) x • (symbol x : ℂ)) volume

theorem correlation_real (k : Fin (m + 3) → ℤ) :
    ((fieldStrengthCorrelation k).re : ℂ) = fieldStrengthCorrelation k := by
  have h := congrArg Complex.im (correlation_conj k)
  apply Complex.ext
  · rfl
  · simp only [Complex.conj_im] at h
    simp only [Complex.ofReal_im]
    linarith

end Covariance

namespace GaussianField

open ProbabilityTheory FreeMaxwellNonClustering Quadrature

variable {m n : ℕ}

/-- A torus link's base point, lifted to integer coordinates. -/
def liftLink (l : Link (m + 3) n) : Fin (m + 3) → ℤ := fun i => (l.1 i).val

/-- A spatial Fourier character at one discrete momentum. -/
def modeValue (p : Mode (Fin (m + 3)) n) (l : Link (m + 3) n) : ℂ :=
  mFourier (liftLink l) (momentum n p)

/-- The nonnegative spectral weight of the Maxwell mode. -/
def weight (p : Mode (Fin (m + 3)) n) : ℝ :=
  (1 / (n + 3 : ℝ) ^ (m + 3)) * symbol (momentum n p)

theorem weight_nonneg (p : Mode (Fin (m + 3)) n) : 0 ≤ weight p :=
  mul_nonneg (by positivity) (symbol_mem_Icc _).1

/-- The real Fourier covariance as a sum of positive rank-one matrices.
Directions at the same base point carry the same copy of `F₀₁`. -/
def covariance (m n : ℕ) : Matrix (Link (m + 3) n) (Link (m + 3) n) ℝ :=
  ∑ p : Mode (Fin (m + 3)) n, weight p •
    (Matrix.vecMulVec (fun l => (modeValue p l).re) (fun l => (modeValue p l).re) +
      Matrix.vecMulVec (fun l => (modeValue p l).im) (fun l => (modeValue p l).im))

theorem covariance_posSemidef (m n : ℕ) : (covariance m n).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro p _
  apply Matrix.PosSemidef.smul _ (weight_nonneg p)
  have hr := Matrix.posSemidef_vecMulVec_self_star (fun l => (modeValue p l).re)
  have hi := Matrix.posSemidef_vecMulVec_self_star (fun l => (modeValue p l).im)
  simpa using hr.add hi

theorem covariance_apply (l r : Link (m + 3) n) :
    covariance m n l r = ∑ p : Mode (Fin (m + 3)) n,
      weight p * (modeValue p l * conj (modeValue p r)).re := by
  simp only [covariance, Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  congr 1
  funext p
  ring

/-- The covariance between arbitrary links is exactly the periodic Fourier sum
at the difference of their base points. -/
theorem covariance_fourier (l r : Link (m + 3) n) :
    (covariance m n l r : ℂ) = Covariance.finite n (liftLink r - liftLink l) := by
  rw [← Covariance.finite_real]
  congr 1
  rw [covariance_apply, Covariance.finite_eq_sum]
  simp only [Complex.smul_re, Complex.re_sum, smul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro p _
  rw [neg_sub, sub_eq_add_neg, mFourier_add, mFourier_neg]
  simp [weight, modeValue, Complex.mul_re]
  ring

theorem period_smul_momentum (p : Mode (Fin (m + 3)) n) (i : Fin (m + 3)) :
    ((n + 3 : ℕ) : ℤ) • momentum n p i = 0 := by
  simp only [momentum, BoxIntegral.unitPartition.tag_apply, Nat.cast_add, Nat.cast_ofNat]
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  norm_num only [Int.cast_add, Int.cast_natCast, Int.cast_ofNat]
  have he : (n + 3 : ℝ) * (((p.val i : ℝ) + 1) / (n + 3 : ℝ)) =
      ((p.val i + 1 : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [he]
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨p.val i + 1, by simp⟩

theorem fourier_reduced (p : Mode (Fin (m + 3)) n) (i : Fin (m + 3)) (j : ℤ) :
    fourier (((j : ZMod (n + 3)).val : ℤ)) (momentum n p i) = fourier j (momentum n p i) := by
  obtain ⟨a, ha⟩ := (ZMod.intCast_eq_iff (n + 3) j (j : ZMod (n + 3))).mp rfl
  have he : j • momentum n p i = (((j : ZMod (n + 3)).val : ℤ)) • momentum n p i := by
    conv_lhs => rw [ha, add_zsmul, mul_comm ((n + 3 : ℕ) : ℤ) a, mul_zsmul,
      period_smul_momentum, smul_zero, add_zero]
  simp only [fourier_apply, he]

theorem modeValue_displaced (p : Mode (Fin (m + 3)) n) (μ : Fin (m + 3))
    (k : Fin (m + 3) → ℤ) :
    modeValue p (CalibrationSeparation.displacementSite n k, μ) = mFourier k (momentum n p) := by
  simp only [modeValue, mFourier, ContinuousMap.coe_mk, liftLink,
    CalibrationSeparation.displacementSite, fourier_reduced]

theorem modeValue_origin (p : Mode (Fin (m + 3)) n) (μ : Fin (m + 3)) :
    modeValue p ((0 : Site (m + 3) n), μ) = 1 := by
  simp [modeValue, liftLink, mFourier]

theorem covariance_origin_displaced (μ : Fin (m + 3)) (k : Fin (m + 3) → ℤ) :
    covariance m n ((0 : Site (m + 3) n), μ) (CalibrationSeparation.displacementSite n k, μ) =
      (Covariance.finite n k).re := by
  rw [covariance_apply, Covariance.finite_eq_sum]
  simp only [modeValue_origin, modeValue_displaced, one_mul, mFourier_neg,
    Complex.smul_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, smul_eq_mul, mul_sum, weight]
  apply sum_congr rfl
  intro p _
  ring

theorem covariance_diagonal (l : Link (m + 3) n) :
    covariance m n l l = (Covariance.finite n (0 : Fin (m + 3) → ℤ)).re := by
  rw [covariance_apply, Covariance.finite_eq_sum]
  have hnorm (p : Mode (Fin (m + 3)) n) : (modeValue p l * conj (modeValue p l)).re = 1 := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq,
      modeValue, Covariance.mFourier_apply_norm, one_pow]
  simp only [hnorm, mul_one, neg_zero, mFourier_zero, ContinuousMap.one_apply, one_mul,
    Complex.smul_re, Complex.re_sum, Complex.ofReal_re, smul_eq_mul, mul_sum, weight]

/-- The centred finite-dimensional Gaussian with the periodic Maxwell covariance. -/
def euclideanLaw (m n : ℕ) : Measure (EuclideanSpace ℝ (Link (m + 3) n)) :=
  multivariateGaussian 0 (covariance m n)

/-- The same field as real variables on links. -/
def law (m n : ℕ) : Measure (Link (m + 3) n → ℝ) :=
  (euclideanLaw m n).map (fun v l => v l)

instance (m n : ℕ) : IsProbabilityMeasure (euclideanLaw m n) :=
  inferInstanceAs (IsProbabilityMeasure (multivariateGaussian 0 (covariance m n)))

instance (m n : ℕ) : IsProbabilityMeasure (law m n) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

instance (m n : ℕ) : IsGaussian (euclideanLaw m n) :=
  inferInstanceAs (IsGaussian (multivariateGaussian 0 (covariance m n)))

instance (m n : ℕ) : IsGaussian (law m n) := by
  change IsGaussian ((euclideanLaw m n).map
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Link (m + 3) n => ℝ)))
  infer_instance

theorem mean_zero (l : Link (m + 3) n) : (∫ ω, ω l ∂law m n) = 0 := by
  rw [law, integral_map (by fun_prop)
    (show AEStronglyMeasurable (fun ω : Link (m + 3) n → ℝ => ω l) _ from
      (measurable_pi_apply l).aestronglyMeasurable)]
  change (∫ v : EuclideanSpace ℝ (Link (m + 3) n), (EuclideanSpace.proj l) v
    ∂multivariateGaussian 0 (covariance m n)) = 0
  rw [ContinuousLinearMap.integral_comp_comm _ IsGaussian.integrable_fun_id,
    integral_id_multivariateGaussian]
  simp

theorem covariance_law (l r : Link (m + 3) n) :
    ProbabilityTheory.covariance (fun ω => ω l) (fun ω => ω r) (law m n) =
      covariance m n l r := by
  rw [law, ProbabilityTheory.covariance_map_fun
    (measurable_pi_apply l).aestronglyMeasurable
    (measurable_pi_apply r).aestronglyMeasurable (by fun_prop)]
  exact covariance_eval_multivariateGaussian (covariance_posSemidef m n) l r

/-- The characteristic function of the real link-labelled field. -/
theorem characteristic (w : Link (m + 3) n → ℝ) :
    (∫ ω, Complex.exp ((w ⬝ᵥ ω : ℝ) * I) ∂law m n) =
      Complex.exp (-((w ⬝ᵥ covariance m n *ᵥ w : ℝ) : ℂ) / 2) := by
  rw [law, integral_map (by fun_prop) (by fun_prop)]
  have h := charFun_multivariateGaussian (μ := 0) (covariance_posSemidef m n)
    (WithLp.toLp 2 w)
  simpa [charFun_apply, EuclideanSpace.inner_eq_star_dotProduct, euclideanLaw, neg_div] using h

/-- A unit-modulus real-field phase. -/
def phase (a x : ℝ) : ℂ := Complex.exp ((a * x : ℝ) * I)

theorem measurable_phase (a : ℝ) : Measurable (phase a) := by
  unfold phase
  fun_prop

@[simp] theorem norm_phase (a x : ℝ) : ‖phase a x‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem covariance_symm (l r : Link (m + 3) n) :
    covariance m n r l = covariance m n l r := by
  simpa using (covariance_posSemidef m n).isHermitian.apply l r

theorem phase_expectation (a : ℝ) (l : Link (m + 3) n) :
    (∫ ω, phase a (ω l) ∂law m n) =
      Complex.exp (-(a ^ 2 * (Covariance.finite n (0 : Fin (m + 3) → ℤ)).re : ℝ) / 2) := by
  classical
  have h := characteristic (m := m) (n := n) (Pi.single l a)
  simp only [single_dotProduct, mulVec, dotProduct_single, covariance_diagonal] at h
  have he : a ^ 2 * (Covariance.finite n (0 : Fin (m + 3) → ℤ)).re =
      a * ((Covariance.finite n (0 : Fin (m + 3) → ℤ)).re * a) := by ring
  simpa only [phase, he, Complex.ofReal_neg] using h

/-- Joint phases follow from one evaluation of the Gaussian characteristic function;
the two links need not be distinct. -/
theorem phase_pair_expectation (a b : ℝ) (l r : Link (m + 3) n) :
    (∫ ω, phase a (ω l) * phase b (ω r) ∂law m n) =
      Complex.exp (-(((a ^ 2 + b ^ 2) *
        (Covariance.finite n (0 : Fin (m + 3) → ℤ)).re +
        2 * a * b * covariance m n l r : ℝ) : ℂ) / 2) := by
  classical
  have h := characteristic (m := m) (n := n) (Pi.single l a + Pi.single r b)
  simp only [add_dotProduct, single_dotProduct, mulVec_add, Pi.add_apply,
    mulVec, dotProduct_single, covariance_diagonal, covariance_symm l r] at h
  calc
    _ = ∫ ω, Complex.exp (((a * ω l + b * ω r : ℝ) : ℂ) * I) ∂law m n := by
      congr 1
      funext ω
      simp [phase, ← Complex.exp_add, add_mul]
    _ = _ := h.trans (by congr 1; push_cast; ring)

/-- The covariance tested by phases of frequency `1/2`, hence Gaussian parameter `t=1/4`. -/
def phaseCorrelation (n : ℕ) (k : Fin (m + 3) → ℤ) : ℂ :=
  (∫ ω, phase (1 / 2) (ω ((0 : Site (m + 3) n), 0)) *
      phase (-1 / 2) (ω (CalibrationSeparation.displacementSite n k, 0)) ∂law m n) -
    (∫ ω, phase (1 / 2) (ω ((0 : Site (m + 3) n), 0)) ∂law m n) *
      (∫ ω, phase (-1 / 2) (ω (CalibrationSeparation.displacementSite n k, 0)) ∂law m n)

theorem phaseCorrelation_eq (n : ℕ) (k : Fin (m + 3) → ℤ) :
    phaseCorrelation n k =
      (Real.exp (-(1 / 4 * (Covariance.finite n (0 : Fin (m + 3) → ℤ)).re)) : ℂ) *
        (Complex.exp ((1 / 4 : ℂ) * ((Covariance.finite n k).re : ℂ)) - 1) := by
  unfold phaseCorrelation
  rw [phase_pair_expectation, phase_expectation, phase_expectation,
    covariance_origin_displaced, Complex.ofReal_exp]
  push_cast
  rw [← Complex.exp_add]
  have he : -(((1 / 2 : ℂ) ^ 2 + (-1 / 2 : ℂ) ^ 2) *
      ((Covariance.finite n (0 : Fin (m + 3) → ℤ)).re : ℂ) +
      2 * (1 / 2) * (-1 / 2) * ((Covariance.finite n k).re : ℂ)) / 2 =
      -(1 / 4 * ((Covariance.finite n (0 : Fin (m + 3) → ℤ)).re : ℂ)) +
        1 / 4 * ((Covariance.finite n k).re : ℂ) := by ring
  rw [he, Complex.exp_add]
  have he' : -((1 / 2 : ℂ) ^ 2 * ((Covariance.finite n (0 : Fin (m + 3) → ℤ)).re : ℂ)) / 2 +
      -((-1 / 2 : ℂ) ^ 2 * ((Covariance.finite n (0 : Fin (m + 3) → ℤ)).re : ℂ)) / 2 =
      -(1 / 4 * ((Covariance.finite n (0 : Fin (m + 3) → ℤ)).re : ℂ)) := by ring
  rw [he']
  ring

theorem phaseCorrelation_eq_fourier (n : ℕ) (k : Fin (m + 3) → ℤ) :
    phaseCorrelation n k =
      (Real.exp (-(1 / 4 * (Covariance.finite n (0 : Fin (m + 3) → ℤ)).re)) : ℂ) *
        (Complex.exp ((1 / 4 : ℂ) * Covariance.finite n k) - 1) := by
  rw [phaseCorrelation_eq, Covariance.finite_real]

/-- The infinite-volume covariance of the two bounded phases. -/
def limitingPhaseCorrelation (k : Fin (m + 3) → ℤ) : ℂ :=
  (Real.exp (-(1 / 4 * (fieldStrengthCorrelation (0 : Fin (m + 3) → ℤ)).re)) : ℂ) *
    (Complex.exp ((1 / 4 : ℂ) * fieldStrengthCorrelation k) - 1)

theorem tendsto_phaseCorrelation (k : Fin (m + 3) → ℤ) :
    Tendsto (fun n => phaseCorrelation n k) atTop (𝓝 (limitingPhaseCorrelation k)) := by
  simp only [phaseCorrelation_eq, limitingPhaseCorrelation]
  rw [← Covariance.correlation_real k]
  have hzero := Complex.continuous_re.continuousAt.tendsto.comp
    (Covariance.tendsto_finite (0 : Fin (m + 3) → ℤ))
  have hk := Complex.continuous_re.continuousAt.tendsto.comp (Covariance.tendsto_finite k)
  exact ((Complex.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_exp.continuousAt.tendsto.comp ((tendsto_const_nhds.mul hzero).neg))).mul
    ((Complex.continuous_exp.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hk))).sub
        tendsto_const_nhds))

theorem covariance_dominated (k : Fin (m + 3) → ℤ) :
    ‖fieldStrengthCorrelation k‖ ≤
      (8 * Real.exp (1 / 4 * (fieldStrengthCorrelation (0 : Fin (m + 3) → ℤ)).re)) *
        ‖limitingPhaseCorrelation k‖ := by
  have h := CrossingInput.norm_fieldStrengthCorrelation_le_gaussian
    (t := 1 / 4) (σ2 := (fieldStrengthCorrelation (0 : Fin (m + 3) → ℤ)).re)
    (by norm_num) (by norm_num) k
  convert h using 1
  unfold limitingPhaseCorrelation
  push_cast
  ring

end GaussianField

open GaussianField CalibrationSeparation

variable {m : ℕ}

/-- The first bounded phase, regarded as a function of its singleton support. -/
def originPhase (n : ℕ) (k : Fin (m + 3) → ℤ)
    (v : firstSupport 0 n k → ℝ) : ℂ :=
  phase (1 / 2) (v ⟨((0 : Site (m + 3) n), 0), by simp [firstSupport]⟩)

/-- The oppositely signed phase at the displaced singleton support. -/
def displacedPhase (n : ℕ) (k : Fin (m + 3) → ℤ)
    (v : secondSupport 0 n k → ℝ) : ℂ :=
  phase (-1 / 2) (v ⟨(displacementSite n k, 0), by simp [secondSupport]⟩)

theorem measurable_originPhase (n : ℕ) (k : Fin (m + 3) → ℤ) :
    Measurable (originPhase n k) := (measurable_phase _).comp (measurable_pi_apply _)

theorem measurable_displacedPhase (n : ℕ) (k : Fin (m + 3) → ℤ) :
    Measurable (displacedPhase n k) := (measurable_phase _).comp (measurable_pi_apply _)

section NoCrossing

variable (ν₀ : Measure ℝ) [IsProbabilityMeasure ν₀]
  (K : ∀ n (S : Finset (Link (m + 3) n)), (S → ℝ) → ℂ)
  (Λ : ∀ n, Finset (Finset (Link (m + 3) n)))

/-- Only three expectations are required: the two phase marginals and their product.
No matching of unbounded field observables is assumed. -/
structure PhaseRepresentation : Prop where
  origin : ∀ n,
    expectation ν₀ (fun ω => phase (1 / 2) (ω ((0 : Site (m + 3) n), 0))) (K n) (Λ n) =
      ∫ ω, phase (1 / 2) (ω ((0 : Site (m + 3) n), 0)) ∂law m n
  displaced : ∀ n (k : Fin (m + 3) → ℤ),
    expectation ν₀ (fun ω => phase (-1 / 2) (ω (displacementSite n k, 0))) (K n) (Λ n) =
      ∫ ω, phase (-1 / 2) (ω (displacementSite n k, 0)) ∂law m n
  pair : ∀ n (k : Fin (m + 3) → ℤ),
    expectation ν₀ (fun ω => phase (1 / 2) (ω ((0 : Site (m + 3) n), 0)) *
      phase (-1 / 2) (ω (displacementSite n k, 0))) (K n) (Λ n) =
      ∫ ω, phase (1 / 2) (ω ((0 : Site (m + 3) n), 0)) *
        phase (-1 / 2) (ω (displacementSite n k, 0)) ∂law m n

/-- The periodic centred Gaussian Maxwell field admits no volume-uniform crossing
representation, already when only the two fixed-frequency phases are matched. -/
theorem false_of_phaseRepresentation
    (h : CrossingInput.CrossingInput (Link (m + 3)) ℝ K)
    (hP : PhaseRepresentation ν₀ K Λ) : False := by
  apply CalibrationSeparation.false_of_tendsto_dominating ν₀ 0 h Λ
    originPhase displacedPhase measurable_originPhase measurable_displacedPhase
    (fun n k v => by simp [originPhase]) (fun n k v => by simp [displacedPhase])
    limitingPhaseCorrelation _ _ covariance_dominated
  intro k
  convert tendsto_phaseCorrelation k using 1
  funext n
  simp only [originPhase, displacedPhase, restrictTo]
  rw [hP.pair, hP.origin, hP.displaced]
  rfl

/-- In particular, matching all bounded measurable expectations cannot coexist
with the crossing input. The phase-only theorem requires much less matching. -/
theorem false_of_expectation_eq
    (h : CrossingInput.CrossingInput (Link (m + 3)) ℝ K)
    (hP : ∀ n (F : (Link (m + 3) n → ℝ) → ℂ), Measurable F →
      (∀ ω, ‖F ω‖ ≤ 1) → expectation ν₀ F (K n) (Λ n) = ∫ ω, F ω ∂law m n) : False := by
  apply false_of_phaseRepresentation ν₀ K Λ h
  constructor
  · intro n
    exact hP n _ ((measurable_phase _).comp (measurable_pi_apply _)) (by simp)
  · intro n k
    exact hP n _ ((measurable_phase _).comp (measurable_pi_apply _)) (by simp)
  · intro n k
    exact hP n _ (((measurable_phase _).comp (measurable_pi_apply _)).mul
      ((measurable_phase _).comp (measurable_pi_apply _))) (by simp)

end NoCrossing

#print axioms Quadrature.tendsto_gridSum
#print axioms Covariance.tendsto_finite
#print axioms GaussianField.covariance_fourier
#print axioms GaussianField.mean_zero
#print axioms GaussianField.covariance_law
#print axioms GaussianField.phaseCorrelation_eq_fourier
#print axioms GaussianField.tendsto_phaseCorrelation
#print axioms false_of_phaseRepresentation
#print axioms false_of_expectation_eq

end Mettapedia.QuantumTheory.YangMills.FreeFieldNoCrossing
