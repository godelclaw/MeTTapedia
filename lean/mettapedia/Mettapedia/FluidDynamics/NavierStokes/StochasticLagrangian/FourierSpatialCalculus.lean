import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPhysicalFields

/-!
# Termwise spatial calculus of rapidly decaying Fourier series on `ℝ³`

For a coefficient field `a` whose Fourier moments of every order are bounded,
the complex field

```text
Φₐ(x) = ∑ₖ exp(2π i ⟨k, x⟩) aₖ
```

is smooth on `ℝ³` and its derivatives are computed term by term: the iterated
derivative along `h₁, …, hₙ` multiplies the `k`-th coefficient by
`∏ⱼ 2π i ⟨k, hⱼ⟩`, and the Laplacian multiplies it by `(2π i)² |k|²`.

For real coefficient fields (`a₋ₖ = conj aₖ`) the field is real. For real,
transverse fields the transport derivative of `Φₐ` along its own real part
regroups by output frequency into the Fourier convection:

```text
(Φₐ · ∇) Φₐ = 2π i ∑_q exp(2π i ⟨q, x⟩) ∑ₚ (q · aₚ) a_{q-p}.
```
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierSpatialCalculus

open scoped BigOperators Topology ContDiff Laplacian ComplexConjugate
open Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLatticeDecayEnvelope PancakeFourierMaterialPaths
open PancakeDyadicDirectionEvolution PancakePeriodicVorticityEquation PancakePeriodicComplexStretch
open PancakeBlockReality PancakeCoefficientLimitEquation PancakeSobolevFiberEnvelope
open PancakeTransverseEnergyFreezing
open FourierTimeRegularity FourierPhysicalFields

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

section Rapid

/-- Uniform rapid decay of one coefficient field. -/
def Rapid (a : FourierVelocity) : Prop := ∀ n : ℕ, ∃ C : ℝ, ∀ k, fourierMoment n a k ≤ C

theorem rapid_of_rapidOn {a : ℝ → FourierVelocity} {s : Set ℝ} (h : RapidOn a s) {t : ℝ}
    (ht : t ∈ s) : Rapid (a t) :=
  fun n ↦ (h n).imp fun _ hC k ↦ hC t ht k

variable {a b : FourierVelocity}

/-- Rapid fields have summable weighted norms of every order. -/
theorem Rapid.summable (ha : Rapid a) (n : ℕ) :
    Summable (fun k ↦ (1 + ‖frequencyVec k‖) ^ n * ‖a k‖) := by
  obtain ⟨C, hC⟩ := ha (n + 4)
  refine (summable_latticeDecayWeight.mul_left C).of_nonneg_of_le (fun k ↦ by positivity)
    fun k ↦ ?_
  exact (norm_le_moment a n k).trans (fourierMoment_le_decay hC k)

theorem Rapid.summable_norm (ha : Rapid a) : Summable (fun k ↦ ‖a k‖) := by
  simpa using ha.summable 0

theorem Rapid.summable_bound (ha : Rapid a) (n : ℕ) :
    Summable (fun k ↦ (6 * Real.pi * (1 + ‖frequencyVec k‖)) ^ n * ‖a k‖) := by
  refine ((ha.summable n).mul_left ((6 * Real.pi) ^ n)).congr fun k ↦ ?_
  rw [mul_pow (6 * Real.pi) (1 + ‖frequencyVec k‖) n]
  ring

/-- Multiplying the coefficients by a symbol of polynomial growth keeps them rapid. -/
theorem Rapid.smul_poly (ha : Rapid a) {σ : Wavevector → ℂ} {K : ℝ} {d : ℕ}
    (hσ : ∀ k, ‖σ k‖ ≤ K * (1 + ‖frequencyVec k‖) ^ d) : Rapid (fun k ↦ σ k • a k) := by
  intro n
  obtain ⟨C, hC⟩ := ha (n + d)
  refine ⟨K * C, fun k ↦ ?_⟩
  have hK : 0 ≤ K := by
    have h1 := (norm_nonneg (σ k)).trans (hσ k)
    have h2 : 0 < (1 + ‖frequencyVec k‖) ^ d := by positivity
    by_contra hneg
    have hK : K < 0 := not_le.mp hneg
    nlinarith
  have hm : fourierMoment n (fun k ↦ σ k • a k) k =
      ‖σ k‖ * ((1 + ‖frequencyVec k‖) ^ n * ‖coefficientVec (a k)‖) := by
    have h : coefficientVec (σ k • a k) = σ k • coefficientVec (a k) := rfl
    unfold fourierMoment
    rw [h, norm_smul]
    ring
  rw [hm]
  have hC' : (1 + ‖frequencyVec k‖) ^ (n + d) * ‖coefficientVec (a k)‖ ≤ C := hC k
  calc ‖σ k‖ * ((1 + ‖frequencyVec k‖) ^ n * ‖coefficientVec (a k)‖)
      ≤ K * (1 + ‖frequencyVec k‖) ^ d * ((1 + ‖frequencyVec k‖) ^ n *
          ‖coefficientVec (a k)‖) := by gcongr; exact hσ k
    _ = K * ((1 + ‖frequencyVec k‖) ^ (n + d) * ‖coefficientVec (a k)‖) := by ring
    _ ≤ K * C := by gcongr

end Rapid

section Characters

theorem modeFunctional_add (k p : Wavevector) (x : ℝ³) :
    modeFunctional (k + p) x = modeFunctional k x + modeFunctional p x := by
  simp only [modeFunctional_apply, realModeDot, Pi.add_apply, Int.cast_add, add_mul,
    Finset.sum_add_distrib]

theorem modeFunctional_neg (k : Wavevector) (x : ℝ³) :
    modeFunctional (-k) x = -modeFunctional k x := by
  simp only [modeFunctional_apply, realModeDot, Pi.neg_apply, Int.cast_neg, neg_mul,
    Finset.sum_neg_distrib]

theorem modeFunctional_single (k : Wavevector) (i : Fin 3) :
    modeFunctional k (EuclideanSpace.single i 1) = k i := by
  rw [modeFunctional_apply, realModeDot]
  simp

theorem phaseFun_add (s s' : ℝ) : phaseFun (s + s') = phaseFun s * phaseFun s' := by
  rw [phaseFun, phaseFun, phaseFun, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem character_add (k p : Wavevector) (x : ℝ³) :
    character (k + p) x = character k x * character p x := by
  rw [character, modeFunctional_add, phaseFun_add]
  rfl

theorem conj_phaseFun (s : ℝ) : conj (phaseFun s) = phaseFun (-s) := by
  rw [phaseFun, phaseFun, ← Complex.exp_conj]
  congr 1
  simp only [unitTorusDerivativePhase, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem conj_character (k : Wavevector) (x : ℝ³) : conj (character k x) = character (-k) x := by
  rw [character, character, conj_phaseFun, modeFunctional_neg]

theorem phaseFun_add_int (s : ℝ) (n : ℤ) : phaseFun (s + n) = phaseFun s := by
  rw [phaseFun_add]
  have h : phaseFun n = 1 := by
    rw [phaseFun, unitTorusDerivativePhase]
    have e : 2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ) = n * (2 * Real.pi * Complex.I) := by
      push_cast
      ring
    rw [e, Complex.exp_int_mul_two_pi_mul_I]
  rw [h, mul_one]

/-- Characters are one-periodic in each coordinate. -/
theorem character_add_single (k : Wavevector) (x : ℝ³) (i : Fin 3) :
    character k (x + EuclideanSpace.single i 1) = character k x := by
  rw [character, map_add, modeFunctional_single, phaseFun_add_int]
  rfl

/-- The iterated derivatives of a character. -/
theorem iteratedFDeriv_character_apply (k : Wavevector) (n : ℕ) (x : ℝ³) (m : Fin n → ℝ³) :
    iteratedFDeriv ℝ n (character k) x m =
      (∏ i, unitTorusDerivativePhase * (modeFunctional k (m i) : ℂ)) * character k x := by
  have he : character k = phaseFun ∘ (modeFunctional k) := rfl
  rw [he, (modeFunctional k).iteratedFDeriv_comp_right contDiff_phaseFun x (by simp),
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_phaseFun,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Complex.real_smul, Complex.ofReal_prod]
  simp only [Function.comp_apply]
  ring

end Characters

section Field

variable {a b : FourierVelocity}

/-- The complex field `∑ₖ exp(2π i ⟨k, x⟩) aₖ`. -/
def field (a : FourierVelocity) (x : ℝ³) : VelocityCoefficient := ∑' k, character k x • a k

/-- The multiplication `z ↦ z • w`. -/
def smulVec (w : VelocityCoefficient) : ℂ →L[ℝ] VelocityCoefficient :=
  ContinuousLinearMap.smulRight (1 : ℂ →L[ℝ] ℂ) w

theorem smulVec_apply (w : VelocityCoefficient) (z : ℂ) : smulVec w z = z • w := by
  simp [smulVec]

theorem norm_smulVec_le (w : VelocityCoefficient) : ‖smulVec w‖ ≤ ‖w‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg w) fun z ↦ by
    rw [smulVec_apply, norm_smul, mul_comm]

theorem term_eq (a : FourierVelocity) (k : Wavevector) :
    (fun x : ℝ³ ↦ character k x • a k) = smulVec (a k) ∘ character k := by
  funext x
  simp [smulVec_apply]

theorem contDiff_term (a : FourierVelocity) (k : Wavevector) :
    ContDiff ℝ ∞ (fun x : ℝ³ ↦ character k x • a k) := by
  rw [term_eq]
  exact (smulVec (a k)).contDiff.comp (contDiff_character k)

theorem norm_iteratedFDeriv_term_le (a : FourierVelocity) (k : Wavevector) (n : ℕ) (x : ℝ³) :
    ‖iteratedFDeriv ℝ n (fun x : ℝ³ ↦ character k x • a k) x‖ ≤
      (6 * Real.pi * (1 + ‖frequencyVec k‖)) ^ n * ‖a k‖ := by
  rw [term_eq, (smulVec (a k)).iteratedFDeriv_comp_left
    ((contDiff_character k).contDiffAt) (i := n) (by simp)]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  calc ‖smulVec (a k)‖ * ‖iteratedFDeriv ℝ n (character k) x‖
      ≤ ‖a k‖ * (6 * Real.pi * (1 + ‖frequencyVec k‖)) ^ n :=
        mul_le_mul (norm_smulVec_le _) (norm_iteratedFDeriv_character_le k n x)
          (norm_nonneg _) (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem iteratedFDeriv_term_apply (a : FourierVelocity) (k : Wavevector) (n : ℕ) (x : ℝ³)
    (m : Fin n → ℝ³) :
    iteratedFDeriv ℝ n (fun x : ℝ³ ↦ character k x • a k) x m =
      character k x • ((∏ i, unitTorusDerivativePhase * (modeFunctional k (m i) : ℂ)) • a k) := by
  rw [term_eq, (smulVec (a k)).iteratedFDeriv_comp_left
    ((contDiff_character k).contDiffAt) (i := n) (by simp),
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, smulVec_apply,
    iteratedFDeriv_character_apply, smul_smul]
  congr 1
  ring

theorem summable_term (ha : Rapid a) (x : ℝ³) : Summable (fun k ↦ character k x • a k) := by
  refine ha.summable_norm.of_norm_bounded fun k ↦ ?_
  rw [norm_smul, norm_character, one_mul]

theorem field_apply (ha : Rapid a) (x : ℝ³) (i : Fin 3) :
    field a x i = ∑' k, character k x * a k i := by
  rw [field, tsum_apply (summable_term ha x)]
  rfl

theorem field_add (ha : Rapid a) (hb : Rapid b) (x : ℝ³) :
    field (a + b) x = field a x + field b x := by
  rw [field, field, field, ← (summable_term ha x).tsum_add (summable_term hb x)]
  simp only [Pi.add_apply, smul_add]

theorem field_smul (z : ℂ) (a : FourierVelocity) (x : ℝ³) :
    field (fun k ↦ z • a k) x = z • field a x := by
  unfold field
  rw [← tsum_const_smul'' z]
  exact tsum_congr fun k ↦ smul_comm _ _ _

/-- **Termwise iterated derivatives.** -/
theorem iteratedFDeriv_field (ha : Rapid a) (n : ℕ) (x : ℝ³) :
    iteratedFDeriv ℝ n (field a) x =
      ∑' k, iteratedFDeriv ℝ n (fun y : ℝ³ ↦ character k y • a k) x := by
  have h := iteratedFDeriv_tsum_apply (𝕜 := ℝ) (N := ⊤)
    (f := fun k (y : ℝ³) ↦ character k y • a k)
    (v := fun m k ↦ (6 * Real.pi * (1 + ‖frequencyVec k‖)) ^ m * ‖a k‖)
    (fun k ↦ contDiff_term a k) (fun m _ ↦ ha.summable_bound m)
    (fun m k y _ ↦ norm_iteratedFDeriv_term_le a k m y) (k := n) le_top x
  exact h

/-- The coefficients of the iterated derivative along `m`. -/
def derivCoeff {n : ℕ} (m : Fin n → ℝ³) (a : FourierVelocity) : FourierVelocity :=
  fun k ↦ (∏ i, unitTorusDerivativePhase * (modeFunctional k (m i) : ℂ)) • a k

theorem iteratedFDeriv_field_apply (ha : Rapid a) (n : ℕ) (x : ℝ³) (m : Fin n → ℝ³) :
    iteratedFDeriv ℝ n (field a) x m = field (derivCoeff m a) x := by
  have hs : Summable (fun k ↦ iteratedFDeriv ℝ n (fun y : ℝ³ ↦ character k y • a k) x) :=
    (ha.summable_bound n).of_norm_bounded fun k ↦ norm_iteratedFDeriv_term_le a k n x
  rw [iteratedFDeriv_field ha n x, ContinuousMultilinearMap.tsum_eval hs]
  simp only [iteratedFDeriv_term_apply]
  rfl

theorem contDiff_field (ha : Rapid a) : ContDiff ℝ ∞ (field a) :=
  contDiff_tsum (N := ⊤) (fun k ↦ contDiff_term a k) (fun m _ ↦ ha.summable_bound m)
    (fun m k y _ ↦ norm_iteratedFDeriv_term_le a k m y)

/-- **Termwise first derivative.** -/
theorem fderiv_field_apply (ha : Rapid a) (x h : ℝ³) :
    fderiv ℝ (field a) x h =
      field (fun k ↦ (unitTorusDerivativePhase * (modeFunctional k h : ℂ)) • a k) x := by
  have e2 : derivCoeff ![h] a = fun k ↦ (unitTorusDerivativePhase *
      (modeFunctional k h : ℂ)) • a k := by
    funext k
    simp [derivCoeff]
  have e := iteratedFDeriv_one_apply (𝕜 := ℝ) (f := field a) (x := x) ![h]
  rw [iteratedFDeriv_field_apply ha, e2] at e
  simpa using e.symm

/-- The Laplacian multiplier `(2π i)² |k|²`. -/
def lapCoeff (a : FourierVelocity) : FourierVelocity :=
  fun k ↦ (unitTorusDerivativePhase ^ 2 * modeSquare k) • a k

theorem Rapid.derivCoeff (ha : Rapid a) {n : ℕ} (m : Fin n → ℝ³) : Rapid (derivCoeff m a) := by
  refine ha.smul_poly (K := ∏ i, 2 * Real.pi * (3 * ‖m i‖)) (d := n) fun k ↦ ?_
  rw [norm_prod]
  have hb : ∀ i, ‖unitTorusDerivativePhase * (modeFunctional k (m i) : ℂ)‖ ≤
      2 * Real.pi * (3 * ‖m i‖) * (1 + ‖frequencyVec k‖) := by
    intro i
    rw [norm_mul, PancakeIncomingLowSourceEnergy.norm_derivativePhase, Complex.norm_real,
      Real.norm_eq_abs]
    have h1 : |modeFunctional k (m i)| ≤ 3 * ‖frequencyVec k‖ * ‖m i‖ := by
      have h := (modeFunctional k).le_opNorm (m i)
      rw [Real.norm_eq_abs] at h
      exact h.trans (mul_le_mul_of_nonneg_right (norm_modeFunctional_le k) (norm_nonneg _))
    have h2 : 3 * ‖frequencyVec k‖ * ‖m i‖ ≤ 3 * ‖m i‖ * (1 + ‖frequencyVec k‖) := by
      nlinarith [norm_nonneg (m i), norm_nonneg (frequencyVec k)]
    calc 2 * Real.pi * |modeFunctional k (m i)|
        ≤ 2 * Real.pi * (3 * ‖m i‖ * (1 + ‖frequencyVec k‖)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = _ := by ring
  calc ∏ i, ‖unitTorusDerivativePhase * (modeFunctional k (m i) : ℂ)‖
      ≤ ∏ i, 2 * Real.pi * (3 * ‖m i‖) * (1 + ‖frequencyVec k‖) :=
        Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) fun i _ ↦ hb i
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Termwise Laplacian.** -/
theorem laplacian_field (ha : Rapid a) (x : ℝ³) : Δ (field a) x = field (lapCoeff a) x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (field a)
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [iteratedFDeriv_field_apply ha]
  have hsym : ∀ k, lapCoeff a k = ∑ i : Fin 3, derivCoeff
      ![EuclideanSpace.basisFun (Fin 3) ℝ i, EuclideanSpace.basisFun (Fin 3) ℝ i] a k := by
    intro k
    simp only [lapCoeff, derivCoeff, ← Finset.sum_smul]
    congr 1
    simp only [EuclideanSpace.basisFun_apply, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, modeFunctional_single, modeSquare, Fin.sum_univ_three]
    push_cast
    ring
  unfold field
  rw [← Summable.tsum_finsetSum fun i _ ↦ summable_term (ha.derivCoeff _) x]
  refine tsum_congr fun k ↦ ?_
  rw [hsym k, Finset.smul_sum]

end Field

section Real

variable {a : FourierVelocity}

/-- Real coefficient fields: `a₋ₖ = conj aₖ`. -/
def IsReal (a : FourierVelocity) : Prop := ∀ k, a (-k) = coefficientConjugate (a k)

theorem conj_field_apply (ha : Rapid a) (hr : IsReal a) (x : ℝ³) (i : Fin 3) :
    conj (field a x i) = field a x i := by
  rw [field_apply ha]
  change star (∑' k, character k x * a k i) = _
  rw [tsum_star]
  have hs : ∀ k, star (character k x * a k i) = character (-k) x * a (-k) i := by
    intro k
    rw [hr k]
    simp only [coefficientConjugate, star_mul', ← conj_character]
    rfl
  simp only [hs]
  exact (Equiv.neg Wavevector).tsum_eq (fun k ↦ character k x * a k i)

theorem re_field_apply (ha : Rapid a) (hr : IsReal a) (x : ℝ³) (i : Fin 3) :
    ((field a x i).re : ℂ) = field a x i :=
  Complex.conj_eq_iff_re.mp (conj_field_apply ha hr x i)

/-- The real part of the field. -/
def realField (a : FourierVelocity) (x : ℝ³) : ℝ³ := complexRealPartEuclideanCLM (field a x)

theorem realPart_apply (w : VelocityCoefficient) (i : Fin 3) :
    complexRealPartEuclideanCLM w i = (w i).re := by
  simp [complexRealPartEuclidean]

theorem realField_apply (a : FourierVelocity) (x : ℝ³) (i : Fin 3) :
    realField a x i = (field a x i).re :=
  realPart_apply _ i

theorem physVelocity_eq (c : ℝ → FourierVelocity) (x : ℝ³) (t : ℝ) :
    physVelocity c x t = realField (c t) x := rfl

theorem contDiff_realField (ha : Rapid a) : ContDiff ℝ ∞ (realField a) :=
  complexRealPartEuclideanCLM.contDiff.comp (contDiff_field ha)

theorem fderiv_realField_apply (ha : Rapid a) (x h : ℝ³) :
    fderiv ℝ (realField a) x h = complexRealPartEuclideanCLM
      (field (fun k ↦ (unitTorusDerivativePhase * (modeFunctional k h : ℂ)) • a k) x) := by
  have hd : HasFDerivAt (field a) (fderiv ℝ (field a) x) x :=
    ((contDiff_field ha).differentiable (by simp) x).hasFDerivAt
  have e : realField a = complexRealPartEuclideanCLM ∘ field a := rfl
  rw [e, (complexRealPartEuclideanCLM.hasFDerivAt.comp x hd).fderiv,
    ContinuousLinearMap.comp_apply, fderiv_field_apply ha]

theorem laplacian_realField (ha : Rapid a) (x : ℝ³) :
    Δ (realField a) x = complexRealPartEuclideanCLM (field (lapCoeff a) x) := by
  have e : realField a = complexRealPartEuclideanCLM ∘ field a := rfl
  rw [e, ((contDiff_field ha).contDiffAt.of_le (by simp)).laplacian_CLM_comp_left,
    Function.comp_apply, laplacian_field ha]

/-- The real transport speed along a real field is the complex one. -/
theorem modeFunctional_realField (ha : Rapid a) (hr : IsReal a) (k : Wavevector) (x : ℝ³) :
    (modeFunctional k (realField a x) : ℂ) = modeDot k (field a x) := by
  rw [modeFunctional_apply, realModeDot, modeDot]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h : ((WithLp.ofLp (realField a x) i : ℝ) : ℂ) = field a x i := by
    rw [← re_field_apply ha hr x i]
    rfl
  rw [h]

end Real

section Advection

variable {a : FourierVelocity}

/-- The shear `(q, p) ↦ (q - p, p)` of pairs of wavevectors. -/
def shearEquiv : Wavevector × Wavevector ≃ Wavevector × Wavevector where
  toFun qp := (qp.1 - qp.2, qp.2)
  invFun kp := (kp.1 + kp.2, kp.2)
  left_inv qp := by simp
  right_inv kp := by simp

theorem shearEquiv_apply (qp : Wavevector × Wavevector) :
    shearEquiv qp = (qp.1 - qp.2, qp.2) := rfl

/-- The divergence symbol `v ↦ k · v` as a continuous complex-linear map. -/
def modeDotCLM (k : Wavevector) : VelocityCoefficient →L[ℂ] ℂ :=
  ∑ i : Fin 3, (k i : ℂ) • ContinuousLinearMap.proj i

theorem modeDotCLM_apply (k : Wavevector) (v : VelocityCoefficient) :
    modeDotCLM k v = modeDot k v := by
  simp [modeDotCLM, modeDot]

theorem norm_modeDot_le_sup (k : Wavevector) (v : VelocityCoefficient) :
    ‖modeDot k v‖ ≤ 3 * (1 + ‖frequencyVec k‖) * ‖v‖ := by
  unfold modeDot
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ i : Fin 3, ‖(k i : ℂ) * v i‖ ≤ (1 + ‖frequencyVec k‖) * ‖v‖ := by
    intro i
    rw [norm_mul, Complex.norm_intCast]
    have h1 : |(k i : ℝ)| ≤ 1 + ‖frequencyVec k‖ := (abs_coord_le k i).trans (by linarith)
    exact mul_le_mul h1 (norm_le_pi_norm v i) (norm_nonneg _) (by positivity)
  calc ∑ i : Fin 3, ‖(k i : ℂ) * v i‖ ≤ ∑ _i : Fin 3, (1 + ‖frequencyVec k‖) * ‖v‖ :=
        Finset.sum_le_sum fun i _ ↦ hb i
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

theorem Rapid.bounded (ha : Rapid a) : ∃ C, ∀ k, ‖a k‖ ≤ C := by
  obtain ⟨C, hC⟩ := ha 0
  exact ⟨C, fun k ↦ by simpa using (norm_le_moment a 0 k).trans (hC k)⟩

/-- The convection terms of a rapid field are summable. -/
theorem summable_convTerm (ha : Rapid a) (q : Wavevector) :
    Summable (fun p ↦ modeDot q (a p) • a (q - p)) := by
  obtain ⟨C, hC⟩ := ha.bounded
  refine (ha.summable_norm.mul_left (3 * (1 + ‖frequencyVec q‖) * C)).of_norm_bounded
    fun p ↦ ?_
  rw [norm_smul]
  have h1 := norm_modeDot_le_sup q (a p)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  calc ‖modeDot q (a p)‖ * ‖a (q - p)‖ ≤ (3 * (1 + ‖frequencyVec q‖) * ‖a p‖) * C :=
        mul_le_mul h1 (hC _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The Fourier convection as a series of vectors, from summability of the terms. -/
theorem infiniteConvection_eq_of_summable {a : FourierVelocity} {q : Wavevector}
    (hs : Summable (fun p ↦ modeDot q (a p) • a (q - p))) :
    infiniteConvection a q = ∑' p, modeDot q (a p) • a (q - p) := by
  funext i
  rw [tsum_apply hs]
  rfl

/-- The Fourier convection as a series of vectors. -/
theorem infiniteConvection_eq (ha : Rapid a) (q : Wavevector) :
    infiniteConvection a q = ∑' p, modeDot q (a p) • a (q - p) :=
  infiniteConvection_eq_of_summable (summable_convTerm ha q)

theorem modeDot_field (ha : Rapid a) (k : Wavevector) (x : ℝ³) :
    modeDot k (field a x) = ∑' p, character p x * modeDot k (a p) := by
  rw [← modeDotCLM_apply, field, ContinuousLinearMap.map_tsum _ (summable_term ha x)]
  refine tsum_congr fun p ↦ ?_
  rw [map_smul, modeDotCLM_apply, smul_eq_mul]

/-- **Regrouping of the transport term by output frequency.** For a rapid,
transverse field, the derivative of `Φₐ` along the complex vector `Φₐ(x)`
is `2π i` times the field of the Fourier convection. -/
theorem field_transport (ha : Rapid a) (htr : ∀ k, modeDot k (a k) = 0) (x : ℝ³) :
    field (fun k ↦ (unitTorusDerivativePhase * modeDot k (field a x)) • a k) x =
      unitTorusDerivativePhase • field (infiniteConvection a) x := by
  set ph := unitTorusDerivativePhase with hph
  let G : Wavevector × Wavevector → VelocityCoefficient := fun kp ↦
    (ph * (character (kp.1 + kp.2) x * modeDot kp.1 (a kp.2))) • a kp.1
  have hG : Summable G := by
    have hf := (ha.summable 1).mul_of_nonneg ha.summable_norm (fun k ↦ by positivity)
      (fun k ↦ norm_nonneg _)
    refine (hf.mul_left (6 * Real.pi)).of_norm_bounded fun kp ↦ ?_
    have h1 := norm_modeDot_le_sup kp.1 (a kp.2)
    simp only [G, norm_smul, norm_mul, norm_character, one_mul, hph,
      PancakeIncomingLowSourceEnergy.norm_derivativePhase, pow_one]
    calc 2 * Real.pi * ‖modeDot kp.1 (a kp.2)‖ * ‖a kp.1‖
        ≤ 2 * Real.pi * (3 * (1 + ‖frequencyVec kp.1‖) * ‖a kp.2‖) * ‖a kp.1‖ := by gcongr
      _ = 6 * Real.pi * ((1 + ‖frequencyVec kp.1‖) * ‖a kp.1‖ * ‖a kp.2‖) := by ring
  have hL : ∀ k, character k x • ((ph * modeDot k (field a x)) • a k) = ∑' p, G (k, p) := by
    intro k
    have hs : Summable (fun p ↦ ph * (character (k + p) x * modeDot k (a p))) := by
      refine ((ha.summable_norm.mul_left (3 * (1 + ‖frequencyVec k‖))).mul_left
        ‖ph‖).of_norm_bounded fun p ↦ ?_
      rw [norm_mul, norm_mul, norm_character, one_mul]
      exact mul_le_mul_of_nonneg_left (norm_modeDot_le_sup k (a p)) (norm_nonneg _)
    simp only [G]
    rw [hs.tsum_smul_const, tsum_mul_left, smul_smul]
    congr 1
    simp only [character_add, mul_assoc]
    rw [tsum_mul_left, ← modeDot_field ha]
    ring
  have hR : ∀ q, (ph * character q x) • infiniteConvection a q =
      ∑' p, G (shearEquiv (q, p)) := by
    intro q
    have hterm : ∀ p, G (shearEquiv (q, p)) =
        (ph * character q x) • (modeDot q (a p) • a (q - p)) := by
      intro p
      simp only [G, shearEquiv_apply, sub_add_cancel]
      rw [PancakeSignedTransportEnergy.modeDot_sub_left, htr p, sub_zero, smul_smul]
      congr 1
      ring
    simp only [hterm]
    rw [tsum_const_smul'', infiniteConvection_eq ha]
  calc field (fun k ↦ (ph * modeDot k (field a x)) • a k) x
      = ∑' k, ∑' p, G (k, p) := tsum_congr hL
    _ = ∑' kp, G kp := hG.tsum_prod.symm
    _ = ∑' qp, G (shearEquiv qp) := (shearEquiv.tsum_eq G).symm
    _ = ∑' q, ∑' p, G (shearEquiv (q, p)) := ((shearEquiv.summable_iff).mpr hG).tsum_prod
    _ = ∑' q, (ph * character q x) • infiniteConvection a q := tsum_congr fun q ↦ (hR q).symm
    _ = ph • field (infiniteConvection a) x := by
        rw [field, ← tsum_const_smul'']
        exact tsum_congr fun q ↦ (smul_smul _ _ _).symm

end Advection

end Mettapedia.FluidDynamics.NavierStokes.FourierSpatialCalculus
