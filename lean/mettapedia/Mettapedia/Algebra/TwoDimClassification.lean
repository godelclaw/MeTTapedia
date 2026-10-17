/-
# Classification of 2-Dimensional Unital Real Algebras

This module proves the classical classification theorem:

**Theorem**: Every 2-dimensional unital associative algebra over ℝ is isomorphic to exactly one of:
- Complex numbers ℂ (where i² = -1)
- Dual numbers ℝ[ε] (where ε² = 0)
- Split-complex numbers ℝ[j] (where j² = +1)

The proof uses the "completing the square" technique:
1. Any 2D unital algebra has a basis {1, e} with e² = a + be for some a, b ∈ ℝ
2. Define e' = e - b/2, then (e')² = a + b²/4 =: μ
3. The sign of μ determines the algebra:
   - μ < 0: Complex (rescale to get i with i² = -1)
   - μ = 0: Dual (already have ε² = 0)
   - μ > 0: Split-complex (rescale to get j with j² = +1)

Key insight for K&S: The bilinearProduct parameterized by μ continuously covers all three cases,
but there are only 3 isomorphism classes - the classification is discrete, not continuous!

The normalized parameter μ depends on the chosen generator. Its sign, rather
than its numerical value, determines the real algebra isomorphism class.
The general basis construction and polynomial quotient presentation use the
shared quadratic presentation modules; no extra algebra carrier is defined.

## References

- Skilling & Knuth (2018), "The Symmetrical Foundation of Measure, Probability, and Quantum Theories"
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.DualNumber
import Mettapedia.Algebra.SplitComplex
import Mettapedia.Algebra.QuadraticPolynomialPresentation
import Mathlib.Tactic

namespace Mettapedia.Algebra.TwoDimClassification

open SplitComplex

/-! ## The μ-Parameterized Product

Following K&S, we define the bilinear product parameterized by μ ∈ ℝ:
  (u₁, u₂) * (v₁, v₂) = (u₁v₁ + μ·u₂v₂, u₁v₂ + u₂v₁)

This gives:
- μ = -1: Complex multiplication
- μ = 0: Dual number multiplication
- μ = +1: Split-complex multiplication
-/

/-- The normalized family is the canonical quadratic algebra with no linear
term. Ring, module and real algebra structures all come from Mathlib. -/
abbrev MuAlgebra (μ : ℝ) := QuadraticAlgebra ℝ μ 0

namespace MuAlgebra

variable (μ : ℝ)

/-- The normalized product has no linear coefficient. -/
@[simp] theorem mul_im (z w : MuAlgebra μ) :
    (z * w).im = z.re * w.im + z.im * w.re := by simp

/-- The distinguished generator satisfies `e² = μ`. -/
def e : MuAlgebra μ := QuadraticAlgebra.omega

@[simp] theorem e_re : (e μ).re = 0 := rfl
@[simp] theorem e_im : (e μ).im = 1 := rfl

@[simp] theorem e_sq : (e μ) * (e μ) = ⟨μ, 0⟩ := by
  ext <;> simp [e]

end MuAlgebra

/-! ## Isomorphisms to Concrete Algebras

We now show that:
- MuAlgebra (-1) ≃ ℂ
- MuAlgebra 1 ≃ SplitComplex
-/

/-- MuAlgebra (-1) is isomorphic to ℂ. -/
noncomputable def muAlgebraNegOneEquivComplex : MuAlgebra (-1) ≃+* ℂ where
  toFun z := ⟨z.re, z.im⟩
  invFun c := ⟨c.re, c.im⟩
  left_inv := fun z => by ext <;> rfl
  right_inv := fun c => by
    apply Complex.ext
    · simp
    · simp
  map_mul' := fun z w => by
    apply Complex.ext
    · simp only [QuadraticAlgebra.re_mul, Complex.mul_re]; ring
    · simp only [MuAlgebra.mul_im, Complex.mul_im]
  map_add' := fun z w => by
    apply Complex.ext <;> simp

/-- MuAlgebra 1 is isomorphic to SplitComplex. -/
noncomputable def muAlgebraOneEquivSplit : MuAlgebra (1 : ℝ) ≃+* SplitComplex where
  toFun z := ⟨z.re, z.im⟩
  invFun s := ⟨s.re, s.im⟩
  left_inv := fun z => by ext <;> rfl
  right_inv := fun s => by ext <;> rfl
  map_mul' := fun z w => by
    ext
    · simp only [QuadraticAlgebra.re_mul, SplitComplex.mul_re]; ring
    · simp only [MuAlgebra.mul_im, SplitComplex.mul_im]
  map_add' := fun z w => by ext <;> simp

/-! ## The Classification Theorem

Now we prove the main classification result.
-/

/-- The three isomorphism classes of 2D unital real algebras. -/
inductive TwoDimAlgebraClass
  | complex      -- i² = -1
  | dual         -- ε² = 0
  | splitComplex -- j² = +1
deriving DecidableEq, Repr

/-- Classification by the sign of μ. -/
noncomputable def classifyByMu (μ : ℝ) : TwoDimAlgebraClass :=
  if μ < 0 then TwoDimAlgebraClass.complex
  else if μ = 0 then TwoDimAlgebraClass.dual
  else TwoDimAlgebraClass.splitComplex

/-- MuAlgebra 0 has ε² = 0 (dual numbers). -/
theorem muAlgebra_zero_e_sq : (MuAlgebra.e 0) * (MuAlgebra.e 0) = (0 : MuAlgebra 0) := by
  ext <;> simp [MuAlgebra.e]

/-- Rescaling: all positive μ give isomorphic algebras.
The map (a, b) ↦ (a, b·√(μ/μ')) scales e² by μ/μ'. -/
noncomputable def muAlgebraRescale (μ μ' : ℝ) (hμ : 0 < μ) (hμ' : 0 < μ') :
    MuAlgebra μ ≃+* MuAlgebra μ' := by
  let k := Real.sqrt (μ / μ')
  let k' := Real.sqrt (μ' / μ)
  have hk_pos : 0 ≤ k := Real.sqrt_nonneg _
  have hk'_pos : 0 ≤ k' := Real.sqrt_nonneg _
  have hkk' : k * k' = 1 := by
    simp only [k, k']
    rw [← Real.sqrt_mul (div_nonneg (le_of_lt hμ) (le_of_lt hμ'))]
    rw [div_mul_div_comm, mul_comm μ' μ, div_self (ne_of_gt (mul_pos hμ hμ'))]
    simp
  have hk'k : k' * k = 1 := by rw [mul_comm]; exact hkk'
  have hksq : k * k = μ / μ' := Real.mul_self_sqrt (div_nonneg (le_of_lt hμ) (le_of_lt hμ'))
  refine ⟨⟨fun z => ⟨z.re, z.im * k⟩, fun z => ⟨z.re, z.im * k'⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro z; ext; rfl; simp only; rw [mul_assoc, hkk', mul_one]
  · intro z; ext; rfl; simp only; rw [mul_assoc, hk'k, mul_one]
  · intro z w
    ext
    · simp only [QuadraticAlgebra.re_mul]
      have h : μ' * (z.im * k) * (w.im * k) = μ * z.im * w.im := by
        calc μ' * (z.im * k) * (w.im * k)
            = μ' * z.im * w.im * (k * k) := by ring
          _ = μ' * z.im * w.im * (μ / μ') := by rw [hksq]
          _ = μ * z.im * w.im := by field_simp
      linarith [h]
    · simp only [MuAlgebra.mul_im]; ring
  · intro z w; ext <;> simp [add_mul]

/-- Rescaling for negative μ values. -/
noncomputable def muAlgebraRescaleNeg (μ μ' : ℝ) (hμ : μ < 0) (hμ' : μ' < 0) :
    MuAlgebra μ ≃+* MuAlgebra μ' := by
  have hdiv_pos : 0 < μ / μ' := div_pos_of_neg_of_neg hμ hμ'
  have hdiv_pos' : 0 < μ' / μ := div_pos_of_neg_of_neg hμ' hμ
  let k := Real.sqrt (μ / μ')
  let k' := Real.sqrt (μ' / μ)
  have hk_pos : 0 ≤ k := Real.sqrt_nonneg _
  have hk'_pos : 0 ≤ k' := Real.sqrt_nonneg _
  have hkk' : k * k' = 1 := by
    simp only [k, k']
    rw [← Real.sqrt_mul (le_of_lt hdiv_pos)]
    rw [div_mul_div_comm, mul_comm μ' μ, div_self (ne_of_gt (mul_pos_of_neg_of_neg hμ hμ'))]
    simp
  have hk'k : k' * k = 1 := by rw [mul_comm]; exact hkk'
  have hksq : k * k = μ / μ' := Real.mul_self_sqrt (le_of_lt hdiv_pos)
  refine ⟨⟨fun z => ⟨z.re, z.im * k⟩, fun z => ⟨z.re, z.im * k'⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro z; ext; rfl; simp only; rw [mul_assoc, hkk', mul_one]
  · intro z; ext; rfl; simp only; rw [mul_assoc, hk'k, mul_one]
  · intro z w
    ext
    · simp only [QuadraticAlgebra.re_mul]
      have hμ'_ne : μ' ≠ 0 := ne_of_lt hμ'
      have h : μ' * (z.im * k) * (w.im * k) = μ * z.im * w.im := by
        have step1 : μ' * (z.im * k) * (w.im * k) = μ' * z.im * w.im * (k * k) := by ring
        have step2 : μ' * z.im * w.im * (k * k) = μ' * z.im * w.im * (μ / μ') := by rw [hksq]
        have step3 : μ' * z.im * w.im * (μ / μ') = μ * z.im * w.im := by field_simp
        linarith [step1, step2, step3]
      linarith [h]
    · simp only [MuAlgebra.mul_im]; ring
  · intro z w; ext <;> simp [add_mul]

/-- Every MuAlgebra with μ > 0 is isomorphic to MuAlgebra 1 (split-complex). -/
noncomputable def muAlgebraPosToOne (μ : ℝ) (hμ : 0 < μ) : MuAlgebra μ ≃+* MuAlgebra 1 :=
  muAlgebraRescale μ 1 hμ one_pos

/-- Every MuAlgebra with μ < 0 is isomorphic to MuAlgebra (-1) (complex). -/
noncomputable def muAlgebraNegToNegOne (μ : ℝ) (hμ : μ < 0) : MuAlgebra μ ≃+* MuAlgebra (-1) :=
  muAlgebraRescaleNeg μ (-1) hμ (neg_one_lt_zero)

/-- Every 2D unital real algebra with e² = μ is isomorphic to one of the three standard forms. -/
theorem mu_algebra_classification (μ : ℝ) :
    (μ < 0 ∧ Nonempty (MuAlgebra μ ≃+* ℂ)) ∨
    (μ = 0) ∨
    (0 < μ ∧ Nonempty (MuAlgebra μ ≃+* SplitComplex)) := by
  rcases lt_trichotomy μ 0 with h_neg | h_zero | h_pos
  · left
    refine ⟨h_neg, ?_⟩
    exact ⟨(muAlgebraNegToNegOne μ h_neg).trans muAlgebraNegOneEquivComplex⟩
  · right; left; exact h_zero
  · right; right
    refine ⟨h_pos, ?_⟩
    exact ⟨(muAlgebraPosToOne μ h_pos).trans muAlgebraOneEquivSplit⟩

/-! ## The Completing-the-Square Parameter

The key algebraic insight: Given e² = a + be, defining e' = e - b/2 gives (e')² = μ·1
where μ = a + b²/4. Rescaling the new generator changes μ; its sign classifies
the resulting real algebra.
-/

/-- The normalized square parameter. Its numerical value is not invariant
under a further rescaling of the generator. -/
noncomputable def completingSquareInvariant (a b : ℝ) : ℝ := a + b^2 / 4

/-- Squaring within the normalized algebra. This coordinate identity does
not perform the change of basis; `completingSquareIso` does so below. -/
theorem completing_square_abstract (a b : ℝ) :
    let μ := completingSquareInvariant a b
    ∀ z : MuAlgebra μ, z * z = ⟨z.re^2 + μ * z.im^2, 2 * z.re * z.im⟩ := by
  intro μ z
  ext
  · simp [QuadraticAlgebra.re_mul]; ring
  · simp; ring

/-! ## Connection to K&S SymmetricalFoundation

K&S parameterize their bilinear product by a real parameter μ:
  (u₁, u₂) * (v₁, v₂) = (u₁v₁ + μ·u₂v₂, u₁v₂ + u₂v₁)

This gives exactly MuAlgebra μ. The classification theorem shows that although μ
varies continuously, there are only 3 isomorphism classes.

For quantum mechanics, K&S argue that μ = -1 (complex numbers) is selected by
additional physical constraints (unitarity, Fourier duality).
-/

/-- K&S bilinearProduct matches MuAlgebra multiplication. -/
theorem ks_bilinearProduct_eq_muAlgebra (μ : ℝ) (z w : MuAlgebra μ) :
    z * w = ⟨z.re * w.re + μ * z.im * w.im, z.re * w.im + z.im * w.re⟩ := by
  ext <;> simp

/-- The three-way classification is complete: every μ falls into exactly one class. -/
theorem classification_trichotomy (μ : ℝ) :
    (μ < 0 ∧ classifyByMu μ = TwoDimAlgebraClass.complex) ∨
    (μ = 0 ∧ classifyByMu μ = TwoDimAlgebraClass.dual) ∨
    (0 < μ ∧ classifyByMu μ = TwoDimAlgebraClass.splitComplex) := by
  rcases lt_trichotomy μ 0 with h | h | h
  · left; exact ⟨h, by simp [classifyByMu, h]⟩
  · right; left; exact ⟨h, by simp [classifyByMu, h]⟩
  · right; right; exact ⟨h, by simp [classifyByMu, not_lt.mpr (le_of_lt h), ne_of_gt h]⟩

/-! ## Connection to K&S Bilinear Product

The K&S bilinearProduct is exactly MuAlgebra multiplication viewed on ℝ × ℝ.
-/

/-- The general bilinear product form (matching K&S definition in SymmetricalFoundation). -/
def bilinearProductDef (μ : ℝ) (u v : ℝ × ℝ) : ℝ × ℝ :=
  (u.1 * v.1 + μ * u.2 * v.2, u.1 * v.2 + u.2 * v.1)

/-- bilinearProductDef is associative for any μ. -/
theorem bilinearProductDef_assoc (μ : ℝ) (u v w : ℝ × ℝ) :
    bilinearProductDef μ (bilinearProductDef μ u v) w =
    bilinearProductDef μ u (bilinearProductDef μ v w) := by
  simp only [bilinearProductDef]
  ext <;> ring

/-- bilinearProductDef has identity (1, 0). -/
theorem bilinearProductDef_one_left (μ : ℝ) (u : ℝ × ℝ) :
    bilinearProductDef μ (1, 0) u = u := by
  simp only [bilinearProductDef]
  ext <;> simp

theorem bilinearProductDef_one_right (μ : ℝ) (u : ℝ × ℝ) :
    bilinearProductDef μ u (1, 0) = u := by
  simp only [bilinearProductDef]
  ext <;> simp

/-- MuAlgebra multiplication matches bilinearProductDef. -/
theorem muAlgebra_eq_bilinearProductDef (μ : ℝ) (z w : MuAlgebra μ) :
    let prod := z * w
    (prod.re, prod.im) = bilinearProductDef μ (z.re, z.im) (w.re, w.im) := by
  simp only [bilinearProductDef, QuadraticAlgebra.re_mul, MuAlgebra.mul_im]

/-- bilinearProductDef is commutative. -/
theorem bilinearProductDef_comm (μ : ℝ) (u v : ℝ × ℝ) :
    bilinearProductDef μ u v = bilinearProductDef μ v u := by
  simp only [bilinearProductDef]
  ext <;> ring

/-- The classification restated: all bilinearProductDef μ algebras are classified by sign of μ. -/
theorem bilinearProductDef_classification (μ : ℝ) :
    (μ < 0 ∧ Nonempty (MuAlgebra μ ≃+* ℂ)) ∨
    (μ = 0) ∨
    (0 < μ ∧ Nonempty (MuAlgebra μ ≃+* SplitComplex)) := by
  rcases lt_trichotomy μ 0 with h | h | h
  · left
    exact ⟨h, ⟨(muAlgebraNegToNegOne μ h).trans muAlgebraNegOneEquivComplex⟩⟩
  · right; left; exact h
  · right; right
    exact ⟨h, ⟨(muAlgebraPosToOne μ h).trans muAlgebraOneEquivSplit⟩⟩

/-! ## Positive-definite conjugate norm

Requiring this particular conjugate norm to be positive definite selects
negative μ within the normalized family. Whether a proposed physical model
requires that norm, and whether it realizes quantum mechanics, are additional
questions not established by the algebraic theorem.

For MuAlgebra(μ), conjugation is conj(u₁, u₂) = (u₁, -u₂), and:
  N(u) = u · conj(u) = (u₁² - μ·u₂², 0)

So the norm² is u₁² - μ·u₂²:
- μ < 0: N(u) = u₁² + |μ|·u₂² ≥ 0 (positive definite) ✓
- μ = 0: N(u) = u₁² (degenerate - ignores imaginary part)
- μ > 0: N(u) = u₁² - μ·u₂² (indefinite - can be negative) ✗
-/

/-- The consumed conjugate API reuses the canonical quadratic involution. -/
def MuAlgebra.conj {μ : ℝ} (z : MuAlgebra μ) : MuAlgebra μ := star z

@[simp] lemma MuAlgebra.conj_re {μ : ℝ} (z : MuAlgebra μ) : z.conj.re = z.re := by
  simp [conj]
@[simp] lemma MuAlgebra.conj_im {μ : ℝ} (z : MuAlgebra μ) : z.conj.im = -z.im := rfl

/-- The consumed conjugate-norm API is Mathlib's quadratic norm. -/
def MuAlgebra.conjNorm {μ : ℝ} (z : MuAlgebra μ) : ℝ := QuadraticAlgebra.norm z

/-- Its coordinate formula in the normalized family. -/
theorem MuAlgebra.conjNorm_def {μ : ℝ} (z : MuAlgebra μ) :
    z.conjNorm = z.re ^ 2 - μ * z.im ^ 2 := by
  simp [conjNorm, QuadraticAlgebra.norm_def, pow_two, mul_assoc]

/-- The product identity is inherited from the standard norm and involution. -/
theorem MuAlgebra.mul_conj_eq_norm {μ : ℝ} (z : MuAlgebra μ) :
    z * z.conj = ⟨z.conjNorm, 0⟩ := by
  change z * star z = algebraMap ℝ (MuAlgebra μ) (QuadraticAlgebra.norm z)
  exact (QuadraticAlgebra.algebraMap_norm_eq_mul_star z).symm

/-- For μ < 0, the conjugate norm is positive definite:
    N(z) ≥ 0, and N(z) = 0 iff z = 0. -/
theorem MuAlgebra.conjNorm_nonneg {μ : ℝ} (hμ : μ < 0) (z : MuAlgebra μ) :
    0 ≤ z.conjNorm := by
  simp only [MuAlgebra.conjNorm_def]
  have h : 0 ≤ -μ * z.im^2 := by nlinarith [sq_nonneg z.im]
  linarith [sq_nonneg z.re]

theorem MuAlgebra.conjNorm_eq_zero_iff {μ : ℝ} (hμ : μ < 0) (z : MuAlgebra μ) :
    z.conjNorm = 0 ↔ z = 0 := by
  constructor
  · intro h
    simp only [MuAlgebra.conjNorm_def] at h
    -- h : z.re^2 - μ * z.im^2 = 0, i.e., z.re^2 = μ * z.im^2
    -- Since μ < 0 and z.im^2 ≥ 0, we have μ * z.im^2 ≤ 0
    -- But z.re^2 ≥ 0, so z.re^2 = μ * z.im^2 implies both are 0
    have hre_sq : z.re^2 = μ * z.im^2 := by linarith
    have him_sq_nonneg : 0 ≤ z.im^2 := sq_nonneg z.im
    have hμ_im_nonpos : μ * z.im^2 ≤ 0 := by nlinarith
    have hre_sq_nonneg : 0 ≤ z.re^2 := sq_nonneg z.re
    have hre_sq_zero : z.re^2 = 0 := by linarith
    have him_sq_zero : z.im^2 = 0 := by
      have : 0 = μ * z.im^2 := by linarith
      nlinarith
    have hre : z.re = 0 := by nlinarith
    have him : z.im = 0 := by nlinarith
    ext <;> assumption
  · intro h
    simp [h, MuAlgebra.conjNorm_def]

/-- For μ > 0 (split-complex), the conjugate norm can be negative. -/
theorem MuAlgebra.conjNorm_can_be_negative {μ : ℝ} (hμ : 0 < μ) :
    ∃ z : MuAlgebra μ, z.conjNorm < 0 := by
  use ⟨0, 1⟩
  simp [MuAlgebra.conjNorm_def]
  linarith

/-- For μ = 0 (dual), the conjugate norm ignores the imaginary part. -/
theorem MuAlgebra.conjNorm_zero_mu (z : MuAlgebra 0) : z.conjNorm = z.re^2 := by
  simp [MuAlgebra.conjNorm_def]

/-- Only negative μ gives a positive-definite conjugate norm in this family.
The algebraic implication does not establish a physical selection principle. -/
theorem selection_theorem :
    ∀ μ : ℝ, (∀ z : MuAlgebra μ, 0 ≤ z.conjNorm ∧ (z.conjNorm = 0 → z = 0)) ↔ μ < 0 := by
  intro μ
  constructor
  · -- If norm is positive-definite, then μ < 0
    intro h
    by_contra hμ_nonneg
    push Not at hμ_nonneg
    rcases lt_or_eq_of_le hμ_nonneg with hμ_pos | hμ_zero
    · -- Case μ > 0: contradicts positive-definiteness
      obtain ⟨z, hz⟩ := MuAlgebra.conjNorm_can_be_negative hμ_pos
      have ⟨hnonneg, _⟩ := h z
      linarith
    · -- Case μ = 0: z = (0, 1) has norm 0 but z ≠ 0
      subst hμ_zero
      have ⟨_, hinj⟩ := h ⟨0, 1⟩
      have heq : MuAlgebra.conjNorm (⟨0, 1⟩ : MuAlgebra 0) = 0 := by
        simp [MuAlgebra.conjNorm_def]
      have hz : (⟨0, 1⟩ : MuAlgebra 0) = 0 := hinj heq
      have : (1 : ℝ) = 0 := congrArg QuadraticAlgebra.im hz
      linarith
  · -- If μ < 0, then norm is positive-definite
    intro hμ z
    exact ⟨MuAlgebra.conjNorm_nonneg hμ z, fun h => (MuAlgebra.conjNorm_eq_zero_iff hμ z).mp h⟩

/-- Multiplicativity is the standard quadratic norm's multiplication law. -/
theorem MuAlgebra.conjNorm_mul {μ : ℝ} (z w : MuAlgebra μ) :
    (z * w).conjNorm = z.conjNorm * w.conjNorm :=
  (QuadraticAlgebra.norm : MuAlgebra μ →* ℝ).map_mul z w

/-! ## General Bilinear Algebra and Classification

The general 2D bilinear algebra has multiplication:
  (u₁, u₂) * (v₁, v₂) = (u₁v₁ + a·u₂v₂, u₁v₂ + u₂v₁ + b·u₂v₂)

Both domain names reuse Mathlib's canonical `QuadraticAlgebra`, including
its ring and scalar structures. The coordinate shift below is retained and
upgraded to an equivalence of real algebras.
-/

/-- The general coordinate family reuses the standard quadratic algebra;
its defining relation is `ω² = a + bω`. -/
abbrev GeneralBilinearAlgebra (a b : ℝ) := QuadraticAlgebra ℝ a b

/-- The completing-the-square isomorphism:
    GeneralBilinearAlgebra(a, b) ≃+* MuAlgebra(a + b²/4)

    The map is (x, y) ↦ (x + b·y/2, y), which corresponds to the
    change of basis e' = e - b/2 where (e')² = (a + b²/4)·1. -/
noncomputable def completingSquareIso (a b : ℝ) :
    GeneralBilinearAlgebra a b ≃+* MuAlgebra (a + b^2/4) where
  toFun z := ⟨z.re + b * z.im / 2, z.im⟩
  invFun z := ⟨z.re - b * z.im / 2, z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' z w := by
    ext
    · -- First component: need to show transformed product matches
      simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
      ring
    · -- Second component: direct calculation
      simp only [QuadraticAlgebra.im_mul]
      ring
  map_add' z w := by
    ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
      ring
    · simp only [QuadraticAlgebra.im_add]

/-- The existing coordinate shift also preserves the declared real scalars. -/
noncomputable def completingSquareAlgEquiv (a b : ℝ) :
    GeneralBilinearAlgebra a b ≃ₐ[ℝ] MuAlgebra (a + b ^ 2 / 4) where
  __ := completingSquareIso a b
  commutes' r := by
    ext <;> simp [completingSquareIso, QuadraticAlgebra.algebraMap_eq]

@[simp] theorem completingSquareAlgEquiv_re (a b : ℝ) (z : QuadraticAlgebra ℝ a b) :
    (completingSquareAlgEquiv a b z).re = z.re + b * z.im / 2 := rfl

@[simp] theorem completingSquareAlgEquiv_im (a b : ℝ) (z : QuadraticAlgebra ℝ a b) :
    (completingSquareAlgEquiv a b z).im = z.im := rfl

/-- The shifted old generator becomes the normalized generator, rather than
merely satisfying a squaring identity in an already normalized algebra. -/
theorem completingSquareAlgEquiv_shift (a b : ℝ) :
    completingSquareAlgEquiv a b
        (QuadraticAlgebra.omega - algebraMap ℝ (QuadraticAlgebra ℝ a b) (b / 2)) =
      MuAlgebra.e (a + b ^ 2 / 4) := by
  ext <;> simp [MuAlgebra.e]

/-- The authored two-parameter coordinate algebra admits a normalized form.
The arbitrary finite-dimensional algebra presentation is handled separately. -/
theorem classification_to_muAlgebra (a b : ℝ) :
    Nonempty (GeneralBilinearAlgebra a b ≃+* MuAlgebra (a + b^2/4)) :=
  ⟨completingSquareIso a b⟩

/-- Equality of normalized parameters suffices for isomorphism. It is not
necessary: rescaling permits distinct parameters with the same sign. -/
theorem classification_invariant (a₁ b₁ a₂ b₂ : ℝ)
    (h : a₁ + b₁^2/4 = a₂ + b₂^2/4) :
    Nonempty (GeneralBilinearAlgebra a₁ b₁ ≃+* GeneralBilinearAlgebra a₂ b₂) := by
  have h1 := completingSquareIso a₁ b₁
  have h2 := completingSquareIso a₂ b₂
  rw [h] at h1
  exact ⟨h1.trans h2.symm⟩

/-! ## Real algebra equivalences and distinct standard forms -/

/-- The existing complex comparison preserves the real algebra structure. -/
noncomputable def muAlgebraNegOneAlgEquivComplex : MuAlgebra (-1) ≃ₐ[ℝ] ℂ where
  __ := muAlgebraNegOneEquivComplex
  commutes' r := by
    apply Complex.ext <;> simp [muAlgebraNegOneEquivComplex]

/-- The existing split-complex comparison preserves real scalars. -/
noncomputable def muAlgebraOneAlgEquivSplit : MuAlgebra 1 ≃ₐ[ℝ] SplitComplex where
  __ := muAlgebraOneEquivSplit
  commutes' r := by ext <;> simp [muAlgebraOneEquivSplit]

/-- The missing standard form uses Mathlib's dual numbers, with their
nonzero square-zero generator, rather than only a zero parameter label. -/
noncomputable def muAlgebraZeroAlgEquivDual : MuAlgebra 0 ≃ₐ[ℝ] DualNumber ℝ where
  toFun z := (z.re, z.im)
  invFun z := ⟨z.fst, z.snd⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl
  map_mul' z w := by
    apply TrivSqZeroExt.ext
    · change z.re * w.re + 0 * z.im * w.im = z.re * w.re
      ring
    · change z.re * w.im + z.im * w.re + 0 * z.im * w.im =
        z.re * w.im + z.im * w.re
      ring
  map_add' z w := by apply TrivSqZeroExt.ext <;> rfl
  commutes' r := by rw [QuadraticAlgebra.algebraMap_eq]; rfl

/-- Positive-parameter rescaling is an equivalence of real algebras. -/
noncomputable def muAlgebraRescaleAlg (μ μ' : ℝ) (hμ : 0 < μ) (hμ' : 0 < μ') :
    MuAlgebra μ ≃ₐ[ℝ] MuAlgebra μ' where
  __ := muAlgebraRescale μ μ' hμ hμ'
  commutes' r := by ext <;> simp [muAlgebraRescale]

/-- Negative-parameter rescaling also preserves all real scalars. -/
noncomputable def muAlgebraRescaleNegAlg (μ μ' : ℝ) (hμ : μ < 0) (hμ' : μ' < 0) :
    MuAlgebra μ ≃ₐ[ℝ] MuAlgebra μ' where
  __ := muAlgebraRescaleNeg μ μ' hμ hμ'
  commutes' r := by ext <;> simp [muAlgebraRescaleNeg]

/-- All three branches now carry an actual equivalence of real algebras. -/
theorem mu_algebra_real_classification (μ : ℝ) :
    (μ < 0 ∧ Nonempty (MuAlgebra μ ≃ₐ[ℝ] ℂ)) ∨
      (μ = 0 ∧ Nonempty (MuAlgebra μ ≃ₐ[ℝ] DualNumber ℝ)) ∨
      (0 < μ ∧ Nonempty (MuAlgebra μ ≃ₐ[ℝ] SplitComplex)) := by
  rcases lt_trichotomy μ 0 with negative | zero | positive
  · exact Or.inl ⟨negative, ⟨(muAlgebraRescaleNegAlg μ (-1) negative
      neg_one_lt_zero).trans muAlgebraNegOneAlgEquivComplex⟩⟩
  · subst μ
    exact Or.inr (Or.inl ⟨rfl, ⟨muAlgebraZeroAlgEquivDual⟩⟩)
  · exact Or.inr (Or.inr ⟨positive, ⟨(muAlgebraRescaleAlg μ 1 positive
      one_pos).trans muAlgebraOneAlgEquivSplit⟩⟩)

/-- Split-complex numbers have no nonzero square-zero element, although
they do have nonzero zero divisors. -/
theorem split_square_eq_zero_iff (z : SplitComplex) : z * z = 0 ↔ z = 0 := by
  constructor
  · intro square
    have realPart := congrArg SplitComplex.re square
    simp only [SplitComplex.mul_re, SplitComplex.zero_re] at realPart
    have realZero : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    have imaginaryZero : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    ext <;> assumption
  · rintro rfl
    exact zero_mul _

theorem dual_eps_ne_zero : (DualNumber.eps : DualNumber ℝ) ≠ 0 := by
  intro equal
  have := congrArg TrivSqZeroExt.snd equal
  simp at this

/-- Complex numbers cannot supply the dual numbers' nonzero nilpotent. -/
theorem complex_not_equiv_dual : ¬ Nonempty (ℂ ≃ₐ[ℝ] DualNumber ℝ) := by
  rintro ⟨equiv⟩
  have square : equiv.symm DualNumber.eps * equiv.symm DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have vanishes : equiv.symm DualNumber.eps = 0 := mul_self_eq_zero.mp square
  apply dual_eps_ne_zero
  apply equiv.symm.injective
  simpa using vanishes

/-- A nonzero nilpotent also separates dual from split-complex numbers. -/
theorem dual_not_equiv_split : ¬ Nonempty (DualNumber ℝ ≃ₐ[ℝ] SplitComplex) := by
  rintro ⟨equiv⟩
  have square : equiv DualNumber.eps * equiv DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have vanishes := (split_square_eq_zero_iff _).mp square
  apply dual_eps_ne_zero
  apply equiv.injective
  simpa using vanishes

/-- Nonzero zero divisors separate split-complex from complex numbers. -/
theorem split_not_equiv_complex : ¬ Nonempty (SplitComplex ≃ₐ[ℝ] ℂ) := by
  rintro ⟨equiv⟩
  obtain ⟨first, second, firstNonzero, secondNonzero, product⟩ :=
    SplitComplex.has_zero_divisors
  have mapped : equiv first * equiv second = 0 := by rw [← map_mul, product, map_zero]
  rcases mul_eq_zero.mp mapped with firstZero | secondZero
  · exact firstNonzero (equiv.injective (by simpa using firstZero))
  · exact secondNonzero (equiv.injective (by simpa using secondZero))

/-- A uniform carrier for the three standard real algebras. -/
def standardForm : TwoDimAlgebraClass → Type
  | .complex => ℂ
  | .dual => DualNumber ℝ
  | .splitComplex => SplitComplex

noncomputable instance standardFormCommRing (kind : TwoDimAlgebraClass) :
    CommRing (standardForm kind) := by
  cases kind <;> dsimp [standardForm] <;> infer_instance

noncomputable instance standardFormAlgebra (kind : TwoDimAlgebraClass) :
    Algebra ℝ (standardForm kind) := by
  cases kind <;> dsimp [standardForm] <;> infer_instance

/-- An isomorphism cannot identify distinct entries of the classification. -/
theorem standardForm_class_eq {first second : TwoDimAlgebraClass}
    (equivalent : Nonempty (standardForm first ≃ₐ[ℝ] standardForm second)) :
    first = second := by
  cases first <;> cases second
  · rfl
  · exact (complex_not_equiv_dual equivalent).elim
  · exact (split_not_equiv_complex (equivalent.map AlgEquiv.symm)).elim
  · exact (complex_not_equiv_dual (equivalent.map AlgEquiv.symm)).elim
  · rfl
  · exact (dual_not_equiv_split equivalent).elim
  · exact (split_not_equiv_complex equivalent).elim
  · exact (dual_not_equiv_split (equivalent.map AlgEquiv.symm)).elim
  · rfl

/-- Every normalized parameter has its sign-selected standard real algebra. -/
noncomputable def muAlgebraAlgEquivStandard (μ : ℝ) :
    MuAlgebra μ ≃ₐ[ℝ] standardForm (classifyByMu μ) :=
  if negative : μ < 0 then by
    have kind : TwoDimAlgebraClass.complex = classifyByMu μ := by
      simp [classifyByMu, negative]
    exact ((muAlgebraRescaleNegAlg μ (-1) negative neg_one_lt_zero).trans
      muAlgebraNegOneAlgEquivComplex).trans
        (AlgEquiv.cast (R := ℝ) (A := standardForm) kind)
  else if zero : μ = 0 then by
    subst μ
    have kind : TwoDimAlgebraClass.dual = classifyByMu 0 := by simp [classifyByMu]
    exact muAlgebraZeroAlgEquivDual.trans
      (AlgEquiv.cast (R := ℝ) (A := standardForm) kind)
  else by
    have positive : 0 < μ := lt_of_le_of_ne (le_of_not_gt negative) (Ne.symm zero)
    have kind : TwoDimAlgebraClass.splitComplex = classifyByMu μ := by
      simp [classifyByMu, negative, zero]
    exact ((muAlgebraRescaleAlg μ 1 positive one_pos).trans
      muAlgebraOneAlgEquivSplit).trans
        (AlgEquiv.cast (R := ℝ) (A := standardForm) kind)

/-- The same classification applies to the actual polynomial quotient, via
its independently proved quadratic-coordinate equivalence. -/
noncomputable def adjoinRootAlgEquivStandard (a b : ℝ) :
    AdjoinRoot (QuadraticPolynomialPresentation.definingPolynomial a b) ≃ₐ[ℝ]
      standardForm (classifyByMu (a + b ^ 2 / 4)) :=
  (QuadraticPolynomialPresentation.equivAdjoinRoot a b).symm.trans
    ((completingSquareAlgEquiv a b).trans (muAlgebraAlgEquivStandard (a + b ^ 2 / 4)))

/-- The sign class is the complete invariant for normalized parameters. -/
theorem mu_algebra_equiv_iff (μ μ' : ℝ) :
    Nonempty (MuAlgebra μ ≃ₐ[ℝ] MuAlgebra μ') ↔ classifyByMu μ = classifyByMu μ' := by
  constructor
  · rintro ⟨equiv⟩
    exact standardForm_class_eq ⟨(muAlgebraAlgEquivStandard μ).symm.trans
      (equiv.trans (muAlgebraAlgEquivStandard μ'))⟩
  · intro equal
    exact ⟨(muAlgebraAlgEquivStandard μ).trans
      ((AlgEquiv.cast equal).trans (muAlgebraAlgEquivStandard μ').symm)⟩

/-- Negative control for numerical invariance: two different positive
parameters present isomorphic real algebras. -/
theorem parameter_value_not_invariant :
    (2 : ℝ) ≠ 1 ∧ Nonempty (MuAlgebra 2 ≃ₐ[ℝ] MuAlgebra 1) := by
  exact ⟨by norm_num, ⟨muAlgebraRescaleAlg 2 1 (by norm_num) one_pos⟩⟩

/-- Every unital associative real algebra of dimension two has exactly one
of the three standard forms. Commutativity is a consequence, not a premise. -/
theorem two_dimensional_classification (A : Type*) [Ring A] [Algebra ℝ A]
    (dimension : Module.finrank ℝ A = 2) :
    ∃! kind : TwoDimAlgebraClass, Nonempty (A ≃ₐ[ℝ] standardForm kind) := by
  obtain ⟨a, b, ⟨presentation⟩⟩ :=
    QuadraticPresentation.exists_equiv_quadratic ℝ A dimension
  let μ := a + b ^ 2 / 4
  let normalized : A ≃ₐ[ℝ] MuAlgebra μ := presentation.trans (completingSquareAlgEquiv a b)
  let comparison : A ≃ₐ[ℝ] standardForm (classifyByMu μ) :=
    normalized.trans (muAlgebraAlgEquivStandard μ)
  refine ⟨classifyByMu μ, ⟨comparison⟩, ?_⟩
  intro other ⟨equiv⟩
  exact standardForm_class_eq ⟨equiv.symm.trans comparison⟩

end Mettapedia.Algebra.TwoDimClassification
