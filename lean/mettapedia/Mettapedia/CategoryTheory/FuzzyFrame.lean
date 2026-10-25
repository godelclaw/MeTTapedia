import Mathlib.Order.Heyting.Basic
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Algebra.Order.Interval.Set.Instances
import Mathlib.Algebra.Order.Quantale
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Linarith
import KnuthSkilling.Literature.Residuated

/-!
# Frame and product-quantale semantics on the unit interval

A single inherited closed-interval order supplies minimum, maximum, and arbitrary
infima and suprema. The authored binary formulas retain their concrete meanings.
Minimum has Gödel implication as right adjoint; multiplication has the distinct
product implication. Product is bounded by minimum, but fails its idempotence
away from the endpoints. Its adjunction supplies arbitrary-join preservation
and Mathlib's quantale structure, without identifying these two connectives.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.FuzzyFrame

open Set Classical

/-- The unit interval [0,1] as a subtype of ℝ -/
def UnitInterval : Type := {x : ℝ // 0 ≤ x ∧ x ≤ 1}

notation "𝕀" => UnitInterval

namespace UnitInterval

/-- Extensionality for unit interval -/
@[ext]
theorem ext {a b : 𝕀} (h : a.val = b.val) : a = b := Subtype.ext h

/-- One inherited order supplies all lattice operations and their laws. -/
noncomputable instance : CompleteLinearOrder 𝕀 :=
  inferInstanceAs (CompleteLinearOrder (Set.Icc (0 : ℝ) 1))

noncomputable instance : CommMonoid 𝕀 :=
  inferInstanceAs (CommMonoid (Set.Icc (0 : ℝ) 1))

instance : Zero 𝕀 := inferInstanceAs (Zero (Set.Icc (0 : ℝ) 1))

/-- Zero in the unit interval -/
def zero : 𝕀 := ⟨0, by norm_num, by norm_num⟩

/-- One in the unit interval -/
def one : 𝕀 := ⟨1, by norm_num, by norm_num⟩

@[simp] theorem zero_val : (0 : 𝕀).val = 0 := rfl
@[simp] theorem one_val : (1 : 𝕀).val = 1 := rfl
@[simp] theorem inf_val (a b : 𝕀) : (a ⊓ b).val = min a.val b.val := rfl

/-- Meet: minimum of two values -/
def inf (a b : 𝕀) : 𝕀 :=
  ⟨min a.val b.val, by
    constructor
    · exact le_min a.prop.1 b.prop.1
    · exact min_le_iff.mpr (Or.inl a.prop.2)⟩

/-- Join: maximum of two values -/
def sup (a b : 𝕀) : 𝕀 :=
  ⟨max a.val b.val, by
    constructor
    · exact le_max_iff.mpr (Or.inl a.prop.1)
    · exact max_le a.prop.2 b.prop.2⟩

/-- Product t-norm: a ⊗ b = a * b -/
def product (a b : 𝕀) : 𝕀 :=
  ⟨a.val * b.val, by
    constructor
    · exact mul_nonneg a.prop.1 b.prop.1
    · calc a.val * b.val
        _ ≤ 1 * 1 := mul_le_mul a.prop.2 b.prop.2 b.prop.1 (by norm_num)
        _ = 1 := by norm_num⟩

@[simp] theorem product_val (a b : 𝕀) : (a * b).val = a.val * b.val := rfl

/-- Product is commutative -/
theorem product_comm (a b : 𝕀) : a * b = b * a := by
  ext
  exact mul_comm a.val b.val

/-- Product is associative -/
theorem product_assoc (a b c : 𝕀) : a * b * c = a * (b * c) := by
  ext
  exact mul_assoc a.val b.val c.val

/-- One is the unit for product -/
theorem product_one (a : 𝕀) : a * 1 = a := by
  ext
  exact mul_one a.val

/-- One is the left unit for product. -/
theorem one_product (a : 𝕀) : (1 : 𝕀) * a = a := by
  ext
  exact one_mul a.val

/-- Gödel implication (residuation for min) -/
noncomputable def himp (a b : 𝕀) : 𝕀 :=
  if a.val ≤ b.val then
    one
  else
    b

/-- Product implication (residuation for product t-norm) -/
noncomputable def productImp (a b : 𝕀) : 𝕀 :=
  if a.val = 0 then
    one
  else
    ⟨min 1 (b.val / a.val), by
      constructor
      · exact le_min (by norm_num) (div_nonneg b.prop.1 a.prop.1)
      · exact min_le_left 1 _⟩

@[simp] theorem productImp_val_of_eq (a b : 𝕀) (ha : a.val = 0) :
    (productImp a b).val = 1 := by
  simp [productImp, ha, one]

@[simp] theorem productImp_val_of_ne (a b : 𝕀) (ha : a.val ≠ 0) :
    (productImp a b).val = min 1 (b.val / a.val) := by
  simp [productImp, ha]

theorem product_residuation (a b c : 𝕀) :
    a * b ≤ c ↔ b ≤ productImp a c := by
  by_cases ha : a.val = 0
  · constructor
    · intro _
      change b.val ≤ (productImp a c).val
      rw [productImp_val_of_eq _ _ ha]
      exact b.prop.2
    · intro _
      change a.val * b.val ≤ c.val
      simpa [ha] using c.prop.1
  · have ha0 : 0 < a.val := lt_of_le_of_ne a.prop.1 (Ne.symm ha)
    constructor
    · intro hab
      change b.val ≤ (productImp a c).val
      rw [productImp_val_of_ne _ _ ha]
      refine le_min b.prop.2 ?_
      have hab' : a.val * b.val ≤ c.val := hab
      exact (le_div_iff₀ ha0).2 (by rw [mul_comm]; exact hab')
    · intro hbc
      change a.val * b.val ≤ c.val
      have hbc' : b.val ≤ c.val / a.val := by
        have hmin : b.val ≤ min 1 (c.val / a.val) := by
          have hbval : b.val ≤ (productImp a c).val := hbc
          simpa [productImp, ha] using hbval
        exact (le_min_iff.mp hmin).2
      have hmul : b.val * a.val ≤ c.val := (le_div_iff₀ ha0).1 hbc'
      simpa [mul_comm] using hmul

/-- Product implication is right adjoint to product t-norm. -/
theorem productImp_adjoint (a b c : 𝕀) :
    a * b ≤ c ↔ b ≤ productImp a c :=
  product_residuation a b c

/-- Product t-norm is bounded by meet on `[0,1]`. -/
theorem product_le_inf (a b : 𝕀) : a * b ≤ a ⊓ b := by
  refine le_inf ?_ ?_
  · change a.val * b.val ≤ a.val
    exact mul_le_of_le_one_right a.prop.1 b.prop.2
  · change a.val * b.val ≤ b.val
    simpa [mul_comm] using (mul_le_of_le_one_right b.prop.1 a.prop.2)

noncomputable instance : KnuthSkilling.Literature.ResiduatedMonoid 𝕀 where
  res := productImp
  adj := product_residuation

/-- Exchange law for product residuation:
`(a * b) ⇒ c = a ⇒ (b ⇒ c)`. -/
theorem productImp_exchange (a b c : 𝕀) :
    productImp (a * b) c = productImp a (productImp b c) :=
  KnuthSkilling.Literature.ResiduatedMonoidLemmas.exchange (α := 𝕀) a b c

/-- The authored constants and binary formulas agree with the inherited operations. -/
@[simp] theorem zero_eq : zero = 0 := rfl
@[simp] theorem one_eq : one = 1 := rfl
@[simp] theorem inf_eq (a b : 𝕀) : inf a b = a ⊓ b := rfl
@[simp] theorem sup_eq (a b : 𝕀) : sup a b = a ⊔ b := rfl
@[simp] theorem product_eq (a b : 𝕀) : product a b = a * b := rfl

/-- Gödel implication belongs to the minimum connective. -/
theorem himp_eq_canonical (a b : 𝕀) : himp a b = (a ⇨ b) := rfl

theorem himp_residuation (a b c : 𝕀) : a ⊓ b ≤ c ↔ b ≤ himp a c := by
  rw [himp_eq_canonical]
  exact le_himp_iff'.symm

/-- Product multiplication is a left adjoint and therefore preserves arbitrary joins. -/
theorem product_galoisConnection (a : 𝕀) : GaloisConnection (a * ·) (productImp a) :=
  fun b c => product_residuation a b c

noncomputable instance : IsQuantale 𝕀 where
  mul_sSup_distrib a S := (product_galoisConnection a).l_sSup
  sSup_mul_distrib S a := by simpa only [mul_comm] using (product_galoisConnection a).l_sSup (s := S)

/-- The concrete quotient formula is the product quantale's order-theoretic residual. -/
theorem productImp_eq_rightMulResiduation (a b : 𝕀) : productImp a b = Quantale.rightMulResiduation a b := by
  apply le_antisymm
  · exact Quantale.rightMulResiduation_le_iff_mul_le.mpr ((product_residuation a _ b).mpr le_rfl)
  · exact (product_residuation a _ b).mp (Quantale.rightMulResiduation_le_iff_mul_le.mp le_rfl)

theorem himp_le_productImp (a b : 𝕀) : himp a b ≤ productImp a b := by
  apply (product_residuation a _ b).mp
  exact (product_le_inf _ _).trans ((himp_residuation a _ b).mpr le_rfl)

/-- Product has only the endpoint idempotents; minimum is idempotent everywhere. -/
theorem product_idempotent_iff (a : 𝕀) : a * a = a ↔ a = 0 ∨ a = 1 := by
  constructor
  · intro h
    have value := congrArg Subtype.val h
    change a.val * a.val = a.val at value
    have factor : a.val * (a.val - 1) = 0 := by nlinarith [value]
    rcases mul_eq_zero.mp factor with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext (sub_eq_zero.mp h)
  · rintro (rfl | rfl) <;> apply Subtype.ext <;> norm_num

/-- The same carrier supports different implication and multiplication observations. -/
theorem connective_separation :
    let half : 𝕀 := ⟨1 / 2, by norm_num, by norm_num⟩
    let quarter : 𝕀 := ⟨1 / 4, by norm_num, by norm_num⟩
    (himp half quarter).val = 1 / 4 ∧ (productImp half quarter).val = 1 / 2 ∧
      half * half ≠ half ⊓ half := by
  let half : 𝕀 := ⟨1 / 2, by norm_num, by norm_num⟩
  let quarter : 𝕀 := ⟨1 / 4, by norm_num, by norm_num⟩
  change (himp half quarter).val = 1 / 4 ∧ (productImp half quarter).val = 1 / 2 ∧
    half * half ≠ half ⊓ half
  refine ⟨?_, ?_, ?_⟩
  · rw [himp, if_neg (by norm_num [half, quarter] : ¬ half.val ≤ quarter.val)]
  · rw [productImp_val_of_ne _ _ (by norm_num [half])]
    norm_num [half, quarter]
  · intro h
    have values := congrArg Subtype.val h
    change (1 / 2 : ℝ) * (1 / 2) = min (1 / 2) (1 / 2) at values
    norm_num at values

end UnitInterval

end Mettapedia.CategoryTheory.FuzzyFrame
