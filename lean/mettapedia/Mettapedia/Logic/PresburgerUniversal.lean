import Mathlib.ModelTheory.Arithmetic.Presburger.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# An executable standard-natural arithmetic fragment

The input terms are Mathlib's actual Presburger terms: variables, zero, one,
and addition.  A claim universally compares two such terms over the usual
natural numbers.  Normalization extracts a constant and the multiplicity of
each variable.  The comparison is valid for every natural valuation exactly
when the constant and every coefficient are componentwise ordered.

This decides universally quantified, hypothesis-free affine inequalities.
It is not a decision procedure for arbitrary Boolean combinations or
quantifier alternation in Presburger arithmetic.
-/

namespace Mettapedia.Logic.PresburgerUniversal

open FirstOrder
open scoped BigOperators

/-- A constant and nonnegative coefficients on a finite variable list. -/
structure Affine (nVars : Nat) where
  constant : Nat
  coefficient : Fin nVars → Nat

def Affine.eval {nVars : Nat} (form : Affine nVars)
    (valuation : Fin nVars → Nat) : Nat :=
  form.constant + ∑ index, form.coefficient index * valuation index

def Affine.add {nVars : Nat} (left right : Affine nVars) :
    Affine nVars where
  constant := left.constant + right.constant
  coefficient index := left.coefficient index + right.coefficient index

theorem Affine.eval_add {nVars : Nat} (left right : Affine nVars)
    (valuation : Fin nVars → Nat) :
    (left.add right).eval valuation = left.eval valuation + right.eval valuation := by
  simp only [Affine.add, Affine.eval, Nat.add_mul, Finset.sum_add_distrib]
  omega

/-- Structural normalization of the existing Presburger term syntax. -/
def normalize {nVars : Nat} : Language.presburger.Term (Fin nVars) →
    Affine nVars
  | .var index => ⟨0, fun other => if other = index then 1 else 0⟩
  | .func .zero _ => ⟨0, fun _ => 0⟩
  | .func .one _ => ⟨1, fun _ => 0⟩
  | .func .add terms => (normalize (terms 0)).add (normalize (terms 1))

/-- The computed affine form denotes the original term in the standard
natural-number structure. -/
theorem normalize_correct {nVars : Nat}
    (term : Language.presburger.Term (Fin nVars))
    (valuation : Fin nVars → Nat) :
    (normalize term).eval valuation = term.realize valuation := by
  induction term with
  | var index => simp [normalize, Affine.eval, Language.Term.realize]
  | @func arity operation terms inductionHypothesis =>
      cases operation with
      | zero => simp [normalize, Affine.eval, Language.Term.realize]
      | one => simp [normalize, Affine.eval, Language.Term.realize]
      | add =>
          rw [normalize, Affine.eval_add, inductionHypothesis 0, inductionHypothesis 1]
          rfl

/-- A finite, executable test on the normalized coefficients. -/
def Affine.checkLe {nVars : Nat} (left right : Affine nVars) : Bool :=
  decide (left.constant ≤ right.constant ∧
    ∀ index, left.coefficient index ≤ right.coefficient index)

theorem Affine.eval_zero {nVars : Nat} (form : Affine nVars) :
    form.eval (fun _ => 0) = form.constant := by
  simp [Affine.eval]

theorem Affine.eval_single {nVars : Nat} (form : Affine nVars)
    (index : Fin nVars) (value : Nat) :
    form.eval (fun other => if other = index then value else 0) =
      form.constant + form.coefficient index * value := by
  simp [Affine.eval, mul_ite]

/-- Exactness is over all natural valuations, not just a tested finite range.
A deficient coefficient is exposed by a single-coordinate valuation larger
than the right-hand constant. -/
theorem Affine.checkLe_eq_true_iff {nVars : Nat}
    (left right : Affine nVars) :
    left.checkLe right = true ↔
      ∀ valuation, left.eval valuation ≤ right.eval valuation := by
  simp only [Affine.checkLe, decide_eq_true_eq]
  constructor
  · rintro ⟨constants, coefficients⟩ valuation
    exact Nat.add_le_add constants
      (Finset.sum_le_sum fun index _ =>
        Nat.mul_le_mul_right (valuation index) (coefficients index))
  · intro universally
    refine ⟨?_, ?_⟩
    · simpa only [Affine.eval_zero] using universally (fun _ => 0)
    · intro index
      have witness := universally
        (fun other => if other = index then right.constant + 1 else 0)
      simp only [Affine.eval_single] at witness
      by_contra notLe
      have larger : right.coefficient index + 1 ≤ left.coefficient index := by omega
      have multiplied := Nat.mul_le_mul_right (right.constant + 1) larger
      nlinarith

/-- An explicit arithmetic claim, using existing first-order syntax. -/
structure Claim (nVars : Nat) where
  left : Language.presburger.Term (Fin nVars)
  right : Language.presburger.Term (Fin nVars)

/-- Truth means comparison at every valuation in the ordinary natural numbers. -/
def Claim.Meaning {nVars : Nat} (claim : Claim nVars) : Prop :=
  ∀ valuation : Fin nVars → Nat,
    claim.left.realize valuation ≤ claim.right.realize valuation

def Claim.check {nVars : Nat} (claim : Claim nVars) : Bool :=
  (normalize claim.left).checkLe (normalize claim.right)

theorem Claim.check_eq_true_iff {nVars : Nat} (claim : Claim nVars) :
    claim.check = true ↔ claim.Meaning := by
  simp only [Claim.check, Claim.Meaning, Affine.checkLe_eq_true_iff, normalize_correct]

/-- Refusal of this complete fragment checker yields an actual natural-number
countervaluation.  This is stronger than exhaustion of an incomplete search. -/
theorem Claim.refused_iff_counterexample {nVars : Nat} (claim : Claim nVars) :
    claim.check = false ↔
      ∃ valuation : Fin nVars → Nat,
        claim.right.realize valuation < claim.left.realize valuation := by
  classical
  rw [← Bool.not_eq_true, claim.check_eq_true_iff]
  simp only [Claim.Meaning, not_forall, Nat.not_le]

end Mettapedia.Logic.PresburgerUniversal
