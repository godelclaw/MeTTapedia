import Mathlib.Tactic

/-!
# Exact masked scalar inverses and conservative proposal constraints

These are field laws, not identities for rounded binary64 arithmetic. They
identify the consistency condition omitted by a proposal-only zero-product
relaxation. The numerical learner replays every proposed program through its
original observation checker, including its precision and mask; it does not
use field algebra to prune floating-point preimages.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.MaskedScalarInverse

inductive Constraint (K : Type) where
  | free
  | equal (value : K)
  | impossible
  deriving DecidableEq, Repr

def Holds {K : Type} : Constraint K → K → Prop
  | .free, _ => True
  | .equal expected, actual => actual = expected
  | .impossible, _ => False

variable {K : Type} [Field K] [DecidableEq K]

def add (observed : Bool) (known target : K) : Constraint K :=
  if observed then .equal (target - known) else .free

def subtractLeft (observed : Bool) (known target : K) : Constraint K :=
  if observed then .equal (target + known) else .free

def subtractRight (observed : Bool) (known target : K) : Constraint K :=
  if observed then .equal (known - target) else .free

def multiply (observed : Bool) (known target : K) : Constraint K :=
  if observed then
    if known = 0 then if target = 0 then .free else .impossible
    else .equal (target / known)
  else .free

def multiplyProposal (observed : Bool) (known target : K) : Constraint K :=
  if observed && decide (known ≠ 0) then .equal (target / known) else .free

omit [DecidableEq K] in
theorem add_iff (observed : Bool) (known target actual : K) :
    Holds (add observed known target) actual ↔ (observed = true → known + actual = target) := by
  cases observed with
  | false => simp [add, Holds]
  | true =>
      simpa [add, Holds] using
        (show actual = target - known ↔ known + actual = target from by
          constructor <;> intro equal <;> linear_combination equal)

omit [DecidableEq K] in
theorem subtractLeft_iff (observed : Bool) (known target actual : K) :
    Holds (subtractLeft observed known target) actual ↔ (observed = true → actual - known = target) := by
  cases observed with
  | false => simp [subtractLeft, Holds]
  | true =>
      simpa [subtractLeft, Holds] using
        (show actual = target + known ↔ actual - known = target from by
          constructor <;> intro equal <;> linear_combination equal)

omit [DecidableEq K] in
theorem subtractRight_iff (observed : Bool) (known target actual : K) :
    Holds (subtractRight observed known target) actual ↔ (observed = true → known - actual = target) := by
  cases observed with
  | false => simp [subtractRight, Holds]
  | true =>
      simpa [subtractRight, Holds] using
        (show actual = known - target ↔ known - actual = target from by
          constructor <;> intro equal <;> linear_combination -equal)

theorem multiply_iff (observed : Bool) (known target actual : K) :
    Holds (multiply observed known target) actual ↔ (observed = true → known * actual = target) := by
  cases observed with
  | false => simp [multiply, Holds]
  | true =>
      by_cases zero : known = 0
      · by_cases consistent : target = 0 <;> simp [multiply, zero, consistent, Holds, eq_comm]
      · simpa [multiply, zero, Holds, mul_comm] using (eq_div_iff zero : actual = target / known ↔ actual * known = target)

theorem proposal_is_relaxation (observed : Bool) (known target actual : K)
    (exact : Holds (multiply observed known target) actual) :
    Holds (multiplyProposal observed known target) actual := by
  cases observed with
  | false => simp [multiplyProposal, Holds]
  | true =>
      by_cases zero : known = 0
      · simp [multiplyProposal, zero, Holds]
      · simpa [multiplyProposal, zero, multiply, Holds] using exact

theorem checked_proposal_iff (observed : Bool) (known target actual : K) :
    Holds (multiplyProposal observed known target) actual ∧
      (observed = true → known = 0 → target = 0) ↔
        (observed = true → known * actual = target) := by
  cases observed with
  | false => simp [multiplyProposal, Holds]
  | true =>
      by_cases zero : known = 0
      · simp [multiplyProposal, zero, Holds, eq_comm]
      · simpa [multiplyProposal, zero, Holds, mul_comm] using
          (eq_div_iff zero : actual = target / known ↔ actual * known = target)

theorem masked_product_fiber {Index : Type} (observed : Index → Bool)
    (known target actual : Index → K) :
    (∀ index, Holds (multiply (observed index) (known index) (target index)) (actual index)) ↔
      ∀ index, observed index = true → known index * actual index = target index := by
  simp only [multiply_iff]

namespace Controls

theorem zero_product_can_leave_a_parameter_free :
    multiply true (0 : ℚ) 0 = .free := by decide

theorem inconsistent_zero_product_has_no_exact_preimage :
    multiply true (0 : ℚ) 1 = .impossible := by decide

theorem relaxed_proposal_is_not_a_solution_certificate :
    Holds (multiplyProposal true (0 : ℚ) 1) 0 ∧ ¬ (0 : ℚ) * 0 = 1 := by
  norm_num [multiplyProposal, Holds]

theorem unobserved_coordinate_imposes_no_equation :
    Holds (multiply false (7 : ℚ) 19) 0 := by simp [multiply, Holds]

end Controls

end Mettapedia.Algorithms.Compression.MaskedScalarInverse
