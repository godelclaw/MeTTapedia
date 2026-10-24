import Mathlib.Tactic

/-!
# Checked signed-word arithmetic and guarded scalar publication

The reference classifies an exact result by its signed range. The checked
realization first narrows it to a signed word and detects whether narrowing
changed the value. Its temporary result is published only on success.

This is the arithmetic/cast contract used by the native checked-integer
service. It does not verify a C compiler, processor overflow flags, ABI layout,
or native memory. The guarded adapter preserves its prior output on refusal.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CheckedIntegerTransfer

def Fits (limit value : Int) : Prop := -limit ≤ value ∧ value < limit

instance (limit value : Int) : Decidable (Fits limit value) :=
  inferInstanceAs (Decidable (-limit ≤ value ∧ value < limit))

def narrow (limit value : Int) : Int := (value + limit) % (2 * limit) - limit

theorem narrow_fits (limit value : Int) (positive : 0 < limit) :
    Fits limit (narrow limit value) := by
  have modulus : 0 < 2 * limit := by omega
  have lower := Int.emod_nonneg (value + limit) (by omega : 2 * limit ≠ 0)
  have upper := Int.emod_lt_of_pos (value + limit) modulus
  unfold Fits narrow
  omega

theorem narrow_eq_iff (limit value : Int) (positive : 0 < limit) :
    narrow limit value = value ↔ Fits limit value := by
  constructor
  · intro same
    simpa [same] using narrow_fits limit value positive
  · intro bounded
    have lower : 0 ≤ value + limit := by rcases bounded with ⟨lower, _⟩; omega
    have upper : value + limit < 2 * limit := by rcases bounded with ⟨_, upper⟩; omega
    simp [narrow, Int.emod_eq_of_lt lower upper]

structure Checked where
  temporary : Int
  overflow : Bool
  deriving DecidableEq, Repr

def check (limit exact : Int) : Checked :=
  let temporary := narrow limit exact
  ⟨temporary, decide (temporary ≠ exact)⟩

def publish (result : Checked) (prior : Int) : Bool × Int :=
  if result.overflow then (false, prior) else (true, result.temporary)

def wideReference (limit exact prior : Int) : Bool × Int :=
  if Fits limit exact then (true, exact) else (false, prior)

theorem checked_publication_eq_reference (limit exact prior : Int)
    (positive : 0 < limit) :
    publish (check limit exact) prior = wideReference limit exact prior := by
  by_cases bounded : Fits limit exact
  · have same := (narrow_eq_iff limit exact positive).mpr bounded
    simp [publish, check, wideReference, bounded, same]
  · have different : narrow limit exact ≠ exact := by
      intro same
      exact bounded ((narrow_eq_iff limit exact positive).mp same)
    simp [publish, check, wideReference, bounded, different]

theorem overflow_preserves_output (limit exact prior : Int) (positive : 0 < limit)
    (overflow : ¬ Fits limit exact) : publish (check limit exact) prior = (false, prior) := by
  rw [checked_publication_eq_reference limit exact prior positive]
  simp [wideReference, overflow]

theorem successful_value_is_exact (limit exact prior : Int) (positive : 0 < limit)
    (bounded : Fits limit exact) : publish (check limit exact) prior = (true, exact) := by
  rw [checked_publication_eq_reference limit exact prior positive]
  simp [wideReference, bounded]

inductive Operation where
  | add
  | sub
  | mul
  deriving DecidableEq, Repr

def Operation.eval : Operation → Int → Int → Int
  | .add, left, right => left + right
  | .sub, left, right => left - right
  | .mul, left, right => left * right

theorem scalar_operation_transfer (operation : Operation) (limit left right prior : Int)
    (positive : 0 < limit) :
    publish (check limit (operation.eval left right)) prior =
      wideReference limit (operation.eval left right) prior :=
  checked_publication_eq_reference _ _ _ positive

theorem int64_operands_have_exact_int128_result (operation : Operation) (left right : Int)
    (leftBound : Fits (2 ^ 63) left) (rightBound : Fits (2 ^ 63) right) :
    Fits (2 ^ 127) (operation.eval left right) := by
  have leftAbs : |left| ≤ (2 : Int) ^ 63 := abs_le.mpr ⟨leftBound.1, le_of_lt leftBound.2⟩
  have rightAbs : |right| ≤ (2 : Int) ^ 63 := abs_le.mpr ⟨rightBound.1, le_of_lt rightBound.2⟩
  have product : |left * right| ≤ (2 : Int) ^ 63 * 2 ^ 63 := by
    rw [abs_mul]
    exact mul_le_mul leftAbs rightAbs (abs_nonneg right) (by positivity)
  cases operation <;> simp only [Operation.eval, Fits]
  · have sum := abs_add_le left right
    rw [abs_le] at sum
    norm_num at leftAbs rightAbs sum ⊢
    omega
  · have difference : |left - right| ≤ |left| + |right| := by
      simpa [sub_eq_add_neg] using abs_add_le left (-right)
    rw [abs_le] at difference
    norm_num at leftAbs rightAbs difference ⊢
    omega
  · rw [abs_le] at product
    norm_num at product ⊢
    omega

namespace Controls

theorem overflow_cannot_publish_wrapped_value :
    publish (check (2 ^ 63) (2 ^ 63)) 19 = (false, 19) := by decide

theorem minimum_times_negative_one_promotes :
    publish (check (2 ^ 63) (Operation.mul.eval (-(2 ^ 63)) (-1))) 23 = (false, 23) := by decide

theorem exact_boundary_publishes :
    publish (check (2 ^ 63) (Operation.add.eval (2 ^ 63 - 1) 0)) 23 =
      (true, 2 ^ 63 - 1) := by decide

theorem negative_result_is_not_unsigned : publish (check 128 (-1)) 23 = (true, -1) := by decide

end Controls

end Mettapedia.Machines.CheckedIntegerTransfer
