import Std

/-!
# Rank-independent dense tensor values

This value model fixes the shape and ordered-entry contract shared by scalar,
vector, matrix and higher-rank numerical buffers. Checked reshaping preserves
entries exactly. Checked elementwise operations require equal shapes and valid
physical lengths; equal element counts alone do not admit an operation.

The model uses mathematical natural numbers and lists. Strides, native integer
overflow, allocation, mutable aliases, devices, foreign ownership and numerical
kernel refinement are separate implementation obligations. Elementwise lifting
does not define matrix multiplication or an arbitrary coefficient algebra.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.TensorShape

universe u v
variable {α : Type u} {β : Type v}

abbrev Shape := List Nat

/-- A scalar has one entry; any zero dimension makes the value empty. -/
def size : Shape → Nat
  | [] => 1
  | dimension :: remaining => dimension * size remaining

@[simp] theorem size_scalar : size [] = 1 := rfl

@[simp] theorem size_vector (n : Nat) : size [n] = n := by
  simp [size]

@[simp] theorem size_matrix (m n : Nat) : size [m, n] = m * n := by
  simp [size]

theorem size_append (left right : Shape) :
    size (left ++ right) = size left * size right := by
  induction left with
  | nil => simp [size]
  | cons dimension remaining ih => simp [size, ih, Nat.mul_assoc]

theorem size_zero_axis (before after : Shape) :
    size (before ++ 0 :: after) = 0 := by
  simp [size_append, size]

structure Buffer (α : Type u) where
  shape : Shape
  entries : List α
  deriving DecidableEq, Repr

def Buffer.Valid (buffer : Buffer α) : Prop :=
  buffer.entries.length = size buffer.shape

instance (buffer : Buffer α) : Decidable buffer.Valid :=
  inferInstanceAs (Decidable (buffer.entries.length = size buffer.shape))

inductive Error where
  | invalidBuffer
  | elementCountMismatch
  | shapeMismatch
  deriving DecidableEq, Repr

def checked (shape : Shape) (entries : List α) : Except Error (Buffer α) :=
  if entries.length = size shape then .ok ⟨shape, entries⟩
  else .error .invalidBuffer

def reshape (buffer : Buffer α) (shape : Shape) : Except Error (Buffer α) :=
  if buffer.Valid then
    if size shape = size buffer.shape then .ok ⟨shape, buffer.entries⟩
    else .error .elementCountMismatch
  else .error .invalidBuffer

def map (operation : α → β) (buffer : Buffer α) : Buffer β :=
  ⟨buffer.shape, buffer.entries.map operation⟩

def elementwise (operation : α → α → β) (left right : Buffer α) :
    Except Error (Buffer β) :=
  if left.Valid ∧ right.Valid then
    if left.shape = right.shape then
      .ok ⟨left.shape, List.zipWith operation left.entries right.entries⟩
    else .error .shapeMismatch
  else .error .invalidBuffer

theorem checked_success_iff (shape : Shape) (entries : List α) (out : Buffer α) :
    checked shape entries = .ok out ↔
      entries.length = size shape ∧ out = ⟨shape, entries⟩ := by
  by_cases valid : entries.length = size shape <;>
    simp [checked, valid, Eq.comm]

theorem checked_invalid (shape : Shape) (entries : List α)
    (invalid : entries.length ≠ size shape) :
    checked shape entries = .error .invalidBuffer := by
  simp [checked, invalid]

theorem checked_valid (shape : Shape) (entries : List α) (out : Buffer α)
    (success : checked shape entries = .ok out) : out.Valid := by
  obtain ⟨valid, rfl⟩ := (checked_success_iff shape entries out).mp success
  exact valid

theorem reshape_success_iff (buffer out : Buffer α) (shape : Shape) :
    reshape buffer shape = .ok out ↔
      buffer.Valid ∧ size shape = size buffer.shape ∧
        out = ⟨shape, buffer.entries⟩ := by
  by_cases valid : buffer.Valid
  · by_cases count : size shape = size buffer.shape <;>
      simp [reshape, valid, count, Eq.comm]
  · simp [reshape, valid]

theorem reshape_valid (buffer out : Buffer α) (shape : Shape)
    (success : reshape buffer shape = .ok out) : out.Valid := by
  obtain ⟨valid, count, rfl⟩ := (reshape_success_iff buffer out shape).mp success
  exact valid.trans count.symm

theorem reshape_preserves_entries (buffer out : Buffer α) (shape : Shape)
    (success : reshape buffer shape = .ok out) : out.entries = buffer.entries := by
  obtain ⟨_, _, rfl⟩ := (reshape_success_iff buffer out shape).mp success
  rfl

theorem reshape_sets_shape (buffer out : Buffer α) (shape : Shape)
    (success : reshape buffer shape = .ok out) : out.shape = shape := by
  obtain ⟨_, _, rfl⟩ := (reshape_success_iff buffer out shape).mp success
  rfl

theorem reshape_invalid (buffer : Buffer α) (shape : Shape)
    (invalid : ¬ buffer.Valid) : reshape buffer shape = .error .invalidBuffer := by
  simp [reshape, invalid]

theorem reshape_count_refusal (buffer : Buffer α) (shape : Shape)
    (valid : buffer.Valid) (different : size shape ≠ size buffer.shape) :
    reshape buffer shape = .error .elementCountMismatch := by
  simp [reshape, valid, different]

theorem reshape_identity (buffer : Buffer α) (valid : buffer.Valid) :
    reshape buffer buffer.shape = .ok buffer := by
  cases buffer
  simp_all [reshape]

theorem reshape_composition (buffer : Buffer α) (first last : Shape)
    (valid : buffer.Valid) (firstCount : size first = size buffer.shape)
    (lastCount : size last = size first) :
    (reshape buffer first).bind (fun middle => reshape middle last) =
      reshape buffer last := by
  have middleValid : (⟨first, buffer.entries⟩ : Buffer α).Valid :=
    valid.trans firstCount.symm
  have finalCount : size last = size buffer.shape := lastCount.trans firstCount
  have firstSuccess : reshape buffer first = .ok ⟨first, buffer.entries⟩ := by
    unfold reshape
    rw [if_pos valid, if_pos firstCount]
  rw [firstSuccess]
  change reshape ⟨first, buffer.entries⟩ last = reshape buffer last
  unfold reshape
  rw [if_pos middleValid, if_pos valid, if_pos lastCount, if_pos finalCount]

@[simp] theorem map_shape (operation : α → β) (buffer : Buffer α) :
    (map operation buffer).shape = buffer.shape := rfl

theorem map_valid_iff (operation : α → β) (buffer : Buffer α) :
    (map operation buffer).Valid ↔ buffer.Valid := by
  simp [map, Buffer.Valid]

theorem elementwise_success_iff (operation : α → α → β)
    (left right : Buffer α) (out : Buffer β) :
    elementwise operation left right = .ok out ↔
      left.Valid ∧ right.Valid ∧ left.shape = right.shape ∧
        out = ⟨left.shape, List.zipWith operation left.entries right.entries⟩ := by
  by_cases valid : left.Valid ∧ right.Valid
  · by_cases shapes : left.shape = right.shape <;>
      simp [elementwise, valid, shapes, Eq.comm]
  · rw [elementwise, if_neg valid]
    constructor
    · intro impossible
      cases impossible
    · intro success
      exact (valid ⟨success.1, success.2.1⟩).elim

theorem elementwise_valid (operation : α → α → β)
    (left right : Buffer α) (out : Buffer β)
    (success : elementwise operation left right = .ok out) : out.Valid := by
  obtain ⟨leftValid, rightValid, shapes, rfl⟩ :=
    (elementwise_success_iff operation left right out).mp success
  have lengths : left.entries.length = right.entries.length := by
    rw [leftValid, rightValid, shapes]
  change (List.zipWith operation left.entries right.entries).length = size left.shape
  rw [List.length_zipWith, ← lengths, Nat.min_self]
  exact leftValid

theorem elementwise_shape_refusal (operation : α → α → β)
    (left right : Buffer α) (valid : left.Valid ∧ right.Valid)
    (different : left.shape ≠ right.shape) :
    elementwise operation left right = .error .shapeMismatch := by
  simp [elementwise, valid, different]

theorem elementwise_invalid (operation : α → α → β)
    (left right : Buffer α) (invalid : ¬ left.Valid ∨ ¬ right.Valid) :
    elementwise operation left right = .error .invalidBuffer := by
  cases invalid with
  | inl invalid => simp [elementwise, invalid]
  | inr invalid => simp [elementwise, invalid]

theorem scalar_and_empty_control :
    checked [] ([7] : List Nat) = .ok ⟨[], [7]⟩ ∧
    checked [] ([] : List Nat) = .error .invalidBuffer ∧
    checked [2, 0, 3] ([] : List Nat) = .ok ⟨[2, 0, 3], []⟩ := by
  constructor
  · rfl
  · constructor <;> rfl

theorem equal_count_does_not_mean_equal_shape :
    elementwise (Nat.add) (⟨[2, 2], [1, 2, 3, 4]⟩ : Buffer Nat)
      ⟨[4], [5, 6, 7, 8]⟩ = .error .shapeMismatch := by
  rfl

theorem malformed_buffer_cannot_reshape :
    reshape (⟨[2, 2], [1, 2, 3]⟩ : Buffer Nat) [3] = .error .invalidBuffer := by
  rfl

theorem reshape_order_control :
    reshape (⟨[2, 3], [1, 2, 3, 4, 5, 6]⟩ : Buffer Nat) [3, 2] =
      .ok ⟨[3, 2], [1, 2, 3, 4, 5, 6]⟩ := by rfl

theorem invalid_buffer_cannot_zip :
    elementwise (Nat.add) (⟨[3], [1, 2]⟩ : Buffer Nat)
      ⟨[3], [3, 4, 5]⟩ = .error .invalidBuffer := by rfl

end Mettapedia.Algebra.TensorShape
