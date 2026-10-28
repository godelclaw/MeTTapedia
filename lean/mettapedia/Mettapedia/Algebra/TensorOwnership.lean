import Mettapedia.Algebra.TensorShape

/-!
# Tensor ownership, immutable updates and exact value identity

Tensor elements here are bit patterns, not floating-point mathematical values.
This gives a reflexive value identity, including NaN encodings and signed zero.
Immutable updates preserve an alternative branch's input. Reuse of storage is
a separate optimization requiring exclusive access and no outstanding readers,
snapshots or published aliases. These are model contracts, not verification of
the C allocator, reference counter, codec or numerical kernels.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.TensorOwnership

open TensorShape

inductive DType where
  | i64 | f64 | u8
  deriving DecidableEq, Repr

def DType.width : DType → Nat
  | .i64 | .f64 => 8
  | .u8 => 1

structure Value where
  dtype : DType
  buffer : Buffer UInt64
  deriving DecidableEq, Repr

/-- This identity deliberately excludes storage addresses and alias counts. -/
def sameValue (left right : Value) : Prop :=
  left.dtype = right.dtype ∧ left.buffer = right.buffer

theorem sameValue_iff_eq (left right : Value) :
    sameValue left right ↔ left = right := by
  cases left
  cases right
  simp [sameValue]

theorem sameValue_refl (value : Value) : sameValue value value := ⟨rfl, rfl⟩

theorem sameValue_symm {left right : Value} (same : sameValue left right) :
    sameValue right left := ⟨same.1.symm, same.2.symm⟩

theorem sameValue_trans {first middle last : Value}
    (one : sameValue first middle) (two : sameValue middle last) :
    sameValue first last := ⟨one.1.trans two.1, one.2.trans two.2⟩

theorem sameValue_hash {left right : Value} (hash : Value → UInt64)
    (same : sameValue left right) : hash left = hash right := by
  rw [(sameValue_iff_eq left right).mp same]

def positiveZero : Value := ⟨.f64, ⟨[], [0]⟩⟩
def negativeZero : Value := ⟨.f64, ⟨[], [9223372036854775808]⟩⟩
def quietNaN : Value := ⟨.f64, ⟨[], [9221120237041090560]⟩⟩

theorem signed_zero_values_distinct : ¬ sameValue positiveZero negativeZero := by
  change ¬ (DType.f64 = DType.f64 ∧
    (⟨[], [0]⟩ : Buffer UInt64) = ⟨[], [9223372036854775808]⟩)
  decide

theorem nan_encoding_is_reflexive : sameValue quietNaN quietNaN := sameValue_refl _

theorem equal_entries_do_not_erase_dtype :
    ¬ sameValue ⟨.i64, ⟨[1], [7]⟩⟩ ⟨.f64, ⟨[1], [7]⟩⟩ := by
  simp [sameValue]

theorem equal_entries_do_not_erase_shape :
    ¬ sameValue ⟨.i64, ⟨[1], [7]⟩⟩ ⟨.i64, ⟨[], [7]⟩⟩ := by
  simp [sameValue]

/-- Each view, arena holder or pending operation contributes a retained hold. -/
structure Owner where
  holders : Nat
  pins : Nat
  deriving DecidableEq, Repr

def Owner.Live (owner : Owner) : Prop := 0 < owner.holders + owner.pins
def Owner.Releasable (owner : Owner) : Prop := owner.holders = 0 ∧ owner.pins = 0
def retain (owner : Owner) : Owner := { owner with holders := owner.holders + 1 }
def pin (owner : Owner) : Owner := { owner with pins := owner.pins + 1 }
def dropHolder (owner : Owner) : Owner := { owner with holders := owner.holders - 1 }
def unpin (owner : Owner) : Owner := { owner with pins := owner.pins - 1 }

theorem retained_owner_live (owner : Owner) : (retain owner).Live := by
  simp [retain, Owner.Live]
  omega

theorem pinned_owner_live (owner : Owner) : (pin owner).Live := by
  simp [pin, Owner.Live]
  omega

theorem pin_survives_last_holder (owner : Owner) (pending : 0 < owner.pins) :
    (dropHolder owner).Live := by
  simp [dropHolder, Owner.Live]
  omega

theorem holder_survives_unpin (owner : Owner) (held : 0 < owner.holders) :
    (unpin owner).Live := by
  simp [unpin, Owner.Live]
  omega

theorem live_not_releasable (owner : Owner) (live : owner.Live) :
    ¬ owner.Releasable := by
  simp only [Owner.Live, Owner.Releasable] at *
  omega

theorem releasable_iff_not_live (owner : Owner) :
    owner.Releasable ↔ ¬ owner.Live := by
  simp only [Owner.Releasable, Owner.Live]
  omega

theorem retain_drop_identity (owner : Owner) : dropHolder (retain owner) = owner := by
  cases owner
  simp [dropHolder, retain]

theorem pin_unpin_identity (owner : Owner) : unpin (pin owner) = owner := by
  cases owner
  simp [unpin, pin]

/-- Reference uniqueness alone does not imply exclusive access. -/
structure Access where
  owner : Owner
  writable : Bool
  exclusive : Bool
  savedReaders : Nat
  published : Bool
  deriving DecidableEq, Repr

def canReuse (access : Access) : Prop :=
  access.writable = true ∧ access.exclusive = true ∧
  access.owner.holders = 1 ∧ access.owner.pins = 0 ∧
  access.savedReaders = 0 ∧ access.published = false

theorem saved_alternative_blocks_reuse (access : Access)
    (saved : 0 < access.savedReaders) : ¬ canReuse access := by
  simp [canReuse]
  omega

theorem pending_operation_blocks_reuse (access : Access)
    (pending : 0 < access.owner.pins) : ¬ canReuse access := by
  simp [canReuse]
  omega

theorem published_value_blocks_reuse (access : Access)
    (published : access.published = true) : ¬ canReuse access := by
  simp [canReuse, published]

theorem unique_reference_is_insufficient :
    (⟨⟨1, 0⟩, true, true, 1, false⟩ : Access).owner.holders = 1 ∧
    ¬ canReuse ⟨⟨1, 0⟩, true, true, 1, false⟩ := by
  simp [canReuse]

/-- A branch receives a new buffer. The other branch retains the original. -/
def update (value : Value) (index : Nat) (bits : UInt64) : Value :=
  { value with buffer := { value.buffer with entries := value.buffer.entries.set index bits } }

def forkUpdate (value : Value) (index : Nat) (bits : UInt64) : Value × Value :=
  (update value index bits, value)

theorem update_preserves_dtype (value : Value) (index : Nat) (bits : UInt64) :
    (update value index bits).dtype = value.dtype := rfl

theorem update_preserves_shape (value : Value) (index : Nat) (bits : UInt64) :
    (update value index bits).buffer.shape = value.buffer.shape := rfl

theorem update_preserves_length (value : Value) (index : Nat) (bits : UInt64) :
    (update value index bits).buffer.entries.length = value.buffer.entries.length := by
  simp [update]

theorem update_preserves_validity (value : Value) (index : Nat) (bits : UInt64)
    (valid : value.buffer.Valid) : (update value index bits).buffer.Valid := by
  simpa [Buffer.Valid, update] using valid

theorem alternative_preserved (value : Value) (index : Nat) (bits : UInt64) :
    (forkUpdate value index bits).2 = value := rfl

theorem update_isolation_control :
    forkUpdate ⟨.i64, ⟨[2], [3, 4]⟩⟩ 0 99 =
      (⟨.i64, ⟨[2], [99, 4]⟩⟩, ⟨.i64, ⟨[2], [3, 4]⟩⟩) := by rfl

def checkedUpdate (value : Value) (index : Nat) (bits : UInt64) : Option Value :=
  if index < value.buffer.entries.length then some (update value index bits) else none

theorem checkedUpdate_success_iff (value result : Value) (index : Nat) (bits : UInt64) :
    checkedUpdate value index bits = some result ↔
      index < value.buffer.entries.length ∧ result = update value index bits := by
  by_cases fits : index < value.buffer.entries.length <;>
    simp [checkedUpdate, fits, Eq.comm]

theorem checkedUpdate_out_of_bounds (value : Value) (index : Nat) (bits : UInt64)
    (outside : value.buffer.entries.length ≤ index) :
    checkedUpdate value index bits = none := by
  simp [checkedUpdate, Nat.not_lt.mpr outside]

theorem checkedUpdate_preserves_validity (value result : Value) (index : Nat) (bits : UInt64)
    (valid : value.buffer.Valid) (success : checkedUpdate value index bits = some result) :
    result.buffer.Valid := by
  obtain ⟨_, rfl⟩ := (checkedUpdate_success_iff value result index bits).mp success
  exact update_preserves_validity value index bits valid

def checkedBytes (shape : Shape) (dtype : DType) (limit : Nat) : Option Nat :=
  let bytes := size shape * dtype.width
  if bytes ≤ limit then some bytes else none

theorem checkedBytes_bound (shape : Shape) (dtype : DType) (limit bytes : Nat)
    (success : checkedBytes shape dtype limit = some bytes) :
    bytes = size shape * dtype.width ∧ bytes ≤ limit := by
  simp only [checkedBytes] at success
  split at success
  · rename_i within
    simp only [Option.some.injEq] at success
    exact ⟨success.symm, success ▸ within⟩
  · cases success

theorem checkedBytes_zero_axis (before after : Shape) (dtype : DType) (limit : Nat) :
    checkedBytes (before ++ 0 :: after) dtype limit = some 0 := by
  simp [checkedBytes, size_zero_axis]

theorem checkedBytes_scalar (dtype : DType) (limit : Nat)
    (fits : dtype.width ≤ limit) : checkedBytes [] dtype limit = some dtype.width := by
  simp [checkedBytes, fits]

end Mettapedia.Algebra.TensorOwnership
