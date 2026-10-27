import Mettapedia.Machines.NativeStoreTransactions

/-!
# Immutable disk index contracts

The native byte-key kernel stores checksummed, immutable nodes. Child
references precede a parent. Preparing new paths only appends; publication of
one synchronized root belongs to the existing journal owner. This separates
building a candidate from acknowledging an application transaction.

This model proves that appending cannot change reads from an old valid root,
and that increasing critical-bit paths have a key-size depth bound. It does
not yet prove the C insertion algorithm, byte codec, checksums, filesystem or
service integration. Those remain explicit refinement obligations.
-/

namespace Mettapedia.Machines.NativeDiskIndex

abbrev Key := List Bool

inductive Node where
  | leaf (key : Key) (value : Nat)
  | branch (bit left right : Nat)
deriving DecidableEq, Repr

abbrev Heap := Nat → Option Node

inductive Answer where
  | absent
  | value (reference : Nat)
  | corrupt
deriving DecidableEq, Repr

def lookup : Nat → Heap → Nat → Key → Answer
  | _, _, 0, _ => .absent
  | 0, _, _ + 1, _ => .corrupt
  | fuel + 1, heap, address + 1, key =>
    match heap (address + 1) with
    | none => .corrupt
    | some (.leaf stored value) => if stored = key then .value value else .absent
    | some (.branch bit left right) =>
      lookup fuel heap (if key[bit]?.getD false then right else left) key

def closedBelow (heap : Heap) (endOffset : Nat) : Prop :=
  ∀ address ≤ endOffset, ∀ bit left right,
    heap address = some (.branch bit left right) → left < address ∧ right < address

def extendsBelow (before after : Heap) (endOffset : Nat) : Prop :=
  ∀ address ≤ endOffset, after address = before address

theorem captured_root_read_is_unchanged (fuel : Nat) (before after : Heap)
    (endOffset root : Nat) (key : Key)
    (closed : closedBelow before endOffset)
    (unchanged : extendsBelow before after endOffset) (captured : root ≤ endOffset) :
    lookup fuel after root key = lookup fuel before root key := by
  induction fuel generalizing root with
  | zero => cases root <;> rfl
  | succ fuel ih =>
    cases root with
    | zero => rfl
    | succ address =>
      simp only [lookup, unchanged (address + 1) captured]
      cases found : before (address + 1) with
      | none => rfl
      | some node =>
        cases node with
        | leaf stored value => rfl
        | branch bit left right =>
          have children := closed (address + 1) captured bit left right found
          apply ih
          split <;> omega

def appendNode (heap : Heap) (address : Nat) (node : Node) : Heap :=
  fun location => if location = address then some node else heap location

theorem appending_preserves_old_prefix (heap : Heap) (endOffset address : Nat)
    (node : Node) (fresh : endOffset < address) :
    extendsBelow heap (appendNode heap address node) endOffset := by
  intro location bounded
  simp [appendNode, show location ≠ address by omega]

theorem appending_preserves_captured_reads (fuel : Nat) (heap : Heap)
    (endOffset root address : Nat) (node : Node) (key : Key)
    (closed : closedBelow heap endOffset) (captured : root ≤ endOffset)
    (fresh : endOffset < address) :
    lookup fuel (appendNode heap address node) root key = lookup fuel heap root key := by
  exact captured_root_read_is_unchanged fuel heap _ endOffset root key closed
    (appending_preserves_old_prefix heap endOffset address node fresh) captured

/-- These are the actual local conditions checked while descending: critical
bits increase and remain below the limit implied by the permitted key size. -/
def acceptsPath (start limit : Nat) : List Nat → Bool
  | [] => true
  | bit :: rest => start ≤ bit && bit < limit && acceptsPath (bit + 1) limit rest

theorem accepted_path_has_bounded_depth (start limit : Nat) (bits : List Nat)
    (accepted : acceptsPath start limit bits = true) : bits.length ≤ limit - start := by
  induction bits generalizing start with
  | nil => simp
  | cons bit rest ih =>
    simp only [acceptsPath, Bool.and_eq_true, decide_eq_true_eq] at accepted
    have restBound := ih (bit + 1) accepted.2
    simp only [List.length_cons]
    omega

theorem key_size_bounds_path_depth (keyBytes : Nat) (bits : List Nat)
    (accepted : acceptsPath 0 ((keyBytes + 1) * 9) bits = true) :
    bits.length ≤ (keyBytes + 1) * 9 := by
  simpa using accepted_path_has_bounded_depth 0 ((keyBytes + 1) * 9) bits accepted

end Mettapedia.Machines.NativeDiskIndex
