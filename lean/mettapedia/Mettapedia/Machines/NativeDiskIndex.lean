import Std
import Lean.Elab.Tactic.Omega

/-!
# Immutable disk index contracts

The native byte-key kernel stores checksummed, immutable nodes. Child
references precede a parent. Preparing new paths only appends; publication of
one synchronized root belongs to the existing journal owner. This separates
building a candidate from acknowledging an application transaction.

The lookup checks increasing/bounded critical bits, backward nonzero child
and value references, and leaf agreement with the traversed path. The model
proves captured-read preservation and a fuel bound for that checked lookup.
Keys are abstract bit views; the byte+1/terminator encoding and its injectivity
remain separate obligations, as do C insertion, codecs, checksums and I/O.
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

def followsPath (key : Key) (path : List (Nat × Bool)) : Bool :=
  path.all fun step => key[step.1]?.getD false == step.2

def lookup (limit : Nat) : Nat → Heap → Nat → Key → Nat → List (Nat × Bool) → Answer
  | _, _, 0, _, _, _ => .absent
  | 0, _, _ + 1, _, _, _ => .corrupt
  | fuel + 1, heap, address + 1, key, start, path =>
    match heap (address + 1) with
    | none => .corrupt
    | some (.leaf stored value) =>
      if 0 < value ∧ value < address + 1 ∧ followsPath stored path then
        if stored = key then .value value else .absent
      else .corrupt
    | some (.branch bit left right) =>
      if start ≤ bit ∧ bit < limit ∧ 0 < left ∧ 0 < right ∧ left < address + 1 ∧
          right < address + 1 ∧ left ≠ right then
        let side := key[bit]?.getD false
        lookup limit fuel heap (if side then right else left) key (bit + 1) ((bit, side) :: path)
      else .corrupt

def closedBelow (heap : Heap) (endOffset : Nat) : Prop :=
  ∀ address ≤ endOffset, ∀ bit left right,
    heap address = some (.branch bit left right) → left < address ∧ right < address

def extendsBelow (before after : Heap) (endOffset : Nat) : Prop :=
  ∀ address ≤ endOffset, after address = before address

theorem captured_root_read_is_unchanged (limit fuel : Nat) (before after : Heap)
    (endOffset root start : Nat) (key : Key) (path : List (Nat × Bool))
    (closed : closedBelow before endOffset)
    (unchanged : extendsBelow before after endOffset) (captured : root ≤ endOffset) :
    lookup limit fuel after root key start path = lookup limit fuel before root key start path := by
  induction fuel generalizing root start path with
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
          simp only
          split
          · apply ih
            split <;> omega
          · rfl

def appendNode (heap : Heap) (address : Nat) (node : Node) : Heap :=
  fun location => if location = address then some node else heap location

theorem appending_preserves_old_prefix (heap : Heap) (endOffset address : Nat)
    (node : Node) (fresh : endOffset < address) :
    extendsBelow heap (appendNode heap address node) endOffset := by
  intro location bounded
  simp [appendNode, show location ≠ address by omega]

theorem appending_preserves_captured_reads (limit fuel : Nat) (heap : Heap)
    (endOffset root address start : Nat) (node : Node) (key : Key) (path : List (Nat × Bool))
    (closed : closedBelow heap endOffset) (captured : root ≤ endOffset)
    (fresh : endOffset < address) :
    lookup limit fuel (appendNode heap address node) root key start path =
      lookup limit fuel heap root key start path := by
  exact captured_root_read_is_unchanged limit fuel heap _ endOffset root start key path closed
    (appending_preserves_old_prefix heap endOffset address node fresh) captured

/-- Once fuel exceeds the allowed critical-bit interval, more fuel cannot
change a result. This connects the path-size bound to the actual lookup. -/
theorem lookup_fuel_independent (limit : Nat) (heap : Heap) (key : Key) :
    ∀ (fuel extra root start : Nat) (path : List (Nat × Bool)), limit - start < fuel →
      lookup limit (fuel + extra) heap root key start path =
        lookup limit fuel heap root key start path := by
  intro fuel
  induction fuel with
  | zero => intro extra root start path enough; omega
  | succ fuel ih =>
    intro extra root start path enough
    cases root with
    | zero =>
      rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
      rfl
    | succ address =>
      rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega]
      simp only [lookup]
      cases heap (address + 1) with
      | none => rfl
      | some node =>
        cases node with
        | leaf stored value => rfl
        | branch bit left right =>
          simp only
          split
          · exact ih extra _ (bit + 1) _ (by omega)
          · rfl

theorem key_size_fuel_suffices (keyBytes : Nat) (heap : Heap) (root : Nat)
    (key : Key) (extra : Nat) :
    lookup ((keyBytes + 1) * 9) ((keyBytes + 1) * 9 + 1 + extra) heap root key 0 [] =
      lookup ((keyBytes + 1) * 9) ((keyBytes + 1) * 9 + 1) heap root key 0 [] :=
  lookup_fuel_independent _ heap key _ extra root 0 [] (by omega)

def malformedHeap : Heap
  | 3 => some (.leaf [false] 1)
  | 4 => some (.leaf [true] 2)
  | 5 => some (.branch 0 3 4)
  | 6 => some (.leaf [true, true] 2)
  | 7 => some (.branch 0 5 6)
  | _ => none

theorem repeated_critical_bit_is_refused :
    lookup 100 100 malformedHeap 7 [false] 0 [] = .corrupt := by decide

theorem out_of_range_critical_bit_is_refused :
    lookup 0 100 malformedHeap 5 [false] 0 [] = .corrupt := by decide

theorem misplaced_leaf_is_refused :
    lookup 100 100 malformedHeap 3 [true] 0 [(0, true)] = .corrupt := by decide

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
