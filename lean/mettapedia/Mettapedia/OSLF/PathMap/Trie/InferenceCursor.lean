import Mettapedia.OSLF.PathMap.Trie.CursorProtocol
import Mettapedia.Machines.Cursor.ProofChecking

/-!
# Byte-cursor reads for the shared inference checker

An independently recursive Huet-zipper walk reads stored proof rows. Its
read/down client uses the existing indexed cursor protocol, so a scheduler
pause retains the actual path, zipper and reply-dependent continuation.
Direct finite-trie lookup is the independent representation specification.

The graph-store adapter reads a whole key synchronously. The separately proved
navigation client can pause within that key; interleaving those navigation
states into the graph checker's own transition is a further refinement.

The common graph checker still supplies ordered premise resolution and each
logic's separately checked rule interface. Navigation does not perform logical
inference, grant authority, or make a rule's binding/substitution work free.
The charge here counts cursor requests, not sibling scans, bytes allocated,
native instructions or Rust/C execution. Snapshots are immutable model values;
native source ownership and decoding remain separate refinements.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.PathMap.Trie.InferenceCursor

open Mettapedia.Machines.Cursor
open Mettapedia.TypeTheory
open _root_.CategoryTheory

variable {Value : Type}

/-- One request per descent attempt or final value inspection. -/
def walk (zipper : HuetTrieZipper Value) :
    List UInt8 → Nat × Option Value × HuetTrieZipper Value
  | [] => (1, zipper.focus.lookup [], zipper)
  | byte :: rest =>
      match zipper.descendByte byte with
      | none => (1, none, zipper)
      | some child =>
          let result := walk child rest
          (result.1 + 1, result.2)

private theorem missing_child_lookup (byte : UInt8) (rest : List UInt8)
    (children : List (UInt8 × FTrie Value))
    (missing : CursorProtocol.findChild byte children = none) :
    FTrie.lookupChild byte rest children = none := by
  induction children with
  | nil => rfl
  | cons entry children ih =>
      rcases entry with ⟨key, child⟩
      by_cases equal : (key == byte) = true
      · simp [CursorProtocol.findChild, equal] at missing
      · simp only [CursorProtocol.findChild, equal, Bool.false_eq_true, ↓reduceIte] at missing
        simpa [FTrie.lookupChild, equal] using ih missing

theorem missing_descent_lookup (zipper : HuetTrieZipper Value) (byte : UInt8)
    (rest : List UInt8) (missing : zipper.descendByte byte = none) :
    zipper.focus.lookup (byte :: rest) = none := by
  have absent := CursorProtocol.descend_focus zipper byte
  rw [missing] at absent
  rcases zipper with ⟨tree, crumbs⟩
  cases tree with
  | empty => rfl
  | node value children =>
      exact missing_child_lookup byte rest children (by simpa [CursorProtocol.descend] using absent.symm)

/-- Exact lookup includes absent edges and valueless existing nodes. -/
theorem walk_lookup (zipper : HuetTrieZipper Value) (path : List UInt8) :
    (walk zipper path).2.1 = zipper.focus.lookup path := by
  induction path generalizing zipper with
  | nil => rfl
  | cons byte rest ih =>
      cases descended : zipper.descendByte byte with
      | none => simpa [walk, descended] using (missing_descent_lookup zipper byte rest descended).symm
      | some child =>
          simpa [walk, descended, ih] using
            HuetTrieZipper.focus_lookup_descend zipper byte child rest descended

theorem walk_requests_bound (zipper : HuetTrieZipper Value) (path : List UInt8) :
    (walk zipper path).1 ≤ path.length + 1 := by
  induction path generalizing zipper with
  | nil => rfl
  | cons byte rest ih =>
      cases descended : zipper.descendByte byte with
      | none => simp [walk, descended]
      | some child =>
          simpa [walk, descended, Nat.add_assoc] using Nat.add_le_add_right (ih child) 1

inductive Control (Value : Type) where
  | reading (remaining : List UInt8)
  | finished (value : Option Value)

abbrev client (Value : Type) :
    Client (P := CursorProtocol.protocol Value) (Return := fun _ _ => Option Value) where
  V _ _ := Control Value
  str := fun _ _ => ↾(fun control => match control with
    | .finished value => ⟨.inl value, fun impossible => nomatch impossible⟩
    | .reading [] => ⟨.inr .peek, fun value => .finished value⟩
    | .reading (byte :: rest) =>
        ⟨.inr (.down byte), fun found => match found with
          | true => .reading rest
          | false => .finished none⟩)

def packet (zipper : HuetTrieZipper Value) (path : List UInt8) :
    Packet (CursorProtocol.zippers Value) (client Value) () :=
  ⟨(), .reading path, zipper⟩

theorem finished_advance (fuel : Nat) (zipper : HuetTrieZipper Value) (value : Option Value) :
    advance (CursorProtocol.zippers Value) (client Value) (fun _ _ => 1) (base := ()) (fuel + 1)
      ⟨(), .finished value, zipper⟩ = (0, .done ⟨(), value, zipper⟩) := rfl

private theorem advance_reading_cons (fuel : Nat) (zipper : HuetTrieZipper Value)
    (byte : UInt8) (rest : List UInt8) :
    advance (CursorProtocol.zippers Value) (client Value) (fun _ _ => 1) (fuel + 1)
      (packet zipper (byte :: rest)) =
      match zipper.descendByte byte with
      | none =>
          let result := advance (CursorProtocol.zippers Value) (client Value) (fun _ _ => 1)
            (base := ()) fuel ⟨(), .finished none, zipper⟩
          (1 + result.1, result.2)
      | some child =>
          let result := advance (CursorProtocol.zippers Value) (client Value) (fun _ _ => 1)
            fuel (packet child rest)
          (1 + result.1, result.2) := by
  cases descended : zipper.descendByte byte <;>
    simp [advance, packet, client, CursorProtocol.zippers, descended]

/-- Completion retains the actual final zipper; failed descent does not
replace it with a fabricated root or discard its parent contexts. -/
theorem client_complete (zipper : HuetTrieZipper Value) (path : List UInt8) :
    advance (CursorProtocol.zippers Value) (client Value) (fun _ _ => 1) (path.length + 2)
      (packet zipper path) =
      ((walk zipper path).1, .done ⟨(), (walk zipper path).2.1, (walk zipper path).2.2⟩) := by
  induction path generalizing zipper with
  | nil => rfl
  | cons byte rest ih =>
      have fuel : (byte :: rest).length + 2 = (rest.length + 2) + 1 := by simp
      rw [fuel, advance_reading_cons]
      cases descended : zipper.descendByte byte with
      | none =>
          rw [show rest.length + 2 = (rest.length + 1) + 1 by omega,
            finished_advance]
          simp [walk, descended]
      | some child =>
          dsimp only
          rw [ih child]
          simp [walk, descended, Nat.add_comm]

theorem resume_exact (zipper : HuetTrieZipper Value) (path : List UInt8) (first later : Nat) :
    advance (CursorProtocol.zippers Value) (client Value) (fun _ _ => 1) (first + later)
      (packet zipper path) =
      resume (CursorProtocol.zippers Value) (client Value) (fun _ _ => 1) later
        (advance (CursorProtocol.zippers Value) (client Value) (fun _ _ => 1) first
          (packet zipper path)) := advance_add _ _ _ _ _ _

namespace Rows

open Mettapedia.Logic DerivationGraph

variable {J W Origin : Type}

/-- A stored occurrence has an address independently of its judgment contents. -/
structure Entry (J W Origin : Type) where
  address : Nat
  node : BorrowedCursor.StoredNode J W Origin
  deriving DecidableEq

structure Source (J W Origin : Type) where
  revision : Nat
  rows : FTrie (Entry J W Origin)
  key : Nat → List UInt8

/-- A colliding path cannot silently substitute another source occurrence. -/
def admitEntry (address : Nat) (entry : Option (Entry J W Origin)) :
    Option (BorrowedCursor.StoredNode J W Origin) := do
  let row ← entry
  if row.address = address then some row.node else none

/-- The implementation reads by actual zipper descents, not by materializing
an expanded proof tree or calling finite-trie lookup on the complete key. -/
def cursorStore (source : Source J W Origin) : BorrowedCursor.Store J W Origin where
  revision := source.revision
  read address := admitEntry address
    (walk (HuetTrieZipper.fromRoot source.rows) (source.key address)).2.1

/-- Independent representation specification using original finite-trie lookup. -/
def lookupStore (source : Source J W Origin) : BorrowedCursor.Store J W Origin where
  revision := source.revision
  read address := admitEntry address (source.rows.lookup (source.key address))

theorem read_lookup (source : Source J W Origin) (address : Nat) :
    (cursorStore source).read address = (lookupStore source).read address := by
  simp only [cursorStore, lookupStore, walk_lookup, HuetTrieZipper.fromRoot]

theorem store_lookup (source : Source J W Origin) :
    cursorStore source = lookupStore source := by
  have reads : (cursorStore source).read = (lookupStore source).read :=
    funext (read_lookup source)
  cases source
  simp only [cursorStore, lookupStore] at reads ⊢
  exact congrArg (BorrowedCursor.Store.mk _) reads

theorem wrong_occurrence_refused (address : Nat) (row : Entry J W Origin)
    (different : row.address ≠ address) : admitEntry address (some row) = none := by
  simp [admitEntry, different]

/-- The actual generic inference worker has identical success, refusal, ordered
premise lookup and retained cache under these two independent readers. -/
theorem run_lookup {rules : List J → J → Prop} (interface : RuleWitness rules)
    (source : Source J interface.W Origin) (state : BorrowedCursor.State J)
    (schedule : List Nat) :
    BorrowedCursor.run interface (cursorStore source) state schedule =
      BorrowedCursor.run interface (lookupStore source) state schedule := by
  rw [store_lookup]

theorem replay_iff {rules : List J → J → Prop} (interface : RuleWitness rules)
    (source : Source J interface.W Origin) (state result : BorrowedCursor.State J)
    (schedule : List Nat) (current : state.revision = source.revision) :
    BorrowedCursor.run interface (cursorStore source) state schedule = some result ↔
      ∃ nodes, BorrowedCursor.materialize (lookupStore source)
          state.checked state.cache.size schedule = some (nodes, result.checked) ∧
        DerivationGraph.replayFrom interface state.cache nodes = some result.cache ∧
        result.revision = state.revision := by
  rw [run_lookup]
  exact BorrowedCursor.run_iff_materialized interface _ state result schedule current

/-- This conclusion refers to the independent inference predicate, not a
proposition defined to mean acceptance by this cursor implementation. -/
theorem root_valid {rules : List J → J → Prop} (interface : RuleWitness rules)
    (source : Source J interface.W Origin) (schedule : List Nat)
    (result : BorrowedCursor.State J)
    (accepted : BorrowedCursor.run interface (cursorStore source)
      (BorrowedCursor.start (cursorStore source)) schedule = some result)
    (address : Nat) (claim : J) (found : BorrowedCursor.rootAt result address = some claim) :
    Derives rules claim :=
  BorrowedCursor.root_derivable interface _ schedule result accepted address claim found

end Rows

end Mettapedia.OSLF.PathMap.Trie.InferenceCursor
