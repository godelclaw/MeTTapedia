import Mettapedia.OSLF.PathMap.Trie.InferenceCursor

/-! Concrete controls for retained navigation and source-addressed inference. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.PathMap.Trie.InferenceCursor.Controls

open Mettapedia.Logic DerivationGraph
open Mettapedia.Machines.Cursor

def tree : FTrie Nat := .node none [(7, .node none [(1, .node (some 42) [])])]

theorem reads_value : (walk (HuetTrieZipper.fromRoot tree) [7, 1]).2.1 = some 42 := rfl
theorem reads_valueless : (walk (HuetTrieZipper.fromRoot tree) [7]).2.1 = none := rfl
theorem missing_stops_at_parent :
    (walk (HuetTrieZipper.fromRoot tree) [7, 9, 1]).2.2.crumbs.length = 1 := rfl
theorem missing_charged_once :
    (walk (HuetTrieZipper.fromRoot tree) [7, 9, 1]).1 = 2 := rfl
theorem early_pause_retains_path :
    (advance (CursorProtocol.zippers Nat) (client Nat) (fun _ _ => 1) 1
      (packet (HuetTrieZipper.fromRoot tree) [7, 1])).2 =
      .paused ⟨(), .reading [1],
        ⟨.node none [(1, .node (some 42) [])], [⟨none, [], 7, []⟩]⟩⟩ := rfl
theorem resume_finishes :
    resume (CursorProtocol.zippers Nat) (client Nat) (fun _ _ => 1) 3
      (advance (CursorProtocol.zippers Nat) (client Nat) (fun _ _ => 1) 1
        (packet (HuetTrieZipper.fromRoot tree) [7, 1])) =
      (3, .done ⟨(), some 42,
        ⟨.node (some 42) [], [⟨none, [], 1, []⟩, ⟨none, [], 7, []⟩]⟩⟩) := rfl

/-- Independent arithmetic inference: every node adds one to its premise sum. -/
abbrev rules (premises : List Nat) (conclusion : Nat) : Prop :=
  conclusion = premises.sum + 1

abbrev interface : RuleWitness rules where
  W := Unit
  isInstance _ premises conclusion := decide (conclusion = premises.sum + 1)
  sound _ _ _ accepted := of_decide_eq_true accepted
  complete _ _ valid := ⟨(), by simpa only [decide_eq_true_eq] using valid⟩

def leaf (address : Nat) : Rows.Entry Nat Unit Unit := ⟨address, ⟨1, (), [], ()⟩⟩
def source : Rows.Source Nat Unit Unit :=
  ⟨0, .node none [(7, .node (some (leaf 7)) []),
    (8, .node (some ⟨8, ⟨3, (), [7, 7], ()⟩⟩) []),
    (9, .node (some (leaf 9)) [])], fun address => [address.toUInt8]⟩

def initial := BorrowedCursor.start (Rows.cursorStore source)

theorem repeated_premise_success :
    (BorrowedCursor.run interface (Rows.cursorStore source) initial [7, 8]).map
      (fun state => state.cache) = some #[1, 3] := rfl
theorem duplicate_schedule_refused :
    BorrowedCursor.run interface (Rows.cursorStore source) initial [7, 7] = none := rfl
theorem forward_premise_refused :
    BorrowedCursor.run interface (Rows.cursorStore source) initial [8, 7] = none := rfl
theorem equal_judgments_distinct_occurrences :
    (BorrowedCursor.run interface (Rows.cursorStore source) initial [7, 9]).map
      (fun state => state.cache) = some #[1, 1] := rfl
theorem missing_source_refused :
    BorrowedCursor.run interface (Rows.cursorStore source) initial [10] = none := rfl
theorem aliasing_key_refused :
    (Rows.cursorStore { source with key := fun _ => [7] }).read 8 = none := rfl
theorem truncated_byte_collision_refused :
    (Rows.cursorStore source).read 263 = none := rfl
theorem wrong_same_revision_row_refused :
    BorrowedCursor.run interface
      (Rows.cursorStore { source with rows := .node none [(7, .node (some (leaf 9)) [])] })
      initial [7] = none := rfl
theorem changed_revision_refused :
    BorrowedCursor.run interface (Rows.cursorStore { source with revision := 1 })
      initial [7] = none := rfl

def reuse (replacement : Rows.Source Nat Unit Unit) : Bool :=
  match (BorrowedCursor.CheckedCursor.begin interface (Rows.cursorStore source)).advance [7] with
  | none => false
  | some cursor => (cursor.revalidate (Rows.cursorStore replacement)).isSome

def unrelatedChange : Rows.Source Nat Unit Unit := { source with
  revision := 1
  rows := .node none [(7, .node (some (leaf 7)) []),
    (10, .node (some (leaf 10)) [])] }

theorem unrelated_edit_reuses_checked_prefix :
    reuse unrelatedChange = true := rfl

/-- Revalidating a prefix does not promise that an unread suffix still exists. -/
theorem reused_prefix_refetches_unread_suffix :
    ((BorrowedCursor.CheckedCursor.begin interface (Rows.cursorStore source)).advance [7] >>=
      fun cursor => cursor.revalidate (Rows.cursorStore unrelatedChange) >>=
        fun reused => reused.advance [8]).isSome = false := rfl

theorem changed_used_row_rejects_same_revision :
    reuse { source with
      rows := .node none [(7, .node (some ⟨7, ⟨2, (), [], ()⟩⟩) [])] } = false := rfl

theorem removed_used_row_rejects :
    reuse { source with rows := .node none [(9, .node (some (leaf 9)) [])] } = false := rfl

def brokenSource : Rows.Source Nat Unit Unit := { source with
  rows := .node none [(7, .node (some (leaf 7)) []),
    (8, .node (some ⟨8, ⟨4, (), [7, 7], ()⟩⟩) [])] }

theorem broken_head_refused :
    BorrowedCursor.run interface (Rows.cursorStore brokenSource)
      (BorrowedCursor.start (Rows.cursorStore brokenSource)) [7, 8] = none := rfl

theorem repaired_head_rechecked_after_prefix_transport :
    (((BorrowedCursor.CheckedCursor.begin interface (Rows.cursorStore brokenSource)).advance [7] >>=
      fun cursor => cursor.revalidate (Rows.cursorStore source) >>=
        fun reused => reused.advance [8]).map fun cursor => cursor.state.cache) = some #[1, 3] := rfl

theorem missing_edge_pause_keeps_terminal_observation :
    (advance (CursorProtocol.zippers Nat) (client Nat) (fun _ _ => 1) 2
      (packet (HuetTrieZipper.fromRoot tree) [7, 9, 1])).2 =
      .paused ⟨(), .finished none,
        ⟨.node none [(1, .node (some 42) [])], [⟨none, [], 7, []⟩]⟩⟩ := rfl

theorem missing_edge_complete_after_observation :
    advance (CursorProtocol.zippers Nat) (client Nat) (fun _ _ => 1) 3
      (packet (HuetTrieZipper.fromRoot tree) [7, 9, 1]) =
      (2, .done ⟨(), none,
        ⟨.node none [(1, .node (some 42) [])], [⟨none, [], 7, []⟩]⟩⟩) := rfl

end Mettapedia.OSLF.PathMap.Trie.InferenceCursor.Controls
