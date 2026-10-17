import Std

/-!
# Agent-owned memory refinement

The model describes one semantic record's queued edits and retained originals,
and a hierarchical node's retirement. There are no retry quotas or approval
states. Native conditional batches implement the operation-identity comparison;
runtime tests check storage recovery separately. These laws concern state and
provenance, not the truth or quality of an agent's interpretation.
-/

namespace Mettapedia.CognitiveArchitecture.Memory.MemoryRefinement

structure Intent where
  operation : Nat
  text : String
  deriving DecidableEq

structure Memory where
  current : Option String
  pending : Option Intent
  originals : List String

def archive (m : Memory) : List String := m.current.toList ++ m.originals

def edit (m : Memory) (i : Intent) : Memory := { m with pending := some i }

def complete (m : Memory) (i : Intent) : Memory :=
  if m.pending = some i then
    { current := some i.text, pending := none, originals := i.text :: archive m }
  else m

def forget (m : Memory) : Memory :=
  { current := none, pending := none, originals := archive m }

theorem completion_after_forget (m : Memory) (i : Intent) :
    complete (forget m) i = forget m := by
  simp [complete, forget]

theorem forgotten_record_is_absent (m : Memory) : (forget m).current = none := rfl

theorem forgotten_record_has_no_queued_edit (m : Memory) : (forget m).pending = none := rfl

theorem old_completion_cannot_replace_new_edit (m : Memory) (old newer : Intent)
    (different : old.operation ≠ newer.operation) :
    complete (edit m newer) old = edit m newer := by
  have unequal : newer ≠ old := by
    intro equal
    exact different (congrArg Intent.operation equal).symm
  simp [complete, edit, unequal]

theorem current_completion_installs_text (m : Memory) (i : Intent) :
    (complete (edit m i) i).current = some i.text := by
  simp [complete, edit]

theorem successful_edit_settles_itself (m : Memory) (i : Intent) :
    (complete (edit m i) i).pending = none := by
  simp [complete, edit]

theorem forget_preserves_originals (m : Memory) (text : String)
    (saved : text ∈ m.originals) : text ∈ (forget m).originals := by
  simp only [forget, archive, List.mem_append]
  exact Or.inr saved

theorem complete_preserves_originals (m : Memory) (i : Intent) (text : String)
    (saved : text ∈ m.originals) : text ∈ (complete m i).originals := by
  unfold complete
  split
  · simp only [archive, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr saved)
  · exact saved

theorem queued_edit_preserves_current (m : Memory) (i : Intent) :
    (edit m i).current = m.current := rfl

structure Node where
  retired : Bool
  revision : Nat
  body : String
  children : List Nat
  originals : List String

def retire (n : Node) : Node :=
  { n with retired := true, revision := n.revision + 1,
           originals := n.body :: n.originals }

def capture (n : Node) (children : List Nat) : Node :=
  { n with children := children, revision := n.revision + 1 }

def recalled (n : Node) : Bool := !n.retired

def restore (n : Node) (body : String) : Node :=
  { n with retired := false, body := body, revision := n.revision + 1,
           originals := n.body :: n.originals }

theorem retired_node_is_not_recalled (n : Node) : recalled (retire n) = false := rfl

theorem capture_preserves_retirement (n : Node) (children : List Nat) :
    recalled (capture (retire n) children) = false := rfl

theorem retirement_preserves_body (n : Node) : (retire n).body = n.body := rfl

theorem retirement_changes_revision (n : Node) : (retire n).revision ≠ n.revision := by
  simp [retire]

theorem explicit_restore_reactivates (n : Node) (body : String) :
    recalled (restore n body) = true := rfl


end Mettapedia.CognitiveArchitecture.Memory.MemoryRefinement
