import Mettapedia.Logic.DerivationGraph.BorrowedCursor

/-!
# Source-indexed retained cursors

Checked judgments come from the source-independent derivation-graph core.
A retained cursor is additionally indexed by the exact source and witness interface that
checked its prefix. Equal printed labels or revisions do not identify these
parameters. Reuse under another source requires a separate read-coherence law.

Proof fields are erased by execution; the source history is not a runtime
journal. Private Lean construction establishes logical validity, not native
capability security or lifetime safety. Those are implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.DerivationGraph

universe u v w

variable {J : Type u} {Origin : Type w} {rules : List J → J → Prop}


namespace BorrowedCursor

/-- A checked prefix belongs to its source and witness interface, not to a
caller-supplied label. The existential history is erased proof data. -/
structure CheckedCursor (interface : RuleWitness.{u, v} rules)
    (store : Store J interface.W Origin) where
  private mk ::
  state : State J
  checkedPrefix : ∃ schedule, run interface store (start store) schedule = some state

namespace CheckedCursor

def begin (interface : RuleWitness.{u, v} rules) (store : Store J interface.W Origin) :
    CheckedCursor interface store :=
  ⟨start store, [], rfl⟩

/-- Resume the actual source-address worker. Successful checks become the next
prefix; refusing leaves the caller's previous immutable value available. -/
def advance {interface : RuleWitness.{u, v} rules} {store : Store J interface.W Origin}
    (cursor : CheckedCursor interface store) (schedule : List NodeId) :
    Option (CheckedCursor interface store) :=
  match accepted : run interface store cursor.state schedule with
  | none => none
  | some state => some ⟨state, by
      obtain ⟨prior, checked⟩ := cursor.checkedPrefix
      exact ⟨prior ++ schedule, by rw [run_append, checked]; exact accepted⟩⟩

theorem advance_state {interface : RuleWitness.{u, v} rules}
    {store : Store J interface.W Origin} (cursor : CheckedCursor interface store)
    (schedule : List NodeId) :
    (cursor.advance schedule).map state = run interface store cursor.state schedule := by
  unfold advance
  split <;> simp_all

/-- A root projection does not instantiate or freshen the retained judgment. -/
def root {interface : RuleWitness.{u, v} rules} {store : Store J interface.W Origin}
    (cursor : CheckedCursor interface store) (source : NodeId) :
    Option (CheckedJudgment rules) :=
  match found : rootAt cursor.state source with
  | none => none
  | some claim => some (CheckedJudgment.ofDerivation claim (by
      obtain ⟨schedule, checked⟩ := cursor.checkedPrefix
      exact root_derivable interface store schedule cursor.state checked source claim found))

theorem root_judgment {interface : RuleWitness.{u, v} rules}
    {store : Store J interface.W Origin} (cursor : CheckedCursor interface store)
    (source : NodeId) :
    (cursor.root source).map CheckedJudgment.judgment = rootAt cursor.state source := by
  unfold root
  split <;> simp_all [CheckedJudgment.ofDerivation]

/-- A stored prefix is genuine graph evidence in the same rule system. -/
theorem root_has_certificate {interface : RuleWitness.{u, v} rules}
    {store : Store J interface.W Origin} (cursor : CheckedCursor interface store)
    (source : NodeId) (claim : J) (found : rootAt cursor.state source = some claim) :
    ∃ (nodes : List (Node J interface.W Origin)) (root : Nat),
      (CheckedJudgment.mint interface nodes root).map
      CheckedJudgment.judgment = some claim := by
  obtain ⟨schedule, checked⟩ := cursor.checkedPrefix
  obtain ⟨nodes, _, replayed, _⟩ :=
    run_materializes interface store (start store) cursor.state schedule checked
  cases address : indexAt cursor.state.checked source with
  | none => simp [rootAt, address] at found
  | some index =>
      exact ⟨nodes, index, (CheckedJudgment.mint_iff interface nodes index claim).mpr
        ⟨cursor.state.cache, replayed, by simpa [rootAt, address] using found⟩⟩

/-- A different source is admissible only after coherence of the actual
checked footprint has been supplied. Its revision may change. -/
def transport {interface : RuleWitness.{u, v} rules}
    {left right : Store J interface.W Origin} (cursor : CheckedCursor interface left)
    (reads : ∀ source index, (source, index) ∈ cursor.state.checked →
      left.read source = right.read source) :
    CheckedCursor interface right :=
  ⟨atRevision right.revision cursor.state, by
    obtain ⟨schedule, checked⟩ := cursor.checkedPrefix
    have stable : ∀ source ∈ schedule, left.read source = right.read source := by
      intro source present
      obtain ⟨index, found⟩ :=
        run_sources_checked interface left (start left) cursor.state schedule checked source present
      exact reads source index found
    have same := run_rebased_read_stable interface left right (start left) schedule rfl stable
    have begins : atRevision right.revision (start left) = start right := rfl
    exact ⟨schedule, by rw [begins, checked] at same; exact same⟩⟩

theorem transport_state {interface : RuleWitness.{u, v} rules}
    {left right : Store J interface.W Origin} (cursor : CheckedCursor interface left)
    (reads : ∀ source index, (source, index) ∈ cursor.state.checked →
      left.read source = right.read source) :
    (cursor.transport reads).state = atRevision right.revision cursor.state := rfl

/-- Executable validation reads only the retained prefix's actual source
addresses. It does not call the generic rule-instance checker or scan unrelated
rows; provider reads and their decoding/admission work still have a cost.
The left provider must denote the retained snapshot, not a second callback
into the same subsequently mutated map. -/
def revalidate {interface : RuleWitness.{u, v} rules}
    {left : Store J interface.W Origin} [DecidableEq J] [DecidableEq interface.W]
    [DecidableEq Origin] (cursor : CheckedCursor interface left)
    (right : Store J interface.W Origin) : Option (CheckedCursor interface right) :=
  if accepted : cursor.state.checked.all
      (fun entry => decide (left.read entry.1 = right.read entry.1)) = true then
    some (cursor.transport (by
      intro source index present
      have equal := (List.all_eq_true.mp accepted) (source, index) present
      exact of_decide_eq_true equal))
  else none

theorem revalidate_isSome_iff {interface : RuleWitness.{u, v} rules}
    {left : Store J interface.W Origin} [DecidableEq J] [DecidableEq interface.W]
    [DecidableEq Origin] (cursor : CheckedCursor interface left)
    (right : Store J interface.W Origin) :
    (cursor.revalidate right).isSome = true ↔
      ∀ entry ∈ cursor.state.checked, left.read entry.1 = right.read entry.1 := by
  unfold revalidate
  split
  · rename_i accepted
    constructor
    · intro _ entry present
      exact of_decide_eq_true (List.all_eq_true.mp accepted entry present)
    · intro _
      rfl
  · rename_i refused
    constructor
    · intro impossible
      cases impossible
    · intro reads
      exact False.elim (refused (List.all_eq_true.mpr (fun entry present =>
        decide_eq_true (reads entry present))))

end CheckedCursor
end BorrowedCursor
end Mettapedia.Logic.DerivationGraph
