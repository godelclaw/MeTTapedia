import Mettapedia.Machines.CellRootObservation

/-!
# Removing pending alias frames from substitution entry

The framed reader records a pending variable frame for each binding followed.
The root-first reader uses the existing cell query and constructs no such
prefix. Their root answers and ordered lookup certificates agree. Independent
full-image refinement is inherited from CellRootObservation.

A descending alias family separates every queried cell. Consequently no
query correct for the same finite-fuel observation on all stores can use fewer
lookups on that family. The model charges cell reads and pending alias frames,
not hardware instructions, source ownership, result storage or native C.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RootPrefixSubstitution

open ContextualSequenceObservation CellRootObservation

variable {Literal : Type}

def framedQuery : Nat → Term Nat Literal →
    ReadOnlyQuery.Program Nat (Option (Term Nat Literal))
      (Option (Term Nat Literal × List Nat))
  | 0, _ => .pure none
  | fuel + 1, .var cell => .read cell fun stored =>
      match stored with
      | none => .pure (some (.var cell, []))
      | some entered => ReadOnlyQuery.map
          (Option.map fun (target, frames) => (target, cell :: frames))
          (framedQuery fuel entered)
  | _ + 1, value => .pure (some (value, []))

theorem erase_frames (cells : CellStore Literal) (fuel : Nat)
    (source : Term Nat Literal) :
    (ReadOnlyQuery.run cells (framedQuery fuel source)).answer.map Prod.fst =
      (ReadOnlyQuery.run cells (query fuel source)).answer := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
    cases source with
    | leaf _ => rfl
    | expr _ => rfl
    | var cell =>
      cases stored : cells cell with
      | none => simp [framedQuery, query, ReadOnlyQuery.run, stored]
      | some entered =>
        simpa [framedQuery, query, ReadOnlyQuery.run,
          ReadOnlyQuery.run_map, stored, Option.map_map, Function.comp_def] using ih entered

theorem same_lookup_certificate (cells : CellStore Literal) (fuel : Nat)
    (source : Term Nat Literal) :
    (ReadOnlyQuery.run cells (framedQuery fuel source)).reads =
      (ReadOnlyQuery.run cells (query fuel source)).reads := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
    cases source with
    | leaf _ => rfl
    | expr _ => rfl
    | var cell =>
      cases stored : cells cell with
      | none => simp [framedQuery, query, ReadOnlyQuery.run, stored]
      | some entered =>
        simp [framedQuery, query, ReadOnlyQuery.run, ReadOnlyQuery.run_map, stored, ih entered]

theorem framed_root_preserves_image (cells : CellStore Literal) (fuel : Nat)
    (source target : Term Nat Literal) (frames : List Nat)
    (found : (ReadOnlyQuery.run cells (framedQuery fuel source)).answer =
      some (target, frames)) (result : Term (Unit × Nat) Literal) :
    Image (lexicalStore cells) ⟨source, ()⟩ result ↔
      Image (lexicalStore cells) ⟨target, ()⟩ result := by
  apply successful_query_preserves_full_image cells fuel source target
  have erased := erase_frames cells fuel source
  simpa [found] using erased.symm

def countdown (value : Term Nat Nat) : CellStore Nat
  | 0 => some value
  | cell + 1 => some (.var cell)

def original : Term Nat Nat := .leaf 7
def replacement : Term Nat Nat := .leaf 11

theorem countdown_answer (cell : Nat) :
    (ReadOnlyQuery.run (countdown original) (query (cell + 2) (.var cell))).answer =
      some original := by
  induction cell with
  | zero => rfl
  | succ cell ih => simpa [query, ReadOnlyQuery.run, countdown] using ih

theorem countdown_reads (cell : Nat) :
    (ReadOnlyQuery.run (countdown original) (query (cell + 2) (.var cell))).reads.length =
      cell + 1 := by
  induction cell with
  | zero => rfl
  | succ cell ih => simpa [query, ReadOnlyQuery.run, countdown] using congrArg Nat.succ ih

theorem changed_countdown_answer (cell key : Nat) (before : key ≤ cell) :
    (ReadOnlyQuery.run (Function.update (countdown original) key (some replacement))
      (query (cell + 2) (.var cell))).answer = some replacement := by
  induction cell with
  | zero =>
    have same : key = 0 := by omega
    subst key
    rfl
  | succ cell ih =>
    by_cases same : key = cell + 1
    · subst key
      simp [query, ReadOnlyQuery.run, replacement]
    · have earlier : key ≤ cell := by omega
      simpa [query, ReadOnlyQuery.run, Function.update, same,
        Ne.symm same, countdown] using ih earlier

theorem must_read_changed_cell
    (reference : CellStore Nat → Option (Term Nat Nat))
    (program : ReadOnlyQuery.Program Nat (Option (Term Nat Nat)) (Option (Term Nat Nat)))
    (correct : ∀ cells, (ReadOnlyQuery.run cells program).answer = reference cells)
    (cells : CellStore Nat) (key : Nat) (new : Option (Term Nat Nat))
    (changed : reference (Function.update cells key new) ≠ reference cells) :
    key ∈ (ReadOnlyQuery.run cells program).reads.map Prod.fst := by
  by_contra absent
  have agree : ReadOnlyQuery.Agrees (Function.update cells key new)
      (ReadOnlyQuery.run cells program).reads := by
    intro observed member
    have different : observed.1 ≠ key := by
      intro same
      apply absent
      exact List.mem_map.mpr ⟨observed, member, same⟩
    have old := ReadOnlyQuery.run_agrees cells program observed member
    simpa [Function.update, different] using old
  have same := congrArg ReadOnlyQuery.Observation.answer
    (ReadOnlyQuery.run_eq_of_agrees cells (Function.update cells key new) program agree)
  rw [correct, correct] at same
  exact changed same

theorem alias_query_lower_bound (cell : Nat)
    (program : ReadOnlyQuery.Program Nat (Option (Term Nat Nat)) (Option (Term Nat Nat)))
    (correct : ∀ cells, (ReadOnlyQuery.run cells program).answer =
      (ReadOnlyQuery.run cells (query (cell + 2) (.var cell))).answer) :
    cell + 1 ≤ (ReadOnlyQuery.run (countdown original) program).reads.length := by
  let keys := (ReadOnlyQuery.run (countdown original) program).reads.map Prod.fst
  have all : ∀ key ∈ Finset.range (cell + 1), key ∈ keys := by
    intro key member
    have before : key ≤ cell := by simpa using member
    apply must_read_changed_cell
      (fun cells => (ReadOnlyQuery.run cells (query (cell + 2) (.var cell))).answer)
      program correct (countdown original) key (some replacement)
    rw [changed_countdown_answer cell key before, countdown_answer]
    simp [original, replacement]
  have included : Finset.range (cell + 1) ⊆ keys.toFinset := by
    intro key member
    simpa using all key member
  calc
    cell + 1 = (Finset.range (cell + 1)).card := (Finset.card_range _).symm
    _ ≤ keys.toFinset.card := Finset.card_le_card included
    _ ≤ keys.length := List.toFinset_card_le keys
    _ = (ReadOnlyQuery.run (countdown original) program).reads.length := List.length_map _

theorem alias_query_optimal (cell : Nat)
    (program : ReadOnlyQuery.Program Nat (Option (Term Nat Nat)) (Option (Term Nat Nat)))
    (correct : ∀ cells, (ReadOnlyQuery.run cells program).answer =
      (ReadOnlyQuery.run cells (query (cell + 2) (.var cell))).answer) :
    (ReadOnlyQuery.run (countdown original) (query (cell + 2) (.var cell))).reads.length ≤
      (ReadOnlyQuery.run (countdown original) program).reads.length := by
  rw [countdown_reads]
  exact alias_query_lower_bound cell program correct

def pendingFrames : Option (Term Nat Nat × List Nat) → Nat
  | none => 0
  | some (_, frames) => frames.length

theorem countdown_pending_frames (cell : Nat) :
    pendingFrames (ReadOnlyQuery.run (countdown original)
      (framedQuery (cell + 2) (.var cell))).answer = cell + 1 := by
  induction cell with
  | zero => rfl
  | succ cell ih =>
    change pendingFrames ((ReadOnlyQuery.run (countdown original)
      (ReadOnlyQuery.map (Option.map fun pair : Term Nat Nat × List Nat =>
        (pair.1, (cell + 1) :: pair.2))
        (framedQuery (cell + 2) (.var cell)))).answer) = cell + 1 + 1
    rw [ReadOnlyQuery.run_map]
    cases found : (ReadOnlyQuery.run (countdown original)
        (framedQuery (cell + 2) (.var cell))).answer with
    | none => simp [found, pendingFrames] at ih
    | some pair =>
      simpa [found, pendingFrames] using congrArg Nat.succ ih

theorem replaced_cell_changes_answer :
    (ReadOnlyQuery.run (countdown original) (query 4 (.var 2))).answer ≠
      (ReadOnlyQuery.run (Function.update (countdown original) 1 (some replacement))
        (query 4 (.var 2))).answer := by
  simp [query, ReadOnlyQuery.run, countdown, original, replacement]

end Mettapedia.Machines.RootPrefixSubstitution
