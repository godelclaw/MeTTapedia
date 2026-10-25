import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Opaque identity during one foreign answer read

The native reader constructs one handle per previously unseen opaque identity,
then reuses it across the answer's bindings, value and delayed goals. Keys
include the owning runtime and receiver arena. The finite map is scoped to one
read; it supplies neither resource ownership nor identity across later answers.

The executable list algorithm appends new entries and uses the first exact key
match. Its logical reference is a functional map. A hit leaves the registration
frontier unchanged; a miss advances it once. Freshness and injective allocation
preserve distinctions between different keys. Publication order and duplicate
occurrences are retained by the batch reader.

Native atom identity, the lifetime supplied by the runtime's recorded term,
arena identity, allocation failure and the registry's later release protocol
remain separate implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ForeignReferenceAliases

structure Key where
  runtime : Nat
  arena : Nat
  foreignAtom : Nat
  deriving DecidableEq, Repr

abbrev Entries := List (Key × Nat)

def find (key : Key) : Entries → Option Nat
  | [] => none
  | (stored, handle) :: rest => if key = stored then some handle else find key rest

theorem find_append (key : Key) (first second : Entries) :
    find key (first ++ second) = (find key first).orElse (fun _ => find key second) := by
  induction first with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨stored, handle⟩
      by_cases same : key = stored <;> simp [find, same, ih]

structure State where
  next : Nat
  entries : Entries
  deriving DecidableEq, Repr

def empty (next : Nat) : State := ⟨next, []⟩

def read (state : State) (key : Key) : Nat × State :=
  match find key state.entries with
  | some handle => (handle, state)
  | none => (state.next, ⟨state.next + 1, state.entries ++ [(key, state.next)]⟩)

/-- Existing registrations are older than the next fresh handle. -/
def Bounded (state : State) : Prop :=
  ∀ key handle, find key state.entries = some handle → handle < state.next

/-- Different opaque keys cannot acquire one native identity. -/
def Injective (state : State) : Prop :=
  ∀ first second handle, find first state.entries = some handle →
    find second state.entries = some handle → first = second

theorem empty_bounded (next : Nat) : Bounded (empty next) := by
  intro key handle impossible
  simp [empty, find] at impossible

theorem empty_injective (next : Nat) : Injective (empty next) := by
  intro first second handle impossible
  simp [empty, find] at impossible

theorem read_hit (state : State) (key : Key) (handle : Nat)
    (present : find key state.entries = some handle) :
    read state key = (handle, state) := by simp [read, present]

theorem read_miss (state : State) (key : Key)
    (absent : find key state.entries = none) :
    read state key = (state.next, ⟨state.next + 1, state.entries ++ [(key, state.next)]⟩) := by
  simp [read, absent]

/-- The private vector update implements a functional map update exactly. -/
theorem read_lookup (state : State) (key query : Key) :
    find query (read state key).2.entries =
      if query = key then some (read state key).1 else find query state.entries := by
  cases present : find key state.entries with
  | some handle =>
      by_cases same : query = key
      · subst query; simp [read, present]
      · simp [read, present, same]
  | none =>
      by_cases same : query = key
      · subst query; simp [read, present, find_append, find]
      · simp [read, present, find_append, find, same]

theorem read_bounded (state : State) (bounded : Bounded state) (key : Key) :
    Bounded (read state key).2 := by
  cases present : find key state.entries with
  | some handle => simpa [read, present] using bounded
  | none =>
      intro query handle found
      by_cases same : query = key
      · subst query
        have handleSame : handle = state.next := by
          simpa [read, present, find_append, find] using found.symm
        simp only [read, present] at *
        omega
      · have old : find query state.entries = some handle := by
          simpa [read_lookup, same] using found
        have smaller := bounded query handle old
        simp only [read, present]
        omega

theorem read_injective (state : State) (bounded : Bounded state)
    (unique : Injective state) (key : Key) : Injective (read state key).2 := by
  cases present : find key state.entries with
  | some handle => simpa [read, present] using unique
  | none =>
      intro first second handle left right
      rw [read_lookup] at left right
      by_cases firstSame : first = key <;> by_cases secondSame : second = key
      · exact firstSame.trans secondSame.symm
      · have fresh : handle = state.next := by
          simpa [firstSame, read, present] using left.symm
        have old : find second state.entries = some handle := by
          simpa [secondSame] using right
        have smaller := bounded second handle old
        omega
      · have fresh : handle = state.next := by
          simpa [secondSame, read, present] using right.symm
        have old : find first state.entries = some handle := by
          simpa [firstSame] using left
        have smaller := bounded first handle old
        omega
      · exact unique first second handle
          (by simpa [firstSame] using left) (by simpa [secondSame] using right)

theorem read_preserves_old (state : State) (key old : Key) (handle : Nat)
    (present : find old state.entries = some handle) :
    find old (read state key).2.entries = some handle := by
  rw [read_lookup]
  by_cases same : old = key
  · subst old; simp [read, present]
  · simp [same, present]

theorem read_returned_registered (state : State) (key : Key) :
    find key (read state key).2.entries = some (read state key).1 := by
  simp [read_lookup]

/-- Reading the same foreign identity twice registers only once. -/
theorem repeated_read (state : State) (key : Key) :
    read (read state key).2 key = ((read state key).1, (read state key).2) :=
  read_hit _ _ _ (read_returned_registered state key)

def readAll : State → List Key → List Nat × State
  | state, [] => ([], state)
  | state, key :: rest =>
      let first := read state key
      let tail := readAll first.2 rest
      (first.1 :: tail.1, tail.2)

theorem readAll_preserves_old (state : State) (keys : List Key)
    (old : Key) (handle : Nat) (present : find old state.entries = some handle) :
    find old (readAll state keys).2.entries = some handle := by
  induction keys generalizing state with
  | nil => exact present
  | cons key rest ih => exact ih _ (read_preserves_old state key old handle present)

theorem readAll_injective (state : State) (keys : List Key)
    (bounded : Bounded state) (unique : Injective state) :
    Injective (readAll state keys).2 := by
  induction keys generalizing state with
  | nil => exact unique
  | cons key rest ih =>
      exact ih _ (read_bounded state bounded key)
        (read_injective state bounded unique key)

/-- The complete ordered output retains one corresponding handle per input,
including duplicate occurrences. Its final map still contains every handle. -/
theorem readAll_corresponds (state : State) (keys : List Key) :
    List.Forall₂ (fun key handle =>
      find key (readAll state keys).2.entries = some handle)
      keys (readAll state keys).1 := by
  induction keys generalizing state with
  | nil => exact .nil
  | cons key rest ih =>
      apply List.Forall₂.cons
      · exact readAll_preserves_old _ rest key (read state key).1
          (read_returned_registered state key)
      · exact ih (read state key).2

/-- An arbitrary occurrence pair agrees exactly when its scoped keys agree. -/
theorem final_lookup_eq_iff (state : State) (bounded : Bounded state)
    (unique : Injective state) (keys : List Key) (first second : Key)
    (leftHandle rightHandle : Nat)
    (left : find first (readAll state keys).2.entries = some leftHandle)
    (right : find second (readAll state keys).2.entries = some rightHandle) :
    leftHandle = rightHandle ↔ first = second := by
  constructor
  · intro same
    subst rightHandle
    exact readAll_injective state keys bounded unique first second leftHandle left right
  · intro same
    subst second
    exact Option.some.inj (left.symm.trans right)

def one : Key := ⟨3, 7, 11⟩
def other : Key := ⟨3, 7, 12⟩

theorem duplicate_occurrences_and_distinct_handles :
    (readAll (empty 20) [one, one, other, one]).1 = [20, 20, 21, 20] ∧
      (readAll (empty 20) [one, one, other, one]).2.next = 22 := by decide

theorem runtime_and_arena_separate_keys :
    (readAll (empty 20) [one, ⟨4, 7, 11⟩, ⟨3, 8, 11⟩]).1 = [20, 21, 22] := by decide

/-- Resetting a map for a later answer does not borrow an earlier image. -/
theorem new_read_starts_fresh :
    (read (empty 20) one).1 = 20 ∧
      (read (empty (read (empty 20) one).2.next) one).1 = 21 := by decide

#print axioms read_lookup
#print axioms read_bounded
#print axioms read_injective
#print axioms repeated_read
#print axioms readAll_preserves_old
#print axioms readAll_injective
#print axioms readAll_corresponds
#print axioms final_lookup_eq_iff
#print axioms duplicate_occurrences_and_distinct_handles
#print axioms runtime_and_arena_separate_keys
#print axioms new_read_starts_fresh

end Mettapedia.Machines.ForeignReferenceAliases
