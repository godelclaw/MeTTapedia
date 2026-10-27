import Mettapedia.Algorithms.Compression.FairSearch

/-!
# Retained distinct evidence samples under bounded cooperative scanning

`none` is an unobserved coordinate. Keys are exact encodings, not approximate
numeric equivalence classes. One tick consumes one coordinate; a scan stops
at the first new answer, completion, or its quantum. The independent remaining
answer stream is preserved across pauses. Every member reaches an emitting
state, and the cost/age queue services it despite arbitrary competing branches.

This is the cursor algorithm over a logical input suffix. Packed observation,
physical cursor validation, scalar decoding and the no-observation default are
separate interfaces, not assumed implementations of these definitions.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.EvidenceSampling

variable {Key : Type} [DecidableEq Key]

structure State (Key : Type) where
  pending : List (Option Key)
  seen : List Key
  deriving DecidableEq, Repr

inductive Tick (Key : Type) where
  | done
  | pending (next : State Key)
  | answer (key : Key) (next : State Key)
  deriving DecidableEq, Repr

def tick : State Key → Tick Key
  | ⟨[], _⟩ => .done
  | ⟨none :: rest, seen⟩ => .pending ⟨rest, seen⟩
  | ⟨some key :: rest, seen⟩ =>
      if key ∈ seen then .pending ⟨rest, seen⟩ else .answer key ⟨rest, key :: seen⟩

def remaining : List (Option Key) → List Key → List Key
  | [], _ => []
  | none :: rest, seen => remaining rest seen
  | some key :: rest, seen =>
      if key ∈ seen then remaining rest seen else key :: remaining rest (key :: seen)

def scan : Nat → State Key → Tick Key
  | 0, state => .pending state
  | fuel + 1, state =>
      match tick state with
      | .pending next => scan fuel next
      | other => other

theorem tick_pending_preserves {before after : State Key} (found : tick before = .pending after) :
    remaining after.pending after.seen = remaining before.pending before.seen := by
  rcases before with ⟨pending, seen⟩
  cases pending with
  | nil => simp [tick] at found
  | cons head rest =>
      cases head with
      | none => cases found; rfl
      | some key =>
          by_cases old : key ∈ seen
          · simp [tick, old] at found
            subst after
            simp [remaining, old]
          · simp [tick, old] at found

theorem tick_answer_preserves {before after : State Key} {key : Key}
    (found : tick before = .answer key after) :
    remaining before.pending before.seen = key :: remaining after.pending after.seen := by
  rcases before with ⟨pending, seen⟩
  cases pending with
  | nil => simp [tick] at found
  | cons head rest =>
      cases head with
      | none => simp [tick] at found
      | some first =>
          by_cases old : first ∈ seen
          · simp [tick, old] at found
          · simp [tick, old] at found
            obtain ⟨rfl, rfl⟩ := found
            simp [remaining, old]

def Accounts (before : State Key) : Tick Key → Prop
  | .done => remaining before.pending before.seen = []
  | .pending after => remaining before.pending before.seen = remaining after.pending after.seen
  | .answer key after => remaining before.pending before.seen = key :: remaining after.pending after.seen

theorem scan_accounts (fuel : Nat) (state : State Key) : Accounts state (scan fuel state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases found : tick state with
      | done =>
          cases state with
          | mk pending seen =>
              cases pending with
              | nil => simp [scan, tick, Accounts, remaining]
              | cons head rest =>
                  cases head with
                  | none => simp [tick] at found
                  | some key =>
                      by_cases old : key ∈ seen <;> simp [tick, old] at found
      | answer key after =>
          simpa [scan, found, Accounts] using tick_answer_preserves found
      | pending after =>
          have same := tick_pending_preserves found
          have later := ih after
          cases next : scan fuel after <;> simpa [scan, found, next, Accounts, ← same] using later

def successors (state : State Key) : List (State Key) :=
  match tick state with
  | .done => []
  | .pending next => [next]
  | .answer _ next => [next]

def emit (state : State Key) : Option Key :=
  match tick state with
  | .answer key _ => some key
  | _ => none

theorem remaining_reachable (pending : List (Option Key)) (seen : List Key) (key : Key)
    (present : key ∈ remaining pending seen) :
    ∃ target, Relation.ReflTransGen (fun before after : State Key => after ∈ successors before)
      ⟨pending, seen⟩ target ∧ emit target = some key := by
  induction pending generalizing seen with
  | nil => simp [remaining] at present
  | cons head rest ih =>
      cases head with
      | none =>
          obtain ⟨target, path, emits⟩ := ih seen present
          exact ⟨target, (Relation.ReflTransGen.single (by simp [successors, tick])).trans path, emits⟩
      | some first =>
          by_cases old : first ∈ seen
          · simp [remaining, old] at present
            obtain ⟨target, path, emits⟩ := ih seen present
            exact ⟨target, (Relation.ReflTransGen.single (by simp [successors, tick, old])).trans path, emits⟩
          · simp only [remaining, old, ↓reduceIte, List.mem_cons] at present
            rcases present with rfl | later
            · exact ⟨⟨some key :: rest, seen⟩, .refl, by simp [emit, tick, old]⟩
            · obtain ⟨target, path, emits⟩ := ih (first :: seen) later
              exact ⟨target, (Relation.ReflTransGen.single (by simp [successors, tick, old])).trans path, emits⟩

def mixedSuccessors {Noise : Type} (other : Noise → List (Sum Noise (State Key))) :
    Sum Noise (State Key) → List (Sum Noise (State Key))
  | .inl noise => other noise
  | .inr state => (successors state).map Sum.inr

theorem eventually_services_sample {Noise : Type}
    (other : Noise → List (Sum Noise (State Key)))
    (priority : Sum Noise (State Key) → Nat) (queue : FairQueue.Queue (Sum Noise (State Key)))
    (valid : FairQueue.Valid queue) (pending : List (Option Key)) (seen : List Key)
    (root : Sum.inr (State.mk pending seen) ∈ queue.pending.map FairQueue.Entry.value)
    (key : Key) (present : key ∈ remaining pending seen) :
    ∃ fuel target, Sum.inr target ∈
      (FairQueue.run priority (mixedSuccessors other) fuel queue).1.map FairQueue.Entry.value ∧
        emit target = some key := by
  obtain ⟨target, path, emits⟩ := remaining_reachable pending seen key present
  have lifted : Relation.ReflTransGen
      (fun before after : Sum Noise (State Key) => after ∈ mixedSuccessors other before)
      (.inr ⟨pending, seen⟩) (.inr target) := by
    clear emits
    induction path with
    | refl => exact .refl
    | tail _ edge ih => exact .tail ih (List.mem_map.mpr ⟨_, edge, rfl⟩)
  obtain ⟨fuel, serviced⟩ := FairQueue.services_reachable priority (mixedSuccessors other)
    queue valid root lifted
  exact ⟨fuel, target, serviced, emits⟩

namespace Controls

theorem samples_after_masked_and_duplicate_positions_survive :
    remaining [none, some 3, some 3, none, some 7] [] = [3, 7] := by decide

theorem budget_stop_keeps_later_answer :
    scan 1 (⟨[none, some 7], []⟩ : State Nat) = .pending ⟨[some 7], []⟩ := by decide

theorem later_quantum_yields_retained_answer :
    scan 1 (⟨[some 7], []⟩ : State Nat) = .answer 7 ⟨[], [7]⟩ := by decide

end Controls

end Mettapedia.Algorithms.Compression.EvidenceSampling
