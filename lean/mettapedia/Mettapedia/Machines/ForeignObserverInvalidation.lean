import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Effect-scoped foreign invalidation

A foreign call still executes its original program. Only capability invalidation
changes: a checked read-only program that fails without an exception can retain
the current stamp. Reads and writes have an independent interpreter below;
failure alone does not imply purity. Cached answers are justified by the store
and their capability stamp, rather than by the spelling of a foreign predicate.

The native adapter must establish that its current predicate and wrapper
implement the admitted program, and that no inherited goal adds effects.
Those SWI/C conformance obligations are not assumptions disguised as proofs
about the full implementation. The cost below counts invalidation events,
not elapsed time, allocations, or predicate execution work.

The architectural comparison outside Prolog is rustc's pure query dependency
tracking: https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation-in-detail.html
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ForeignObserverInvalidation

abbrev Store := Nat → Nat

inductive Op where
  | probe (key : Nat)
  | write (key value : Nat)
  | reject
  deriving DecidableEq

structure Execution where
  store : Store
  answers : List Nat
  failed : Bool

def run : List Op → Store → Execution
  | [], store => ⟨store, [], false⟩
  | .reject :: _, store => ⟨store, [], true⟩
  | .write key value :: rest, store =>
      run rest (Function.update store key value)
  | .probe key :: rest, store =>
      if store key = 0 then ⟨store, [], true⟩
      else
        let next := run rest store
        ⟨next.store, store key :: next.answers, next.failed⟩

def readOnly : List Op → Bool
  | [] => true
  | .write _ _ :: _ => false
  | _ :: rest => readOnly rest

theorem readOnly_store (code : List Op) (store : Store)
    (admitted : readOnly code = true) : (run code store).store = store := by
  induction code generalizing store with
  | nil => rfl
  | cons op rest ih =>
      cases op with
      | reject => rfl
      | write key value => simp [readOnly] at admitted
      | probe key =>
          simp only [readOnly] at admitted
          simp only [run]
          split
          · rfl
          · exact ih store admitted

structure Entry where
  revision : Nat
  key : Nat
  value : Nat

structure State where
  store : Store
  revision : Nat
  cache : Option Entry

def Sound (state : State) : Prop :=
  ∀ entry, state.cache = some entry →
    entry.revision ≤ state.revision ∧
      (entry.revision = state.revision → entry.value = state.store entry.key)

def query (key : Nat) (state : State) : Nat × Nat :=
  match state.cache with
  | some entry =>
      if entry.revision = state.revision ∧ entry.key = key then (entry.value, 0)
      else (state.store key, 1)
  | none => (state.store key, 1)

theorem query_exact (state : State) (sound : Sound state) (key : Nat) :
    (query key state).1 = state.store key := by
  unfold query
  split
  · rename_i entry found
    split
    · rename_i current
      simpa [current.2] using (sound entry found).2 current.1
    · rfl
  · rfl

def foreign (precise : Bool) (code : List Op) (state : State) : State × Nat :=
  let result := run code state.store
  if precise && readOnly code && result.failed then
    ({ state with store := result.store }, 0)
  else
    ({ state with store := result.store, revision := state.revision + 1 }, 1)

theorem foreign_sound (precise : Bool) (code : List Op) (state : State)
    (sound : Sound state) : Sound (foreign precise code state).1 := by
  unfold foreign
  dsimp only
  split
  · rename_i admitted
    have pure : readOnly code = true := by simp_all
    simpa [readOnly_store code state.store pure] using sound
  · intro entry found
    have old := sound entry found
    exact ⟨by dsimp; omega, by dsimp; omega⟩

theorem foreign_store_exact (code : List Op) (state : State) :
    (foreign true code state).1.store = (foreign false code state).1.store := by
  simp only [foreign, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  split <;> rfl

/-- A subsequent cached read is exact after either invalidation policy. -/
theorem query_after_foreign_exact (code : List Op) (state : State)
    (sound : Sound state) (key : Nat) :
    (query key (foreign true code state).1).1 =
      (query key (foreign false code state).1).1 := by
  rw [query_exact _ (foreign_sound true code state sound),
      query_exact _ (foreign_sound false code state sound), foreign_store_exact]

def executeMany (precise : Bool) : List (List Op) → State → State × Nat
  | [], state => (state, 0)
  | code :: rest, state =>
      let step := foreign precise code state
      let next := executeMany precise rest step.1
      (next.1, step.2 + next.2)

theorem executeMany_sound (precise : Bool) (codes : List (List Op))
    (state : State) (sound : Sound state) :
    Sound (executeMany precise codes state).1 := by
  induction codes generalizing state with
  | nil => exact sound
  | cons code rest ih =>
      exact ih _ (foreign_sound precise code state sound)

theorem failed_probe_retains_state (state : State) (key : Nat)
    (fails : state.store key = 0) : foreign true [.probe key] state = (state, 0) := by
  simp [foreign, readOnly, run, fails]

theorem repeated_failed_probe (state : State) (key count : Nat)
    (fails : state.store key = 0) :
    executeMany true (List.replicate count [.probe key]) state = (state, 0) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, executeMany,
        failed_probe_retains_state state key fails]
      simpa using ih

/-- A warmed answer remains a cache hit across every admitted observation. -/
theorem repeated_failed_probe_cache_hit (state : State) (entry : Entry)
    (present : state.cache = some entry) (current : entry.revision = state.revision)
    (key count : Nat) (sameKey : entry.key = key) (fails : state.store key = 0) :
    (query key (executeMany true (List.replicate count [.probe key]) state).1).2 = 0 := by
  rw [repeated_failed_probe state key count fails]
  simp [query, present, current, sameKey]

/-- The conservative boundary pays one invalidation per call. -/
theorem conservative_invalidations (codes : List (List Op)) (state : State) :
    (executeMany false codes state).2 = codes.length := by
  induction codes generalizing state with
  | nil => rfl
  | cons code rest ih =>
      simp [executeMany, foreign, ih, Nat.add_comm]

/-- Failure can follow a visible write; it grants no purity authority. -/
theorem write_then_fail_changes_store (store : Store) (key value : Nat)
    (different : value ≠ store key) :
    (run [.write key value, .reject] store).failed = true ∧
      (run [.write key value, .reject] store).store key ≠ store key ∧
      readOnly [.write key value, .reject] = false := by
  simp [run, readOnly, different]

theorem written_failure_invalidates (state : State) (key value : Nat) :
    (foreign true [.write key value, .reject] state).2 = 1 := by
  simp [foreign, readOnly]

/-- A previously cached answer must be refreshed after a write followed by failure. -/
example :
    query 7 (foreign true [.write 7 9, .reject]
      ⟨fun _ => 0, 0, some ⟨0, 7, 0⟩⟩).1 = (9, 1) := by
  simp [query, foreign, readOnly, run]

end Mettapedia.Machines.ForeignObserverInvalidation
