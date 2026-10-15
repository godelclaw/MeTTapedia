import Mettapedia.Machines.ProducerReadCapture

/-!+# Inline and spilled producer-read certificates

The storage transition distinguishes a first read, a repeated key and a second
distinct key. A failed spill preserves the earlier storage and refuses reuse.
Hash entries are represented by an association list; probing, native byte
layout and allocation are separate implementation obligations. The capacity
transition accounts for retained spare slots across rounds.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProducerReadStorage

open ReadOnlyQuery ProducerReadCapture

universe u
variable {Key : Type u} [DecidableEq Key]

inductive Storage (Key : Type u) where
  | inline (read : Option (Key × Nat))
  | hash (capacity : Nat) (reads : Reads Key Nat)
  deriving DecidableEq

def entries : Storage Key → Reads Key Nat
  | .inline none => []
  | .inline (some read) => [read]
  | .hash _ reads => reads

def slots : Storage Key → Nat
  | .inline _ => 0
  | .hash capacity _ => capacity

/-- The allocator result is consulted only when storage must grow. Failure
keeps the previous storage but makes its certificate unusable. -/
def recordStorage (allocated : Bool) (read : Key × Nat) :
    Storage Key → Storage Key × Bool
  | .inline none => (.inline (some read), true)
  | .inline (some old) =>
      if old.1 = read.1 then (.inline (some old), decide (old.2 = read.2))
      else if allocated then (.hash 16 [read, old], true)
      else (.inline (some old), false)
  | .hash capacity reads =>
      match lookup read.1 reads with
      | some old => (.hash capacity reads, decide (old = read.2))
      | none =>
          if reads.length = capacity / 2 then
            if allocated then (.hash (2 * capacity) (read :: reads), true)
            else (.hash capacity reads, false)
          else (.hash capacity (read :: reads), true)

def validates (store : Key → Nat) (state : Storage Key × Bool) : Bool :=
  state.2 && checkReads store (entries state.1)

/-- The inline implementation and the independent first-read specification
validate the same complete trace when the required allocation succeeds. -/
theorem record_check_exact (store : Key → Nat) (read : Key × Nat)
    (storage : Storage Key) :
    validates store (recordStorage true read storage) =
      (checkReads store (entries storage) && decide (store read.1 = read.2)) := by
  cases storage with
  | inline old =>
      cases old with
      | none => simp [recordStorage, validates, entries, checkReads]
      | some old =>
          have exactCheck := remember_check_exact store [old] read
          by_cases same : old.1 = read.1
          · by_cases equal : old.2 = read.2
            · simpa [recordStorage, validates, entries, remember, lookup, same,
                equal, checked] using exactCheck
            · simpa [recordStorage, validates, entries, remember, lookup, same,
                equal, checked] using exactCheck
          · simpa [recordStorage, validates, entries, remember, lookup, same,
              checked, checkReads] using exactCheck
  | hash capacity reads =>
      have exactCheck := remember_check_exact store reads read
      cases found : lookup read.1 reads with
      | none =>
          by_cases full : reads.length = capacity / 2
          · simpa [recordStorage, validates, entries, found, full,
              remember, checked] using exactCheck
          · simpa [recordStorage, validates, entries, found, full,
              remember, checked] using exactCheck
      | some old =>
          by_cases equal : old = read.2
          · simpa [recordStorage, validates, entries, found, equal,
              remember, checked] using exactCheck
          · simpa [recordStorage, validates, entries, found, equal,
              remember, checked] using exactCheck

/-- A failed allocation can refuse reuse; it cannot certify an omitted read. -/
theorem record_check_sound (store : Key → Nat) (read : Key × Nat)
    (allocated : Bool) (storage : Storage Key)
    (accepted : validates store (recordStorage allocated read storage) = true) :
    checkReads store (entries storage) = true ∧ store read.1 = read.2 := by
  have success : validates store (recordStorage true read storage) = true := by
    cases allocated with
    | true => exact accepted
    | false =>
        cases storage with
        | inline old =>
            cases old with
            | none => exact accepted
            | some old =>
                by_cases same : old.1 = read.1
                · simpa [recordStorage, same] using accepted
                · simp [recordStorage, validates, same] at accepted
        | hash capacity reads =>
            cases found : lookup read.1 reads with
            | some old => simpa [recordStorage, found] using accepted
            | none =>
                by_cases full : reads.length = capacity / 2
                · simp [recordStorage, validates, found, full] at accepted
                · simpa [recordStorage, found, full] using accepted
  rw [record_check_exact] at success
  simpa using success

def begin : Storage Key → Storage Key
  | .inline _ => .inline none
  | .hash capacity _ => .hash capacity []

omit [DecidableEq Key] in
theorem begin_empty (storage : Storage Key) : entries (begin storage) = [] := by
  cases storage <;> rfl

omit [DecidableEq Key] in
theorem begin_retains_capacity (storage : Storage Key) :
    slots (begin storage) = slots storage := by
  cases storage <;> rfl

theorem first_read_no_allocation (read : Key × Nat) (allocated : Bool) :
    recordStorage allocated read (.inline none) = (.inline (some read), true) := rfl

theorem repeated_key_no_allocation (key : Key) (first later : Nat)
    (allocated : Bool) :
    (recordStorage allocated (key, later) (.inline (some (key, first)))).1 =
      .inline (some (key, first)) := by
  simp [recordStorage]

theorem second_distinct_read_preserves_both (old read : Key × Nat)
    (distinct : old.1 ≠ read.1) :
    recordStorage true read (.inline (some old)) = (.hash 16 [read, old], true) := by
  simp [recordStorage, distinct]

theorem failed_spill_retains_first (old read : Key × Nat)
    (distinct : old.1 ≠ read.1) :
    recordStorage false read (.inline (some old)) = (.inline (some old), false) := by
  simp [recordStorage, distinct]

omit [DecidableEq Key] in
theorem unrelated_change_preserves_inline (store other : Key → Nat) (read : Key × Nat)
    (unchanged : other read.1 = store read.1) :
    validates other (.inline (some read), true) =
      validates store (.inline (some read), true) := by
  simp [validates, entries, checkReads, unchanged]

theorem spill_omission_is_unsound :
    validates (fun _ : Nat => 0) (.hash 16 [(1, 0)], true) = true ∧
    validates (fun _ : Nat => 0) (recordStorage true (1, 0) (.inline (some (0, 1)))) =
      false := by
  decide

theorem mixed_inline_revision_is_refused (store : Nat → Nat) :
    validates store (recordStorage true (0, 1) (.inline (some (0, 0)))) = false := by
  simp [recordStorage, validates]

/-- Capacity is charged to the largest read set retained by this frame,
including spare slots kept when a new round starts. -/
def WellSized (highWater : Nat) (storage : Storage Key) : Prop :=
  (entries storage).length ≤ highWater ∧
    slots storage ≤ max 16 (4 * highWater) ∧
    match storage with
    | .inline _ => slots storage = 0
    | .hash capacity reads => 16 ≤ capacity ∧ reads.length ≤ capacity / 2

theorem record_retention_bound (allocated : Bool) (read : Key × Nat)
    (storage : Storage Key) (highWater : Nat) (sized : WellSized highWater storage) :
    let next := (recordStorage allocated read storage).1
    WellSized (max highWater (entries next).length) next := by
  cases storage with
  | inline old =>
      cases old with
      | none => simp [recordStorage, WellSized, entries, slots]
      | some old =>
          by_cases same : old.1 = read.1
          · simp_all [recordStorage, WellSized, entries, slots]
          · cases allocated <;> simp_all [recordStorage, WellSized, entries, slots]
  | hash capacity reads =>
      cases found : lookup read.1 reads with
      | some old =>
          simp_all [recordStorage, WellSized, entries, slots]
      | none =>
          by_cases full : reads.length = capacity / 2
          · cases allocated <;> simp_all [recordStorage, WellSized, entries, slots]
            all_goals omega
          · simp_all [recordStorage, WellSized, entries, slots]
            omega

omit [DecidableEq Key] in
theorem begin_retention_bound (storage : Storage Key) (highWater : Nat)
    (sized : WellSized highWater storage) : WellSized highWater (begin storage) := by
  cases storage <;> simp_all [WellSized, entries, slots, begin]

omit [DecidableEq Key] in
theorem active_buffer_slots_bound (frames : List (Nat × Storage Key))
    (sized : ∀ frame ∈ frames, WellSized frame.1 frame.2) :
    (frames.map fun frame => slots frame.2).sum ≤
      16 * frames.length + 4 * (frames.map Prod.fst).sum := by
  induction frames with
  | nil => simp
  | cons frame rest ih =>
      have here := (sized frame (by simp)).2.1
      have tail := ih (fun item member => sized item (by simp [member]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

end Mettapedia.Machines.ProducerReadStorage
