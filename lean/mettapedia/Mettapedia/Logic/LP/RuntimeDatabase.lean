import Mettapedia.Logic.LP.Core

/-!
# Persistent logical-update database for the canonical LP runtime

This is the clause-store component that will replace the fixed program carried
by a resumable runtime session.  It is not a resolver: calls still enter the
single `RuntimeQuery` machine, whose clause cursor freezes the source-ordered
visible clause list at predicate entry.

The visibility interval follows SWI-Prolog's logical-update rule: a clause is
visible at generation `g` exactly when `born ≤ g < died`, with no upper bound
for a live clause.  Assertions and erasures advance one persistent generation.
Clause references are stable natural-number identities and are never reused.

Transactions and physical clause reclamation are intentionally absent here.
They are separate mechanisms and must not be smuggled into the basic logical-
update model.
-/

namespace Mettapedia.Logic.LP.RuntimeDatabase

abbrev Generation := Nat
abbrev ClauseRef := Nat

/-- One source clause with a stable reference and logical lifetime. -/
structure Entry (Payload : Type*) where
  reference : ClauseRef
  clause : Payload
  born : Generation
  died : Option Generation := none
deriving Repr

namespace Entry

/-- SWI's `created ≤ generation < erased` visibility test. -/
def VisibleAt (entry : Entry Payload) (generation : Generation) : Prop :=
  entry.born ≤ generation ∧
    ∀ death, entry.died = some death → generation < death

instance (entry : Entry Payload) (generation : Generation) :
    Decidable (entry.VisibleAt generation) := by
  unfold VisibleAt
  infer_instance

/-- Mark one currently visible entry dead at a strictly later generation. -/
def eraseAt (entry : Entry Payload) (death : Generation) : Entry Payload :=
  { entry with died := some death }

@[simp]
theorem visibleAt_live_iff (entry : Entry Payload)
    (generation : Generation) (hLive : entry.died = none) :
    entry.VisibleAt generation ↔ entry.born ≤ generation := by
  simp [VisibleAt, hLive]

@[simp]
theorem visibleAt_eraseAt_iff (entry : Entry Payload)
    (generation death : Generation) :
    (entry.eraseAt death).VisibleAt generation ↔
      entry.born ≤ generation ∧ generation < death := by
  simp [VisibleAt, eraseAt]

/-- Erasing at the successor generation preserves visibility in the old
snapshot. -/
theorem eraseAt_visible_previous (entry : Entry Payload)
    (generation : Generation) (hVisible : entry.VisibleAt generation) :
    (entry.eraseAt (generation + 1)).VisibleAt generation := by
  simp only [visibleAt_eraseAt_iff]
  exact ⟨hVisible.1, Nat.lt_succ_self generation⟩

/-- The erased clause is absent from the new generation. -/
theorem eraseAt_not_visible_current (entry : Entry Payload)
    (generation : Generation) :
    ¬(entry.eraseAt (generation + 1)).VisibleAt (generation + 1) := by
  simp [VisibleAt, eraseAt]

end Entry

/-- Persistent source-ordered clause database.  `nextRef` is a high-water,
not a backtrackable allocation cursor. -/
structure Database (Payload : Type*) where
  generation : Generation := 0
  nextRef : ClauseRef := 0
  entries : List (Entry Payload) := []
deriving Repr

namespace Database

private def seedEntries : ClauseRef → List Payload → List (Entry Payload)
  | _, [] => []
  | reference, clause :: rest =>
      { reference, clause, born := 0 } :: seedEntries (reference + 1) rest

/-- Turn a source-ordered static program into generation-zero database
content while preserving order and multiplicity. -/
def ofProgram (program : List Payload) : Database Payload := {
  generation := 0
  nextRef := program.length
  entries := seedEntries 0 program
}

private def visibleClausesIn : List (Entry Payload) → Generation →
    List (ClauseRef × Payload)
  | [], _ => []
  | entry :: rest, generation =>
      if entry.VisibleAt generation then
        (entry.reference, entry.clause) ::
          visibleClausesIn rest generation
      else
        visibleClausesIn rest generation

private theorem visibleClausesIn_append (left right : List (Entry Payload))
    (generation : Generation) :
    visibleClausesIn (left ++ right) generation =
      visibleClausesIn left generation ++ visibleClausesIn right generation := by
  induction left with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      by_cases hVisible : entry.VisibleAt generation <;>
        simp [visibleClausesIn, hVisible, inductionHypothesis]

private theorem visibleClausesIn_seedEntries_values (reference : ClauseRef)
    (program : List Payload) :
    (visibleClausesIn (seedEntries reference program) 0).map Prod.snd =
      program := by
  induction program generalizing reference with
  | nil => rfl
  | cons clause rest inductionHypothesis =>
      simp [seedEntries, visibleClausesIn, Entry.VisibleAt,
        inductionHypothesis]

/-- Stable references and clauses visible at one snapshot. -/
def visibleClausesAt (database : Database Payload)
    (generation : Generation) : List (ClauseRef × Payload) :=
  visibleClausesIn database.entries generation

/-- Clauses visible to a call opened now. -/
def visibleClauses (database : Database Payload) : List (ClauseRef × Payload) :=
  database.visibleClausesAt database.generation

/-- Generation-zero installation exposes exactly the original program values
in source order.  Stable references add identity without translating clauses. -/
@[simp]
theorem ofProgram_visibleClause_values (program : List Payload) :
    ((ofProgram program).visibleClauses.map Prod.snd) = program := by
  exact visibleClausesIn_seedEntries_values 0 program

/-- Immutable call-start view.  Runtime clause cursors consume its `clauses`
field by value, so later database updates cannot drift an open call. -/
structure Snapshot (Payload : Type*) where
  generation : Generation
  clauses : List (ClauseRef × Payload)
deriving Repr

def snapshot (database : Database Payload) : Snapshot Payload := {
  generation := database.generation
  clauses := database.visibleClauses
}

private def insertedEntry (database : Database Payload)
    (clause : Payload) : Entry Payload := {
  reference := database.nextRef
  clause
  born := database.generation + 1
}

/-- Insert before all existing source occurrences. -/
def asserta (database : Database Payload) (clause : Payload) :
    ClauseRef × Database Payload :=
  (database.nextRef, {
    generation := database.generation + 1
    nextRef := database.nextRef + 1
    entries := database.insertedEntry clause :: database.entries
  })

/-- Insert after all existing source occurrences. -/
def assertz (database : Database Payload) (clause : Payload) :
    ClauseRef × Database Payload :=
  (database.nextRef, {
    generation := database.generation + 1
    nextRef := database.nextRef + 1
    entries := database.entries ++ [database.insertedEntry clause]
  })

private def eraseFirst (reference : ClauseRef) (generation : Generation) :
    List (Entry Payload) → Option (Payload × List (Entry Payload))
  | [] => none
  | entry :: rest =>
      if entry.reference = reference ∧ entry.VisibleAt generation then
        some (entry.clause, entry.eraseAt (generation + 1) :: rest)
      else
        match eraseFirst reference generation rest with
        | none => none
        | some (clause, updated) => some (clause, entry :: updated)

private theorem eraseFirst_preserves_previous
    {reference : ClauseRef} {generation : Generation}
    {entries updated : List (Entry Payload)} {clause : Payload}
    (hErase : eraseFirst reference generation entries =
      some (clause, updated)) :
    visibleClausesIn updated generation =
      visibleClausesIn entries generation := by
  induction entries generalizing updated clause with
  | nil => simp [eraseFirst] at hErase
  | cons entry rest inductionHypothesis =>
      unfold eraseFirst at hErase
      by_cases hTarget :
          entry.reference = reference ∧ entry.VisibleAt generation
      · simp [hTarget] at hErase
        rcases hErase with ⟨rfl, rfl⟩
        have hStillVisible :=
          Entry.eraseAt_visible_previous entry generation hTarget.2
        rw [visibleClausesIn, if_pos hStillVisible]
        rw [visibleClausesIn, if_pos hTarget.2]
        rfl
      · simp [hTarget] at hErase
        cases hRest : eraseFirst reference generation rest with
        | none => simp [hRest] at hErase
        | some result =>
            obtain ⟨erasedClause, updatedRest⟩ := result
            simp [hRest] at hErase
            rcases hErase with ⟨rfl, rfl⟩
            simpa [visibleClausesIn] using
              congrArg
                (fun tail =>
                  if entry.VisibleAt generation then
                    (entry.reference, entry.clause) :: tail
                  else tail)
                (inductionHypothesis hRest)

/-- Erase the first currently visible occurrence with this stable reference.
Failure is observationally pure and does not burn a generation. -/
def eraseRef (database : Database Payload) (reference : ClauseRef) :
    Option (Payload × Database Payload) :=
  match eraseFirst reference database.generation database.entries with
  | none => none
  | some (clause, entries) =>
      some (clause, {
        generation := database.generation + 1
        nextRef := database.nextRef
        entries
      })

@[simp]
theorem asserta_reference (database : Database Payload) (clause : Payload) :
    (database.asserta clause).1 = database.nextRef := rfl

@[simp]
theorem assertz_reference (database : Database Payload) (clause : Payload) :
    (database.assertz clause).1 = database.nextRef := rfl

@[simp]
theorem asserta_generation (database : Database Payload) (clause : Payload) :
    (database.asserta clause).2.generation = database.generation + 1 := rfl

@[simp]
theorem assertz_generation (database : Database Payload) (clause : Payload) :
    (database.assertz clause).2.generation = database.generation + 1 := rfl

@[simp]
theorem asserta_nextRef (database : Database Payload) (clause : Payload) :
    (database.asserta clause).2.nextRef = database.nextRef + 1 := rfl

@[simp]
theorem assertz_nextRef (database : Database Payload) (clause : Payload) :
    (database.assertz clause).2.nextRef = database.nextRef + 1 := rfl

/-- A newly asserted clause is not retroactively visible in the call-start
generation immediately preceding it. -/
@[simp]
theorem insertedEntry_not_visible_previous (database : Database Payload)
    (clause : Payload) :
    ¬(database.insertedEntry clause).VisibleAt database.generation := by
  simp [insertedEntry, Entry.VisibleAt]

/-- A newly asserted clause is visible in the generation created by the
assertion. -/
@[simp]
theorem insertedEntry_visible_current (database : Database Payload)
    (clause : Payload) :
    (database.insertedEntry clause).VisibleAt
      (database.generation + 1) := by
  simp [insertedEntry, Entry.VisibleAt]

/-- `asserta/1` cannot change an already-open call snapshot. -/
@[simp]
theorem visibleClausesAt_asserta_previous (database : Database Payload)
    (clause : Payload) :
    (database.asserta clause).2.visibleClausesAt database.generation =
      database.visibleClausesAt database.generation := by
  simp [asserta, visibleClausesAt, insertedEntry,
    visibleClausesIn, Entry.VisibleAt]

/-- `assertz/1` cannot change an already-open call snapshot. -/
@[simp]
theorem visibleClausesAt_assertz_previous (database : Database Payload)
    (clause : Payload) :
    (database.assertz clause).2.visibleClausesAt database.generation =
      database.visibleClausesAt database.generation := by
  simp [assertz, visibleClausesAt, insertedEntry,
    visibleClausesIn_append, visibleClausesIn, Entry.VisibleAt]

/-- At the new generation, `asserta/1` places its occurrence first. -/
@[simp]
theorem visibleClausesAt_asserta_current (database : Database Payload)
    (clause : Payload) :
    (database.asserta clause).2.visibleClausesAt (database.generation + 1) =
      (database.nextRef, clause) ::
        database.visibleClausesAt (database.generation + 1) := by
  simp [asserta, visibleClausesAt, insertedEntry,
    visibleClausesIn, Entry.VisibleAt]

/-- At the new generation, `assertz/1` places its occurrence last. -/
@[simp]
theorem visibleClausesAt_assertz_current (database : Database Payload)
    (clause : Payload) :
    (database.assertz clause).2.visibleClausesAt (database.generation + 1) =
      database.visibleClausesAt (database.generation + 1) ++
        [(database.nextRef, clause)] := by
  simp [assertz, visibleClausesAt, insertedEntry,
    visibleClausesIn_append, visibleClausesIn, Entry.VisibleAt]

/-- Every successful erasure advances exactly one persistent generation. -/
theorem eraseRef_generation {database updated : Database Payload}
    {reference : ClauseRef} {clause : Payload}
    (hErase : database.eraseRef reference = some (clause, updated)) :
    updated.generation = database.generation + 1 := by
  unfold eraseRef at hErase
  cases hResult : eraseFirst reference database.generation database.entries with
  | none => simp [hResult] at hErase
  | some result =>
      obtain ⟨erasedClause, entries⟩ := result
      simp [hResult] at hErase
      rcases hErase with ⟨rfl, rfl⟩
      rfl

/-- Retraction cannot change the frozen view of a call that opened in the
immediately preceding generation. -/
theorem eraseRef_preserves_previous {database updated : Database Payload}
    {reference : ClauseRef} {clause : Payload}
    (hErase : database.eraseRef reference = some (clause, updated)) :
    updated.visibleClausesAt database.generation =
      database.visibleClausesAt database.generation := by
  unfold eraseRef at hErase
  cases hResult : eraseFirst reference database.generation database.entries with
  | none => simp [hResult] at hErase
  | some result =>
      obtain ⟨erasedClause, entries⟩ := result
      simp [hResult] at hErase
      rcases hErase with ⟨rfl, rfl⟩
      exact eraseFirst_preserves_previous hResult

/-- Erasure never recycles clause-reference identities. -/
theorem eraseRef_nextRef {database updated : Database Payload}
    {reference : ClauseRef} {clause : Payload}
    (hErase : database.eraseRef reference = some (clause, updated)) :
    updated.nextRef = database.nextRef := by
  unfold eraseRef at hErase
  cases hResult : eraseFirst reference database.generation database.entries with
  | none => simp [hResult] at hErase
  | some result =>
      obtain ⟨erasedClause, entries⟩ := result
      simp [hResult] at hErase
      rcases hErase with ⟨rfl, rfl⟩
      rfl

end Database

end Mettapedia.Logic.LP.RuntimeDatabase
