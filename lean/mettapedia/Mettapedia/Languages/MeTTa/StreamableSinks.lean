import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Union

/-!
# Sinks that stream and sinks that need the whole batch

A firing over a set of match rows writes what its sinks make of the rows. A sink is **streamable** when it writes
each row's contribution on its own (`Streamable`): the rows can then be written as they are found, in any order,
by any number of workers.

* **Streamable is exactly union-preserving** (`streamable_iff`): a sink streams exactly when it writes nothing
  for no rows and the writes of a union of row sets are the union of their writes. Such a sink is monotone
  (`Streamable.mono`), and splitting the rows among workers in any way gives the same writes
  (`Streamable.split`).
* **Insertion of a template instance per row streams** (`image_streamable`).
* **An aggregate that is not monotone needs the whole batch.** A guarded count, which writes its template when
  the number of rows equals a given number, writes something for a partial batch that the complete batch does not
  write (`countGuard_not_monotone`); so it does not stream (`countGuard_not_streamable`). A plain count and a
  least-element sink do not stream either (`count_not_streamable`, `least_not_monotone`). Such sinks wait for
  the complete batch: they are finalized once, after every row is staged, as aggregation is stratified in
  Datalog.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.StreamableSinks

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

/-- **A batch sink**: what a firing writes, as a function of its set of match rows. -/
abbrev BatchSink (α : Type u) (β : Type v) := Finset α → Finset β

/-- **A streamable sink** writes each row's contribution on its own. -/
def Streamable (sink : BatchSink α β) : Prop :=
  ∃ contribution : α → Finset β, ∀ rows, sink rows = rows.biUnion contribution

/-- **Streamable is exactly union-preserving.** -/
theorem streamable_iff (sink : BatchSink α β) :
    Streamable sink ↔ sink ∅ = ∅ ∧ ∀ A B, sink (A ∪ B) = sink A ∪ sink B := by
  constructor
  · rintro ⟨contribution, writes⟩
    refine ⟨by rw [writes, Finset.biUnion_empty], fun A B => ?_⟩
    rw [writes, writes, writes, Finset.union_biUnion]
  · rintro ⟨empty, union⟩
    refine ⟨fun a => sink {a}, fun rows => ?_⟩
    induction rows using Finset.induction_on with
    | empty => rw [Finset.biUnion_empty, empty]
    | insert a rows _ ih =>
        rw [Finset.insert_eq, union, ih, Finset.union_biUnion, Finset.singleton_biUnion]

omit [DecidableEq α] in
/-- A streamable sink is monotone: more rows never write less. -/
theorem Streamable.mono {sink : BatchSink α β} (streams : Streamable sink) {A B : Finset α}
    (sub : A ⊆ B) : sink A ⊆ sink B := by
  obtain ⟨contribution, writes⟩ := streams
  rw [writes, writes]
  exact Finset.biUnion_subset_biUnion_of_subset_left _ sub

/-- **Splitting the rows among workers in any way gives the same writes.** -/
theorem Streamable.split {sink : BatchSink α β} (streams : Streamable sink) (A B C D : Finset α)
    (same : A ∪ B = C ∪ D) : sink A ∪ sink B = sink C ∪ sink D := by
  obtain ⟨-, union⟩ := (streamable_iff sink).mp streams
  rw [← union, ← union, same]

omit [DecidableEq α] in
/-- **Inserting a template instance per row streams.** -/
theorem image_streamable (template : α → β) : Streamable fun rows : Finset α => rows.image template :=
  ⟨fun a => {template a}, fun rows => by
    ext b
    simp [Finset.mem_image, Finset.mem_biUnion, eq_comm]⟩

/-- **A guarded count**: write `output` when the number of rows is `n`. -/
def countGuard (n : ℕ) (output : β) : BatchSink α β := fun rows => if rows.card = n then {output} else ∅

omit [DecidableEq β] in
/-- **A guarded count is not monotone**: the first `n + 1` numbers write nothing, while the first `n`, a partial
batch of them, write the output. -/
theorem countGuard_not_monotone (n : ℕ) (output : β) :
    Finset.range n ⊆ Finset.range (n + 1) ∧
      ¬ countGuard n output (Finset.range n) ⊆ countGuard n output (Finset.range (n + 1)) := by
  refine ⟨Finset.range_subset_range.mpr (Nat.le_succ n), ?_⟩
  simp [countGuard]

/-- **A guarded count does not stream.** -/
theorem countGuard_not_streamable (n : ℕ) (output : β) :
    ¬ Streamable (countGuard (α := ℕ) n output) := fun streams =>
  (countGuard_not_monotone n output).2 (streams.mono (countGuard_not_monotone n output).1)

/-- A count: write the number of rows. -/
def count : BatchSink α ℕ := fun rows => {rows.card}

/-- **A count does not stream**: it writes for no rows. -/
theorem count_not_streamable : ¬ Streamable (count (α := α)) := fun streams => by
  have empty := ((streamable_iff _).mp streams).1
  simp [count] at empty

/-- The least row. -/
def least : BatchSink ℕ ℕ := fun rows => if h : rows.Nonempty then {rows.min' h} else ∅

/-- **The least row is not monotone**: adding a smaller row displaces it. -/
theorem least_not_monotone : ¬ least {2} ⊆ least {1, 2} := by
  decide

/-- **The least row does not stream.** -/
theorem least_not_streamable : ¬ Streamable least := fun streams =>
  least_not_monotone (streams.mono (by decide))

end Mettapedia.Languages.MeTTa.StreamableSinks
