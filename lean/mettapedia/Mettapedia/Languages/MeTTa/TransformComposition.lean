import Mettapedia.Languages.MeTTa.StreamableSinks
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Multiset.AddSub

/-!
# Composing transforms: when a reader may run beside a writer, when spans fuse, and what is compositional

## Pipelining and barriers

A transform writes, through a sink, what its rows make; a second transform reads the store. Run beside the
first, the reader sees the store after every prefix of the rows and keeps whatever it derives
(`pipelinedWrites`); behind a barrier it sees only the complete batch (`barrierWrites`).

* **For a monotone sink and a monotone reader the two agree**, whatever the order of the rows
  (`pipelined_eq_barrier`).
* **They agree for every store and order exactly when the reader is monotone**
  (`pipelining_safe_for_reader_iff`): an absence reader (`absentReader_not_monotone`) needs a barrier
  even behind an insertion.
* **They agree behind every monotone reader exactly when the sink is monotone**
  (`pipelining_safe_for_sink_iff`): a guarded count needs a barrier before anything reads it.

So a stratum boundary is needed exactly at a non-monotone edge: a predicate query (absence, `all`,
`unique`, a count) downstream, or a staged sink upstream.

## Fusing two rule instances

Two commits in sequence, where the second reads and consumes only what the first produced together with
the store, are one commit of a fused span (`Span.fuse`): enabled exactly when the sequence is
(`Span.fuse_enables_iff`) and reaching the same store (`Span.fuse_fire`). What the second consumes of the
first's production never reaches the store: with a full hand-off the fused span writes only the second's
production (`Span.fuse_produce_of_handoff`). This is deforestation for transforms.

## Staged sinks

A staged sink adds the rows' contributions in a commutative monoid and finalizes the sum once
(`StagedSink`). Its staging divides among workers in any way (`StagedSink.run_split`), runs as a fold in
any order (`StagedSink.run_eq_foldr`), and is what an `all` source followed by a fold computes. A
streamable sink is a staged sink through the union of writes with the identity as its finalization
(`StagedSink.ofStreamable_run`). Counts and sums stage through the natural numbers
(`StagedSink.count_run`).

## What is compositional

Bags of atoms combine by union. A reaction semantics is compositional for union when behavioural
equivalence is a congruence for it.
* **Unlabelled reactions are not compositional for a join** (`bisimilarity_not_congruence`): a lone
  `a` and the empty bag are bisimilar (neither reacts), but beside `b` the first reacts and the second
  does not.
* **Labelling each reaction with the context it borrows makes it compositional**
  (`saturated_congruence`): for every reaction relation on bags, bisimilarity of the relation
  `M —J→ N ⇔ M + J → N` is a congruence for union, and it refines unlabelled bisimilarity
  (`bisimilar_of_saturated`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TransformComposition

open Mettapedia.Languages.MeTTa.StreamableSinks

universe u v w

/-! ## Pipelining and barriers -/

section Pipelining

variable {α : Type u} {β : Type v} {γ : Type w} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- What a reader derives behind a barrier: from the store with the whole batch written. -/
def barrierWrites (store : Finset β) (sink : BatchSink α β) (reader : Finset β → Finset γ)
    (rows : List α) : Finset γ :=
  reader (store ∪ sink rows.toFinset)

/-- What a reader running beside the writer derives: everything it derives after some prefix of the
rows. -/
def pipelinedWrites (store : Finset β) (sink : BatchSink α β) (reader : Finset β → Finset γ)
    (rows : List α) : Finset γ :=
  (Finset.range (rows.length + 1)).biUnion fun k => reader (store ∪ sink (rows.take k).toFinset)

theorem barrier_subset_pipelined (store : Finset β) (sink : BatchSink α β)
    (reader : Finset β → Finset γ) (rows : List α) :
    barrierWrites store sink reader rows ⊆ pipelinedWrites store sink reader rows := by
  intro x member
  refine Finset.mem_biUnion.mpr ⟨rows.length, Finset.self_mem_range_succ _, ?_⟩
  rwa [List.take_length]

/-- **For a monotone sink and a monotone reader, running beside equals running behind a barrier.** -/
theorem pipelined_eq_barrier (store : Finset β) {sink : BatchSink α β} (sinkMono : Monotone sink)
    {reader : Finset β → Finset γ} (readerMono : Monotone reader) (rows : List α) :
    pipelinedWrites store sink reader rows = barrierWrites store sink reader rows := by
  apply Finset.Subset.antisymm _ (barrier_subset_pipelined store sink reader rows)
  intro x member
  obtain ⟨k, -, inPrefix⟩ := Finset.mem_biUnion.mp member
  have prefixSub : (rows.take k).toFinset ⊆ rows.toFinset := fun y inTake =>
    List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp inTake))
  exact readerMono (Finset.union_subset_union (le_refl store) (sinkMono prefixSub)) inPrefix

/-- Writing each row as itself. -/
def identitySink : BatchSink β β := fun rows => rows

omit [DecidableEq β] in
theorem identitySink_monotone : Monotone (identitySink (β := β)) := fun _ _ le => le

/-- **Running beside equals the barrier for every store and order exactly when the reader is
monotone.** -/
theorem pipelining_safe_for_reader_iff (reader : Finset β → Finset γ) :
    (∀ store rows, pipelinedWrites store identitySink reader rows =
      barrierWrites store identitySink reader rows) ↔ Monotone reader := by
  constructor
  · intro safe A B le x inA
    have agree := safe A (B \ A).toList
    have early : reader (A ∪ identitySink (((B \ A).toList).take 0).toFinset) ⊆
        pipelinedWrites A identitySink reader (B \ A).toList := fun y member =>
      Finset.mem_biUnion.mpr ⟨0, by simp, member⟩
    rw [agree] at early
    have inBarrier := early (by simpa [identitySink] using inA)
    simpa [barrierWrites, identitySink, Finset.union_sdiff_of_subset le] using inBarrier
  · intro readerMono store rows
    exact pipelined_eq_barrier store identitySink_monotone readerMono rows

/-- **Running beside equals the barrier behind every monotone reader exactly when the sink is
monotone.** -/
theorem pipelining_safe_for_sink_iff (sink : BatchSink α β) :
    (∀ (store : Finset β) (rows : List α), pipelinedWrites store sink (fun X => X) rows =
      barrierWrites store sink (fun X => X) rows) ↔ Monotone sink := by
  constructor
  · intro safe A B le x inA
    let rows := A.toList ++ (B \ A).toList
    have takeA : (rows.take A.toList.length).toFinset = A := by
      simp [rows]
    have early : sink A ⊆ pipelinedWrites ∅ sink (fun X => X) rows := by
      intro y member
      refine Finset.mem_biUnion.mpr ⟨A.toList.length, ?_, ?_⟩
      · simp [rows]
        omega
      · rw [takeA]
        simpa using member
    rw [safe ∅ rows] at early
    have whole : rows.toFinset = B := by
      ext y
      simp only [rows, List.toFinset_append, Finset.toList_toFinset, Finset.mem_union,
        Finset.mem_sdiff]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact le h
        · exact h
      · intro h
        by_cases inA' : y ∈ A
        · exact Or.inl inA'
        · exact Or.inr ⟨h, inA'⟩
    simpa [barrierWrites, whole] using early inA
  · intro sinkMono store rows
    exact pipelined_eq_barrier store sinkMono (fun _ _ le => le) rows

/-- A reader that derives `out` when `q` is absent. -/
def absentReader (q out : β) : Finset β → Finset β := fun X => if q ∈ X then ∅ else {out}

/-- **An absence reader is not monotone**, so it needs a barrier behind any writer of `q`. -/
theorem absentReader_not_monotone (q out : β) : ¬ Monotone (absentReader q out) := by
  intro mono
  have := mono (Finset.empty_subset {q})
  simp [absentReader] at this

end Pipelining

/-! ## Fusing two rule instances -/

section Fusion

variable {R : Type u} [DecidableEq R]

/-- A ground rule instance: what it consumes, what it reads, what it produces. -/
structure Span (R : Type u) where
  consume : Multiset R
  read : Multiset R
  produce : Multiset R

namespace Span

/-- Enabled: consumption and reads present side by side. -/
def Enables (s : Span R) (M : Multiset R) : Prop := s.consume + s.read ≤ M

/-- Commit: remove the consumption, add the production. -/
def fire (s : Span R) (M : Multiset R) : Multiset R := M - s.consume + s.produce

/-- **The fused span** of `s` then `t`, when `t` consumes only what `s` produced: it consumes what `s`
consumes, reads what `s` reads and what `t` reads beyond `s`'s remaining production, and produces what
remains of `s`'s production and `t`'s. -/
def fuse (s t : Span R) : Span R where
  consume := s.consume
  read := s.read ∪ (t.read - (s.produce - t.consume))
  produce := (s.produce - t.consume) + t.produce

/-- **The fused span is enabled exactly when the sequence is.** -/
theorem fuse_enables_iff (s t : Span R) (M : Multiset R) (handoff : t.consume ≤ s.produce) :
    (s.fuse t).Enables M ↔ s.Enables M ∧ t.Enables (s.fire M) := by
  unfold Enables fire fuse
  simp only
  rw [Multiset.le_iff_count, Multiset.le_iff_count, Multiset.le_iff_count]
  have hc := Multiset.le_iff_count.mp handoff
  constructor
  · intro le
    refine ⟨fun a => ?_, fun a => ?_⟩
    · have := le a
      simp only [Multiset.count_add, Multiset.count_union] at this ⊢
      omega
    · have := le a
      have := hc a
      simp only [Multiset.count_add, Multiset.count_union, Multiset.count_sub] at *
      omega
  · rintro ⟨first, second⟩ a
    have := first a
    have := second a
    have := hc a
    simp only [Multiset.count_add, Multiset.count_union, Multiset.count_sub] at *
    omega

/-- **The fused span reaches the store the sequence reaches.** -/
theorem fuse_fire (s t : Span R) (M : Multiset R) (handoff : t.consume ≤ s.produce) :
    (s.fuse t).fire M = t.fire (s.fire M) := by
  unfold fire fuse
  ext a
  have := Multiset.le_iff_count.mp handoff a
  simp only [Multiset.count_add, Multiset.count_sub]
  omega

/-- **With a full hand-off the intermediate never reaches the store**: the fused span writes only the
second production. -/
theorem fuse_produce_of_handoff (s t : Span R) (handoff : t.consume = s.produce) :
    (s.fuse t).produce = t.produce := by
  ext a
  simp [fuse, handoff, Multiset.count_sub]

end Span

end Fusion

/-! ## Staged sinks -/

section Staged

variable {α : Type u} {β : Type v} {M : Type w} [AddCommMonoid M]

/-- **A staged sink**: each row contributes in a commutative monoid; the sum is finalized once. -/
structure StagedSink (α : Type u) (β : Type v) (M : Type w) [AddCommMonoid M] where
  contribution : α → M
  finalize : M → Finset β

namespace StagedSink

/-- What the sink writes for a bag of rows. -/
def run (sink : StagedSink α β M) (rows : Multiset α) : Finset β :=
  sink.finalize (rows.map sink.contribution).sum

/-- **Staging divides among workers in any way.** -/
theorem run_split (sink : StagedSink α β M) (A B : Multiset α) :
    sink.run (A + B) = sink.finalize ((A.map sink.contribution).sum + (B.map sink.contribution).sum) := by
  simp [run, Multiset.map_add, Multiset.sum_add]

/-- **Staging runs as a fold over the rows in any order.** -/
theorem run_eq_foldr (sink : StagedSink α β M) (rows : List α) :
    sink.run (rows : Multiset α) =
      sink.finalize (rows.foldr (fun row acc => sink.contribution row + acc) 0) := by
  unfold run
  congr 1
  induction rows with
  | nil => simp
  | cons row rows ih => simp [← ih]

end StagedSink

/-- Written atoms, combined by union. -/
structure Writes (β : Type v) where
  atoms : Finset β

instance : Zero (Writes β) := ⟨⟨∅⟩⟩

instance [DecidableEq β] : Add (Writes β) := ⟨fun s t => ⟨s.atoms ∪ t.atoms⟩⟩

theorem Writes.ext' {s t : Writes β} (h : s.atoms = t.atoms) : s = t := by
  cases s; cases t; cases h; rfl

instance [DecidableEq β] : AddCommMonoid (Writes β) where
  add_assoc _ _ _ := Writes.ext' (Finset.union_assoc _ _ _)
  zero_add _ := Writes.ext' (Finset.empty_union _)
  add_zero _ := Writes.ext' (Finset.union_empty _)
  add_comm _ _ := Writes.ext' (Finset.union_comm _ _)
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl

namespace StagedSink

/-- A streamable sink as a staged sink: stage the union of writes, finalize by reading the atoms. -/
def ofStreamable [DecidableEq β] (contribution : α → Finset β) : StagedSink α β (Writes β) where
  contribution := fun row => ⟨contribution row⟩
  finalize := Writes.atoms

/-- **A streamable sink is the staged sink through the union of writes.** -/
theorem ofStreamable_run [DecidableEq α] [DecidableEq β] (contribution : α → Finset β)
    (rows : Finset α) :
    (ofStreamable contribution).run rows.val = rows.biUnion contribution := by
  unfold run ofStreamable
  induction rows using Finset.induction_on with
  | empty => rfl
  | insert a rows notIn ih =>
      rw [Finset.insert_val_of_notMem notIn, Multiset.map_cons, Multiset.sum_cons,
        Finset.biUnion_insert, ← ih]
      rfl

/-- A count of the rows, written as one atom. -/
def count (output : ℕ → β) : StagedSink α β ℕ where
  contribution := fun _ => 1
  finalize := fun n => {output n}

/-- **A count stages through the natural numbers.** -/
theorem count_run (output : ℕ → β) (rows : Multiset α) :
    (count output).run rows = {output (Multiset.card rows)} := by
  simp [run, count]

end StagedSink

end Staged

/-! ## What is compositional -/

section Compositional

variable {R : Type u}

/-- A bisimulation of a reaction relation. -/
def IsBisimulation (step : Multiset R → Multiset R → Prop) (B : Multiset R → Multiset R → Prop) : Prop :=
  ∀ M N, B M N → (∀ M', step M M' → ∃ N', step N N' ∧ B M' N') ∧ (∀ N', step N N' → ∃ M', step M M' ∧ B M' N')

/-- Bisimilar: related by some bisimulation. -/
def Bisimilar (step : Multiset R → Multiset R → Prop) (M N : Multiset R) : Prop :=
  ∃ B, IsBisimulation step B ∧ B M N

/-- The reaction with a borrowed context: `M —J→ N` when `M + J → N`. -/
def Saturated (step : Multiset R → Multiset R → Prop) (M : Multiset R) (J : Multiset R)
    (N : Multiset R) : Prop :=
  step (M + J) N

/-- A bisimulation of the reaction with borrowed contexts: every borrowed context is matched. -/
def IsSaturatedBisimulation (step : Multiset R → Multiset R → Prop) (B : Multiset R → Multiset R → Prop) :
    Prop :=
  ∀ M N, B M N → ∀ J, (∀ M', Saturated step M J M' → ∃ N', Saturated step N J N' ∧ B M' N') ∧
    (∀ N', Saturated step N J N' → ∃ M', Saturated step M J M' ∧ B M' N')

def SaturatedBisimilar (step : Multiset R → Multiset R → Prop) (M N : Multiset R) : Prop :=
  ∃ B, IsSaturatedBisimulation step B ∧ B M N

/-- **Bisimilarity with borrowed contexts is a congruence for union**, for every reaction relation. -/
theorem saturated_congruence (step : Multiset R → Multiset R → Prop) {M N : Multiset R}
    (similar : SaturatedBisimilar step M N) (C : Multiset R) :
    SaturatedBisimilar step (M + C) (N + C) := by
  refine ⟨fun X Y => ∃ M₀ N₀ C₀, SaturatedBisimilar step M₀ N₀ ∧ X = M₀ + C₀ ∧ Y = N₀ + C₀, ?_,
    ⟨M, N, C, similar, rfl, rfl⟩⟩
  rintro X Y ⟨M₀, N₀, C₀, ⟨B, bisim, related⟩, rfl, rfl⟩ J
  have shift : ∀ P : Multiset R, P + C₀ + J = P + (C₀ + J) := fun P => add_assoc _ _ _
  constructor
  · intro M' stepM
    unfold Saturated at stepM
    rw [shift] at stepM
    obtain ⟨N', stepN, related'⟩ := (bisim M₀ N₀ related (C₀ + J)).1 M' stepM
    refine ⟨N', by unfold Saturated; rw [shift]; exact stepN, M', N', 0, ⟨B, bisim, related'⟩, ?_, ?_⟩ <;>
      simp
  · intro N' stepN
    unfold Saturated at stepN
    rw [shift] at stepN
    obtain ⟨M', stepM, related'⟩ := (bisim M₀ N₀ related (C₀ + J)).2 N' stepN
    refine ⟨M', by unfold Saturated; rw [shift]; exact stepM, M', N', 0, ⟨B, bisim, related'⟩, ?_, ?_⟩ <;>
      simp

/-- **Bisimilarity with borrowed contexts refines plain bisimilarity.** -/
theorem bisimilar_of_saturated (step : Multiset R → Multiset R → Prop) {M N : Multiset R}
    (similar : SaturatedBisimilar step M N) : Bisimilar step M N := by
  obtain ⟨B, bisim, related⟩ := similar
  refine ⟨B, fun X Y relXY => ⟨fun X' stepX => ?_, fun Y' stepY => ?_⟩, related⟩
  · obtain ⟨Y', stepY, rel⟩ := (bisim X Y relXY 0).1 X' (by unfold Saturated; simpa using stepX)
    exact ⟨Y', by unfold Saturated at stepY; simpa using stepY, rel⟩
  · obtain ⟨X', stepX, rel⟩ := (bisim X Y relXY 0).2 Y' (by unfold Saturated; simpa using stepY)
    exact ⟨X', by unfold Saturated at stepX; simpa using stepX, rel⟩

/-- Atoms of the join control. -/
inductive JoinAtom where
  | a | b | c
  deriving DecidableEq, Repr

open JoinAtom

/-- A join: consume `a` and `b`, produce `c`. -/
def joinStep (M N : Multiset JoinAtom) : Prop := ({a, b} : Multiset JoinAtom) ≤ M ∧ N = M - {a, b} + {c}

/-- **Unlabelled reactions are not compositional for a join**: a lone `a` and the empty bag are
bisimilar, and beside `b` they are not. -/
theorem bisimilarity_not_congruence :
    Bisimilar joinStep {a} 0 ∧ ¬ Bisimilar joinStep ({a} + {b}) (0 + {b}) := by
  constructor
  · refine ⟨fun X Y => X = {a} ∧ Y = 0, ?_, rfl, rfl⟩
    rintro X Y ⟨rfl, rfl⟩
    refine ⟨fun X' ⟨le, _⟩ => absurd le (by decide), fun Y' ⟨le, _⟩ => absurd le (by decide)⟩
  · rintro ⟨B, bisim, related⟩
    obtain ⟨Y', ⟨le, _⟩, -⟩ := (bisim _ _ related).1 ({a} + {b} - {a, b} + {c}) ⟨by decide, rfl⟩
    exact absurd le (by decide)

end Compositional

end Mettapedia.Languages.MeTTa.TransformComposition
