import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceControls

/-!
# Footprint types: the separating sum, typed parallel composition, and trust discharged

The static footprint of a transform (`Sources.Transform.static`) lists, as region keys, what the
transform may take, keep, query and make. Read as a **type**, it is a resource assertion:
exclusive use of what is taken, shared use of what is kept, observation of the queried regions,
and writes into the regions taken from or made into. This module makes that reading exact
enough to type parallel composition, and proves what the typing buys.

## The separating sum

Two footprint types **separate** when `Sources.StaticFootprint.Apart` holds: nothing one may take is
taken or kept by the other, and nothing one may write lies in a region the other queries.
Their sum (`+`, concatenation of the key lists) is then their separating conjunction.

* **Symmetry** (`apart_comm`): for keys whose apartness test is symmetric, separation is symmetric.
* **Pairwise determinacy** (`apart_add_left`, `apart_typeSum_left`): a sum separates from a type
  exactly when each summand does. Unlike fractional permissions, where three halves are pairwise
  compatible and not jointly, the shared use here is idempotent: any number of keepers coexist.
* **The empty type** separates from everything (`nothing_apart`).

## Typed parallel composition

A list of transforms is **typed in parallel** (`ParTyped`) when their footprint types pairwise
separate. The check is decidable, independent of the order of the components
(`parTyped_perm`), and independent of how the components are grouped: typing `ts ++ us` is typing
each part and separating the sums of their types (`parTyped_append_iff`).

## What the typing buys

A **typed batch** is a list of commits, each fired at one store by a component of a parallel
composition that is typed, with apart fresh identities.

* Its commits are pairwise independent (`TypedBatch.independent`), so the batch runs in every
  order and every order reaches the one wave commit (`TypedBatch.every_order`).
* **The trust promise is discharged by the types** (`TypedBatch.snapshot_iff_serial`): under the
  cheap `snapshot` check, which validates only takes, the batch has exactly the outcomes of
  serializable rounds. A typed program may therefore run under the cheapest check without a
  promise of its own.

## Duplicable types: the exponential of footprints

A footprint type is **duplicable** when it separates from itself (`Duplicable`). Then any number of
copies separate (`parTyped_replicate`), so any number of concurrent firings of a persistent rule
with that type need no check. When every key covers some value, the duplicable types are exactly
those that take nothing and make nothing inside a region they query (`duplicable_iff`).
This is the sense in which a persistent (`whenever`) rule is a `!`: it may fire concurrently with
itself without validation when its footprint, apart from its own kept occurrence, is duplicable.
A rule that takes is never duplicable: two of its firings may take one occurrence.

## Controls

With the head keys of the source controls, a taker of `tok` and a reader of `lock` are typed in
parallel, a taker and a reader of `tok` are not (`Controls.takeTok_readLock_typed`,
`Controls.takeTok_readTok_untyped`); the reader of `lock` is duplicable and the taker of `tok` is
not (`Controls.readLock_duplicable`, `Controls.takeTok_not_duplicable`), and two firings of the
taker at a store with one `tok` clash (`Controls.takeTok_twice_clash`). A typed batch exists at a
store with a `tok` and a `lock` (`Controls.typedBatch_instance`), so the theorems above are not
vacuous.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe uO uV uT uP uK

variable {O : Type uO} {V : Type uV} {T : Type uT} {P : Type uP} {K : Type uK}

/-! ## The separating sum -/

section Separation

variable {R : RegionKeys T P K}

/-- Region keys whose apartness test does not depend on the order of its arguments. -/
def SymmetricKeys (R : RegionKeys T P K) : Prop := ∀ k k', R.apart k k' = R.apart k' k

/-- Every key covers some value. -/
def InhabitedKeys (R : RegionKeys T P K) : Prop := ∀ k, ∃ t, R.covers k t

theorem allApart_append_left {a b c : List K} :
    R.AllApart (a ++ b) c ↔ R.AllApart a c ∧ R.AllApart b c := by
  unfold RegionKeys.AllApart
  simp only [List.mem_append]
  constructor
  · intro h
    exact ⟨fun k hk => h k (Or.inl hk), fun k hk => h k (Or.inr hk)⟩
  · rintro ⟨ha, hb⟩ k (hk | hk)
    · exact ha k hk
    · exact hb k hk

theorem allApart_append_right {a b c : List K} :
    R.AllApart a (b ++ c) ↔ R.AllApart a b ∧ R.AllApart a c := by
  unfold RegionKeys.AllApart
  simp only [List.mem_append]
  constructor
  · intro h
    exact ⟨fun k hk k' hk' => h k hk k' (Or.inl hk'), fun k hk k' hk' => h k hk k' (Or.inr hk')⟩
  · rintro ⟨hb, hc⟩ k hk k' (hk' | hk')
    · exact hb k hk k' hk'
    · exact hc k hk k' hk'

theorem allApart_nil_left (c : List K) : R.AllApart [] c := fun k hk => by simp at hk

theorem allApart_nil_right (a : List K) : R.AllApart a [] := fun _ _ k' hk' => by simp at hk'

theorem allApart_comm (symm : SymmetricKeys R) {a b : List K} :
    R.AllApart a b ↔ R.AllApart b a := by
  constructor
  · intro h k hk k' hk'
    rw [symm]
    exact h k' hk' k hk
  · intro h k hk k' hk'
    rw [symm]
    exact h k' hk' k hk

/-- **Separation is symmetric** for keys with a symmetric apartness test. -/
theorem apart_comm (symm : SymmetricKeys R) {a b : StaticFootprint K} :
    a.Apart R b ↔ b.Apart R a := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨(allApart_comm symm).mp h1, h3, h2, h5, h4⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨(allApart_comm symm).mp h1, h3, h2, h5, h4⟩

/-- **Pairwise determinacy, left**: a sum separates from a type exactly when each summand does. -/
theorem apart_add_left {a b c : StaticFootprint K} :
    (a + b).Apart R c ↔ a.Apart R c ∧ b.Apart R c := by
  simp only [StaticFootprint.Apart, StaticFootprint.takes_add, StaticFootprint.keeps_add,
    StaticFootprint.queries_add, StaticFootprint.makes_add, allApart_append_left,
    allApart_append_right]
  tauto

/-- **Pairwise determinacy, right.** -/
theorem apart_add_right {a b c : StaticFootprint K} :
    a.Apart R (b + c) ↔ a.Apart R b ∧ a.Apart R c := by
  simp only [StaticFootprint.Apart, StaticFootprint.takes_add, StaticFootprint.keeps_add,
    StaticFootprint.queries_add, StaticFootprint.makes_add, allApart_append_left,
    allApart_append_right]
  tauto

/-- The empty footprint type: it touches nothing. -/
def nothing : StaticFootprint K := ⟨[], [], [], []⟩

/-- The empty type separates from every type. -/
theorem nothing_apart (a : StaticFootprint K) : (nothing : StaticFootprint K).Apart R a :=
  ⟨allApart_nil_left _, allApart_nil_left _, allApart_nil_right _, allApart_nil_left _,
    allApart_nil_right _⟩

/-- Every type separates from the empty type. -/
theorem apart_nothing (a : StaticFootprint K) : a.Apart R (nothing : StaticFootprint K) :=
  ⟨allApart_nil_right _, allApart_nil_right _, allApart_nil_left _, allApart_nil_right _,
    allApart_nil_left _⟩

/-- The separating sum of a list of types. -/
def typeSum : List (StaticFootprint K) → StaticFootprint K
  | [] => nothing
  | a :: rest => a + typeSum rest

/-- A sum of types separates from a type exactly when every summand does. -/
theorem apart_typeSum_left {c : StaticFootprint K} :
    ∀ {l : List (StaticFootprint K)}, (typeSum l).Apart R c ↔ ∀ a ∈ l, a.Apart R c
  | [] => by simpa [typeSum] using nothing_apart c
  | a :: rest => by
      rw [typeSum, apart_add_left, apart_typeSum_left]
      simp

/-- A type separates from a sum of types exactly when it separates from every summand. -/
theorem apart_typeSum_right {a : StaticFootprint K} :
    ∀ {l : List (StaticFootprint K)}, a.Apart R (typeSum l) ↔ ∀ c ∈ l, a.Apart R c
  | [] => by simpa [typeSum] using apart_nothing a
  | c :: rest => by
      rw [typeSum, apart_add_right, apart_typeSum_right]
      simp

end Separation

/-! ## Typed parallel composition -/

section Parallel

variable {R : RegionKeys T P K}

/-- **A parallel composition is typed** when the footprint types of its components pairwise
separate. -/
def ParTyped (R : RegionKeys T P K) (ts : List (Transform V T P)) : Prop :=
  ts.Pairwise fun t t' => (t.static R).Apart R (t'.static R)

instance (ts : List (Transform V T P)) : Decidable (ParTyped R ts) :=
  inferInstanceAs (Decidable (List.Pairwise _ _))

/-- The typing does not depend on the order of the components. -/
theorem parTyped_perm (symm : SymmetricKeys R) {ts ts' : List (Transform V T P)} (perm : ts.Perm ts') :
    ParTyped R ts ↔ ParTyped R ts' :=
  List.Perm.pairwise_iff (fun h => (apart_comm symm).mp h) perm

/-- **The typing does not depend on the grouping**: a composition of two groups is typed exactly
when each group is, and the sums of their types separate. -/
theorem parTyped_append_iff {ts us : List (Transform V T P)} :
    ParTyped R (ts ++ us) ↔ ParTyped R ts ∧ ParTyped R us ∧
      (typeSum (ts.map (Transform.static R))).Apart R (typeSum (us.map (Transform.static R))) := by
  unfold ParTyped
  rw [List.pairwise_append, apart_typeSum_left]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, apart_typeSum_right]

/-- **A duplicable type** separates from itself. -/
def Duplicable (R : RegionKeys T P K) (a : StaticFootprint K) : Prop := a.Apart R a

instance (a : StaticFootprint K) : Decidable (Duplicable R a) :=
  inferInstanceAs (Decidable (a.Apart R a))

/-- **Any number of copies** of one component are typed in parallel exactly when there is at most
one copy or its type is duplicable. -/
theorem parTyped_replicate {n : ℕ} {t : Transform V T P} :
    ParTyped R (List.replicate n t) ↔ n ≤ 1 ∨ Duplicable R (t.static R) :=
  List.pairwise_replicate

/-- **The duplicable types**, when every key covers a value: those that take nothing and make
nothing inside a region they query. -/
theorem duplicable_iff (inhabited : InhabitedKeys R) {a : StaticFootprint K} :
    Duplicable R a ↔ a.takes = [] ∧ R.AllApart a.makes a.queries := by
  constructor
  · rintro ⟨takeTake, -, -, writeRead, -⟩
    have noTakes : a.takes = [] := by
      refine List.eq_nil_iff_forall_not_mem.mpr fun k member => ?_
      obtain ⟨t, covers⟩ := inhabited k
      exact R.apart_sound k k (takeTake k member k member) t covers covers
    refine ⟨noTakes, ?_⟩
    rw [noTakes] at writeRead
    exact writeRead
  · rintro ⟨noTakes, makeRead⟩
    unfold Duplicable StaticFootprint.Apart
    rw [noTakes]
    exact ⟨allApart_nil_left _, allApart_nil_left _, allApart_nil_left _, makeRead, makeRead⟩

end Parallel

/-! ## What the typing buys -/

section Batches

variable [DecidableEq O] {L : TermLayer V T P} {m : Matcher V T P} {label : O → T}
  {R : RegionKeys T P K}

/-- **A typed batch** at a store: each commit is fired there by its component, the components are
typed in parallel, and the fresh identities are pairwise apart. -/
structure TypedBatch (L : TermLayer V T P) (m : Matcher V T P) (label : O → T)
    (R : RegionKeys T P K) (S : Finset O) (W : List (Transform V T P × Commit O T)) : Prop where
  fires : ∀ w ∈ W, Fires L m label S w.1 w.2
  typed : ParTyped R (W.map Prod.fst)
  freshApart : W.Pairwise fun a b => Disjoint a.2.made b.2.made

namespace TypedBatch

variable {S : Finset O} {W : List (Transform V T P × Commit O T)}

theorem enabled (batch : TypedBatch L m label R S W) : ∀ c ∈ W.map Prod.snd, Enabled label S c := by
  intro c member
  obtain ⟨w, inW, rfl⟩ := List.mem_map.mp member
  exact (batch.fires w inW).enabled

/-- **The commits of a typed batch are pairwise independent.** -/
theorem independent (sound : Matcher.Sound L m) (keysSound : R.Sound L)
    (batch : TypedBatch L m label R S W) : (W.map Prod.snd).Pairwise (Independent label) := by
  have typed : W.Pairwise fun a b => (a.1.static R).Apart R (b.1.static R) := by
    have h := batch.typed
    unfold ParTyped at h
    exact (List.pairwise_map (f := Prod.fst)
      (R := fun t t' : Transform V T P => (t.static R).Apart R (t'.static R))).mp h
  refine List.pairwise_map.mpr ((typed.and batch.freshApart).imp_of_mem ?_)
  rintro a b inA inB ⟨staticApart, freshApart⟩
  exact independent_of_staticApart sound keysSound staticApart (batch.fires a inA) (batch.fires b inB)
    freshApart

/-- The precedence relation of a typed batch is acyclic: the trust promise holds. -/
theorem acyclic (sound : Matcher.Sound L m) (keysSound : R.Sound L)
    (batch : TypedBatch L m label R S W) : Acyclic label (W.map Prod.snd) :=
  acyclic_of_pairwise_independent (batch.independent sound keysSound)

/-- **A typed batch runs in every order, and every order reaches the wave commit.** -/
theorem every_order (sound : Matcher.Sound L m) (keysSound : R.Sound L)
    (batch : TypedBatch L m label R S W) {l : List (Commit O T)} (perm : l.Perm (W.map Prod.snd)) :
    Executable label S l ∧ fireList S l = fire S (effectOf (W.map Prod.snd)) := by
  have enabledL : ∀ c ∈ l, Enabled label S c := fun c member => batch.enabled c (perm.subset member)
  have independentL : l.Pairwise (Independent label) :=
    (List.Perm.pairwise_iff (fun h => Independent.symm h) perm).mpr (batch.independent sound keysSound)
  refine ⟨executable_of_pairwise_independent enabledL independentL, ?_⟩
  rw [fireList_perm (MatchedAt.of_enabled enabledL) perm]
  exact Executable.fireList_eq batch.enabled

/-- **The trust promise is discharged by the types.** Under the `snapshot` check, which validates
only what is taken, a typed batch has exactly the outcomes of serializable rounds. -/
theorem snapshot_iff_serial (sound : Matcher.Sound L m) (keysSound : R.Sound L)
    (batch : TypedBatch L m label R S W) (final : Finset O) :
    SnapshotOutcome label S (W.map Prod.snd) final ↔ SerialOutcome label S (W.map Prod.snd) final := by
  have noClash : (W.map Prod.snd).Pairwise fun e d => ¬ Clash e d :=
    (batch.independent sound keysSound).imp fun independent => independent.1
  constructor
  · exact snapshot_refines_of_acyclic batch.enabled noClash (batch.acyclic sound keysSound)
  · intro serial
    obtain ⟨A, subperm, -, rfl⟩ := (serialOutcome_iff batch.enabled noClash).mp serial
    exact (snapshotOutcome_iff batch.enabled noClash).mpr ⟨A, subperm, rfl⟩

end TypedBatch

/-- **Concurrent firings of one duplicable component** form a typed batch: a persistent rule with a
duplicable type fires any number of times at one store with no check. -/
theorem typedBatch_of_duplicable {S : Finset O} {t : Transform V T P}
    {W : List (Transform V T P × Commit O T)} (dup : Duplicable R (t.static R))
    (component : ∀ w ∈ W, w.1 = t) (fires : ∀ w ∈ W, Fires L m label S w.1 w.2)
    (freshApart : W.Pairwise fun a b => Disjoint a.2.made b.2.made) :
    TypedBatch L m label R S W := by
  refine ⟨fires, ?_, freshApart⟩
  have same : W.map Prod.fst = List.replicate W.length t := by
    rw [List.eq_replicate_iff]
    refine ⟨List.length_map _, fun b member => ?_⟩
    obtain ⟨w, inW, rfl⟩ := List.mem_map.mp member
    exact component w inW
  rw [same]
  exact parTyped_replicate.mpr (Or.inr dup)

end Batches

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Commutative
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Controls

/-- The keys of the commutative-matching module have a symmetric apartness test. -/
theorem keys_symmetric {F : Type} [DecidableEq F] {V' : Type} [DecidableEq V']
    (keys : Pat V' F → List (Key F)) : SymmetricKeys (regionKeys keys) := by
  intro k k'
  cases k <;> cases k' <;> simp [regionKeys, Key.apart, eq_comm]

/-- Every key of the commutative-matching module covers a value. -/
theorem keys_inhabited {F : Type} [DecidableEq F] [Nonempty F] {V' : Type} [DecidableEq V']
    (keys : Pat V' F → List (Key F)) : InhabitedKeys (regionKeys keys) := by
  intro k
  rcases k with _ | f | ⟨f, g⟩
  · exact ⟨.leaf (Classical.arbitrary _), trivial⟩
  · exact ⟨.leaf f, rfl⟩
  · exact ⟨.node f (.leaf g) (.leaf g), ⟨.leaf g, .leaf g, rfl, rfl⟩⟩

/-- **Positive control**: a taker of `tok` and a reader of `lock` are typed in parallel. -/
theorem takeTok_readLock_typed : ParTyped headR [takeTok, readLock] := by decide

/-- **Negative control**: a taker of `tok` and a reader of `tok` are not. -/
theorem takeTok_readTok_untyped : ¬ ParTyped headR [takeTok, readTok] := by decide

/-- The order of the components does not matter. -/
theorem readLock_takeTok_typed : ParTyped headR [readLock, takeTok] :=
  (parTyped_perm (keys_symmetric _) (List.Perm.swap _ _ _)).mp takeTok_readLock_typed

/-- **The reader of `lock` is duplicable**: any number of its firings are typed in parallel. -/
theorem readLock_duplicable : Duplicable headR (readLock.static headR) := by decide

/-- **The taker of `tok` is not duplicable.** -/
theorem takeTok_not_duplicable : ¬ Duplicable headR (takeTok.static headR) := by decide

/-- The characterization agrees: the taker of `tok` takes. -/
theorem takeTok_takes : (takeTok.static headR).takes ≠ [] := by decide

/-- **Two firings of the taker at one `tok` clash**: they take the same occurrence. -/
theorem takeTok_twice_clash :
    ∃ c d, Fires Lc mc lbl oneTok takeTok c ∧ Fires Lc mc lbl oneTok takeTok d ∧ Clash c d := by
  obtain ⟨x, xMember, xLinear, xTakes⟩ : ∃ x ∈ takeTok.rows Lc mc lbl oneTok,
      (footprintOf x.2).Linear ∧ (footprintOf x.2).takes = {(k .tok, 0)} :=
    exists_of_not_forall (by decide)
  obtain ⟨c, commitC⟩ := exists_isCommitOf (S := oneTok) supply (footprintOf x.2)
  obtain ⟨d, commitD⟩ := exists_isCommitOf (S := oneTok) supply (footprintOf x.2)
  refine ⟨c, d, ⟨x, xMember, xLinear, commitC⟩, ⟨x, xMember, xLinear, commitD⟩, Or.inl ?_⟩
  rw [commitC.taken, commitD.taken, xTakes]
  decide

/-- A store with one `tok` and one `lock`. -/
def tokLock : Finset Occ := {(k .tok, 0), (k .lock, 0)}

/-- **A typed batch exists**: a taker of `tok` and a reader of `lock` fire at one store, and their
batch meets every hypothesis of the theorems above. -/
theorem typedBatch_instance :
    ∃ c d, TypedBatch Lc mc lbl headR tokLock [(takeTok, c), (readLock, d)] ∧
      ∀ final, (SnapshotOutcome lbl tokLock [c, d] final ↔ SerialOutcome lbl tokLock [c, d] final) := by
  obtain ⟨x, xMember, xLinear, xMakes⟩ : ∃ x ∈ takeTok.rows Lc mc lbl tokLock,
      (footprintOf x.2).Linear ∧ (footprintOf x.2).makes = 0 :=
    exists_of_not_forall (by decide)
  obtain ⟨y, yMember, yLinear⟩ : ∃ y ∈ readLock.rows Lc mc lbl tokLock, (footprintOf y.2).Linear :=
    exists_of_not_forall (by decide)
  obtain ⟨c, commitC⟩ := exists_isCommitOf (S := tokLock) supply (footprintOf x.2)
  obtain ⟨d, commitD⟩ := exists_isCommitOf (S := tokLock) supply (footprintOf y.2)
  have takerMakesNothing : c.made = ∅ := made_eq_empty commitC xMakes
  have batch : TypedBatch Lc mc lbl headR tokLock [(takeTok, c), (readLock, d)] :=
    ⟨by
      intro w member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨x, xMember, xLinear, commitC⟩
      · exact ⟨y, yMember, yLinear, commitD⟩,
     takeTok_readLock_typed,
     by simp [takerMakesNothing]⟩
  exact ⟨c, d, batch, batch.snapshot_iff_serial cmatch_sound (headKeys_sound bagComm)⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
