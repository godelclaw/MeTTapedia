import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Traces

/-!
# Replicas of an occurrence store, and when their merge is serial

A replica holds what it has heard of an occurrence store: every occurrence it has seen and the
occurrences it has heard were taken (`Replica`, a pair of finite sets). It lives on the
occurrences seen and not taken (`live`). A commit applied at a replica adds what it makes to the
seen set and what it takes to the taken set (`apply`). Two replicas merge by union of both sets
(`⊔`), the join of the pair lattice, so merging is idempotent, commutative and associative and
needs no coordination. Occurrence identities are global: what a commit makes has never been seen
anywhere (`Fresh`).

## A commit at a replica is a firing

* `live_apply`: applying a commit enabled at a replica's live store fires it there.

## Two concurrent commits

Two replicas start from one state and each applies one commit; neither has seen the other's.
Their merge is a store whatever the commits are (`live_merge_concurrent`): the union of both
effects, the same set that firing one after the other produces. The question is whether some
serial run of the two commits is **legal**, that is, whether the second is still enabled after the
first (`SerialAt`).

* **The merge is serial exactly when the commits do not clash and at most one spoils the other**
  (`serial_iff`). In the terms of `OccurrenceCommits.Exactness`: no common taken occurrence or
  fresh identity, and the "must precede" relation of the pair is acyclic.

This is the distributed analogue of independence. Independence (no clash, no spoil either way)
says that both orders are legal; a merge needs one. A reader and a taker of one occurrence
merge serially, the reader first; two takers of one occurrence merge to a store in which both
took it, which no serial run reaches; two absence reads that each make into the other's region
merge to write skew.

## Monotone commits

* **Monotone commits always merge serially, in every order** (`monotone_merge_legal`): commits that
  take nothing and query nothing, applied at any number of replicas from one state, merge
  to the store of the serial run in the order given, and that run is executable. This is the
  coordination-freedom half of CALM for commits.

## Controls

`Controls.reader_taker_serial`, `Controls.takers_double_take`, `Controls.write_skew`,
`Controls.senders_serial`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ReplicaMerge

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v

/-- A replica: the occurrences it has seen, and those it has heard were taken. -/
abbrev Replica (O : Type u) := Finset O × Finset O

variable {O : Type u} [DecidableEq O] {R : Type v}

namespace Replica

/-- What a replica has seen. -/
def seen (r : Replica O) : Finset O := r.1

/-- What a replica has heard was taken. -/
def gone (r : Replica O) : Finset O := r.2

/-- The live store of a replica: seen and not taken. -/
def live (r : Replica O) : Finset O := r.seen \ r.gone

/-- Taken occurrences are seen ones. -/
abbrev WellFormed (r : Replica O) : Prop := r.gone ⊆ r.seen

/-- Apply a commit at a replica. -/
def apply (r : Replica O) (c : Commit O R) : Replica O := (r.seen ∪ c.made, r.gone ∪ c.taken)

/-- What a commit makes has never been seen. -/
abbrev Fresh (r : Replica O) (c : Commit O R) : Prop := Disjoint c.made r.seen

theorem mem_live {r : Replica O} {o : O} : o ∈ r.live ↔ o ∈ r.seen ∧ o ∉ r.gone := by
  simp [live]

theorem sup_seen (r s : Replica O) : (r ⊔ s).seen = r.seen ∪ s.seen := rfl

theorem sup_gone (r s : Replica O) : (r ⊔ s).gone = r.gone ∪ s.gone := rfl

theorem apply_seen (r : Replica O) (c : Commit O R) : (r.apply c).seen = r.seen ∪ c.made := rfl

theorem apply_gone (r : Replica O) (c : Commit O R) : (r.apply c).gone = r.gone ∪ c.taken := rfl

theorem le_apply (r : Replica O) (c : Commit O R) : r ≤ r.apply c :=
  ⟨Finset.subset_union_left, Finset.subset_union_left⟩

theorem live_subset_seen (r : Replica O) : r.live ⊆ r.seen := Finset.sdiff_subset

theorem apply_wellFormed {r : Replica O} (wf : r.WellFormed) {c : Commit O R}
    (takenSeen : c.taken ⊆ r.seen) : (r.apply c).WellFormed :=
  Finset.union_subset (wf.trans Finset.subset_union_left) (takenSeen.trans Finset.subset_union_left)

theorem sup_wellFormed {r s : Replica O} (wfR : r.WellFormed) (wfS : s.WellFormed) :
    (r ⊔ s).WellFormed :=
  Finset.union_subset_union wfR wfS

end Replica

open Replica

/-- **A commit at a replica is a firing of its live store.** -/
theorem live_apply {label : O → R} {r : Replica O} (wf : r.WellFormed) {c : Commit O R}
    (enabled : Enabled label r.live c) (fresh : r.Fresh c) :
    (r.apply c).live = fire r.live c := by
  ext o
  simp only [mem_live, apply_seen, apply_gone, mem_fire, Finset.mem_union, not_or]
  have takenSeen := enabled.taken_subset.trans (live_subset_seen r)
  constructor
  · rintro ⟨inSeen | made, notGone, notTaken⟩
    · exact Or.inl ⟨⟨inSeen, notGone⟩, notTaken⟩
    · exact Or.inr made
  · rintro (⟨⟨inSeen, notGone⟩, notTaken⟩ | made)
    · exact ⟨Or.inl inSeen, notGone, notTaken⟩
    · have notSeen : o ∉ r.seen := Finset.disjoint_left.mp fresh made
      exact ⟨Or.inr made, fun gone => notSeen (wf gone), fun taken => notSeen (takenSeen taken)⟩

section Concurrent

variable {label : O → R} {r : Replica O} {c d : Commit O R}

/-- **Two concurrent commits merge to the union of their effects**, which is the set that firing
one after the other produces. -/
theorem live_merge_concurrent (wf : r.WellFormed) (enabledC : Enabled label r.live c)
    (enabledD : Enabled label r.live d) (freshC : r.Fresh c) (freshD : r.Fresh d) :
    (r.apply c ⊔ r.apply d).live = fire (fire r.live c) d := by
  ext o
  simp only [mem_live, sup_seen, sup_gone, apply_seen, apply_gone, mem_fire, Finset.mem_union,
    not_or]
  have takenC := enabledC.taken_subset.trans (live_subset_seen r)
  have takenD := enabledD.taken_subset.trans (live_subset_seen r)
  constructor
  · rintro ⟨seenHere, ⟨notGone, notTakenC⟩, ⟨-, notTakenD⟩⟩
    rcases seenHere with (inSeen | madeC) | (inSeen | madeD)
    · exact Or.inl ⟨Or.inl ⟨⟨inSeen, notGone⟩, notTakenC⟩, notTakenD⟩
    · exact Or.inl ⟨Or.inr madeC, notTakenD⟩
    · exact Or.inl ⟨Or.inl ⟨⟨inSeen, notGone⟩, notTakenC⟩, notTakenD⟩
    · exact Or.inr madeD
  · have fromMade : ∀ {e : Commit O R}, r.Fresh e → o ∈ e.made →
        o ∉ r.gone ∧ o ∉ c.taken ∧ o ∉ d.taken := fun fresh made => by
      have notSeen : o ∉ r.seen := Finset.disjoint_left.mp fresh made
      exact ⟨fun gone => notSeen (wf gone), fun taken => notSeen (takenC taken),
        fun taken => notSeen (takenD taken)⟩
    rintro (⟨⟨⟨inSeen, notGone⟩, notTakenC⟩ | madeC, notTakenD⟩ | madeD)
    · exact ⟨Or.inl (Or.inl inSeen), ⟨notGone, notTakenC⟩, ⟨notGone, notTakenD⟩⟩
    · obtain ⟨notGone, notTakenC, notTakenD'⟩ := fromMade freshC madeC
      exact ⟨Or.inl (Or.inr madeC), ⟨notGone, notTakenC⟩, ⟨notGone, notTakenD'⟩⟩
    · obtain ⟨notGone, notTakenC, notTakenD⟩ := fromMade freshD madeD
      exact ⟨Or.inr (Or.inr madeD), ⟨notGone, notTakenC⟩, ⟨notGone, notTakenD⟩⟩

/-- **A legal serial run reaches the merge**: one of the two orders runs both commits and ends in
the merged store. -/
def SerialAt (label : O → R) (r : Replica O) (c d : Commit O R) : Prop :=
  (Enabled label (fire r.live c) d ∧ (r.apply c ⊔ r.apply d).live = fire (fire r.live c) d) ∨
    (Enabled label (fire r.live d) c ∧ (r.apply c ⊔ r.apply d).live = fire (fire r.live d) c)

/-- **The merge of two concurrent commits is serial exactly when they do not clash and at most one
of them spoils the other.** -/
theorem serial_iff (wf : r.WellFormed) (enabledC : Enabled label r.live c)
    (enabledD : Enabled label r.live d) (freshC : r.Fresh c) (freshD : r.Fresh d) :
    SerialAt label r c d ↔ ¬ Clash c d ∧ (¬ Spoils label c d ∨ ¬ Spoils label d c) := by
  have merged := live_merge_concurrent wf enabledC enabledD freshC freshD
  have swapped : (r.apply c ⊔ r.apply d).live = fire (fire r.live d) c :=
    merged.trans (fire_comm enabledC enabledD)
  unfold SerialAt
  rw [enabled_fire_iff enabledD enabledC, enabled_fire_iff enabledC enabledD]
  constructor
  · rintro (⟨⟨noClash, noSpoil⟩, _⟩ | ⟨⟨noClash, noSpoil⟩, _⟩)
    · exact ⟨fun clash => noClash clash.symm, Or.inl noSpoil⟩
    · exact ⟨noClash, Or.inr noSpoil⟩
  · rintro ⟨noClash, noSpoil | noSpoil⟩
    · exact Or.inl ⟨⟨fun clash => noClash clash.symm, noSpoil⟩, merged⟩
    · exact Or.inr ⟨⟨noClash, noSpoil⟩, swapped⟩

/-- Independent commits merge serially, in both orders. -/
theorem serial_of_independent (wf : r.WellFormed) (enabledC : Enabled label r.live c)
    (enabledD : Enabled label r.live d) (freshC : r.Fresh c) (freshD : r.Fresh d)
    (independent : Independent label c d) : SerialAt label r c d :=
  (serial_iff wf enabledC enabledD freshC freshD).mpr
    ⟨independent.1, Or.inl independent.2.1⟩

end Concurrent

/-! ## Monotone commits

A run of commits is an `Executable` sequence of `OccurrenceCommits.Waves`, fired by `fireList`, and
the fresh identities of a list are `GloballyFresh` (`OccurrenceCommits.Traces`). -/

/-- Merge the replicas that each applied one commit to a common state. -/
def mergeAll (r : Replica O) (cs : List (Commit O R)) : Replica O :=
  cs.foldl (fun merged c => merged ⊔ r.apply c) r

theorem mergeAll_seen_gone (r : Replica O) (cs : List (Commit O R))
    (monotone : ∀ c ∈ cs, c.Monotone) :
    (mergeAll r cs).seen = r.seen ∪ madeOf cs ∧ (mergeAll r cs).gone = r.gone := by
  suffices ∀ (start : Replica O), start.gone = r.gone → r.seen ⊆ start.seen →
      (cs.foldl (fun merged c => merged ⊔ r.apply c) start).seen = start.seen ∪ madeOf cs ∧
        (cs.foldl (fun merged c => merged ⊔ r.apply c) start).gone = r.gone from
    this r rfl le_rfl
  induction cs with
  | nil => intro start gone _; simp [madeOf, gone]
  | cons c rest ih =>
      intro start gone below
      have monoC := monotone c (List.mem_cons_self ..)
      rw [List.foldl_cons]
      have restMono : ∀ e ∈ rest, e.Monotone := fun e member => monotone e (List.mem_cons_of_mem _ member)
      obtain ⟨seenEq, goneEq⟩ := ih restMono (start ⊔ r.apply c)
        (by simp only [sup_gone, apply_gone, gone, monoC.1, Finset.union_empty, Finset.union_self])
        (below.trans (by simp only [sup_seen]; exact Finset.subset_union_left))
      refine ⟨?_, goneEq⟩
      rw [seenEq]
      ext o
      simp only [sup_seen, apply_seen, madeOf, Finset.mem_union]
      have := @below o
      tauto

/-- Take-free commits only add what they make. -/
theorem fireList_of_monotone (store : Finset O) (cs : List (Commit O R))
    (monotone : ∀ c ∈ cs, c.Monotone) : fireList store cs = store ∪ madeOf cs := by
  induction cs generalizing store with
  | nil => simp [madeOf]
  | cons c rest ih =>
      have monoC := monotone c (List.mem_cons_self ..)
      rw [fireList_cons, ih _ fun e member => monotone e (List.mem_cons_of_mem _ member)]
      simp only [fire, monoC.1, Finset.sdiff_empty, madeOf, Finset.union_assoc]

/-- Monotone commits, each enabled at one store, with globally fresh identities, run in the order
given. -/
theorem executable_of_monotone {label : O → R} (store seen : Finset O) (cs : List (Commit O R))
    (monotone : ∀ c ∈ cs, c.Monotone) (enabled : ∀ c ∈ cs, Enabled label store c)
    (storeSeen : store ⊆ seen) (fresh : GloballyFresh seen cs) : Executable label store cs := by
  suffices ∀ (rest pre : List (Commit O R)), pre ++ rest = cs →
      Executable label (store ∪ madeOf pre) rest by
    simpa [madeOf] using this cs [] rfl
  intro rest
  induction rest with
  | nil => intro _ _; exact Executable.nil _
  | cons c rest ih =>
      intro pre split
      have member : c ∈ cs := split ▸ List.mem_append_right _ (List.mem_cons_self ..)
      have monoC := monotone c member
      have enabledC := enabled c member
      have apartPre : Disjoint c.made (madeOf pre) := by
        have pairwise := fresh.2
        rw [← split, List.pairwise_append] at pairwise
        refine Finset.disjoint_left.mpr fun o made inPre => ?_
        obtain ⟨a, aPre, madeA⟩ := mem_madeOf.mp inPre
        exact Finset.disjoint_left.mp (pairwise.2.2 a aPre c (List.mem_cons_self ..)) madeA made
      refine Executable.cons ?_ ?_
      · exact
          { taken_subset := by simp [monoC.1]
            kept_subset := enabledC.kept_subset.trans Finset.subset_union_left
            apart := enabledC.apart
            fresh := Finset.disjoint_union_right.mpr
              ⟨Finset.disjoint_of_subset_right storeSeen (fresh.1 c member), apartPre⟩
            queries_hold := by simp [monoC.2] }
      · have grown : fire (store ∪ madeOf pre) c = store ∪ madeOf (pre ++ [c]) := by
          simp only [fire, monoC.1, Finset.sdiff_empty, madeOf_append, madeOf,
            Finset.union_empty, Finset.union_assoc]
        rw [grown]
        exact ih (pre ++ [c]) (by rw [← split]; simp)

/-- **Monotone commits merge serially.** Commits that take nothing and query nothing,
applied at separate replicas to one well-formed state, with fresh pairwise distinct identities,
merge to the store of the serial run in the order given, and that serial run is executable. -/
theorem monotone_merge_legal {label : O → R} {r : Replica O} (wf : r.WellFormed)
    (cs : List (Commit O R)) (monotone : ∀ c ∈ cs, c.Monotone)
    (enabled : ∀ c ∈ cs, Enabled label r.live c) (fresh : GloballyFresh r.seen cs) :
    (mergeAll r cs).live = fireList r.live cs ∧ Executable label r.live cs := by
  refine ⟨?_, executable_of_monotone r.live r.seen cs monotone enabled (live_subset_seen r) fresh⟩
  obtain ⟨seenEq, goneEq⟩ := mergeAll_seen_gone r cs monotone
  rw [fireList_of_monotone _ cs monotone]
  ext o
  simp only [live, seenEq, goneEq, Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨inSeen | made, notGone⟩
    · exact Or.inl ⟨inSeen, notGone⟩
    · exact Or.inr made
  · rintro (⟨inSeen, notGone⟩ | made)
    · exact ⟨Or.inl inSeen, notGone⟩
    · obtain ⟨c, member, madeC⟩ := mem_madeOf.mp made
      have notSeen : o ∉ r.seen := Finset.disjoint_left.mp (fresh.1 c member) madeC
      exact ⟨Or.inr made, fun gone => notSeen (wf gone)⟩

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Controls

/-- A replica holding the token, occurrence `0`. -/
def holdsToken : Replica ℕ := ({0}, ∅)

theorem holdsToken_live : holdsToken.live = {0} := by decide

theorem holdsToken_wellFormed : holdsToken.WellFormed := by decide

/-- **A reader and a taker of one token merge serially**, the reader first. -/
theorem reader_taker_serial :
    SerialAt label holdsToken reader taker ∧
      (holdsToken.apply reader ⊔ holdsToken.apply taker).live = {5, 6} := by
  refine ⟨(serial_iff holdsToken_wellFormed (holdsToken_live ▸ reader_enabled)
    (holdsToken_live ▸ taker_enabled) (by decide) (by decide)).mpr ⟨?_, Or.inl ?_⟩, by decide⟩
  · unfold Clash; simp [reader, taker]
  · unfold Spoils WritesInto; simp [reader, taker]

/-- **Two takers of one token merge to a double take**: the token is gone and both takers'
outputs are present, which no serial run reaches. -/
theorem takers_double_take :
    ¬ SerialAt label holdsToken taker taker₂ ∧
      (holdsToken.apply taker ⊔ holdsToken.apply taker₂).live = {6, 11} := by
  refine ⟨fun serial => ?_, by decide⟩
  have := ((serial_iff holdsToken_wellFormed (holdsToken_live ▸ taker_enabled)
    (holdsToken_live ▸ taker₂_enabled) (by decide) (by decide)).mp serial).1
  exact this (Or.inl (by simp [taker, taker₂]))

/-- Cells of the write-skew control. -/
inductive Cell where
  | p
  | q
  | other
  deriving DecidableEq

/-- Occurrence `40` is a `p`, `41` a `q`. -/
def cellLabel : ℕ → Cell
  | 40 => .p
  | 41 => .q
  | _ => .other

def isP : Cell → Bool
  | .p => true
  | _ => false

def isQ : Cell → Bool
  | .q => true
  | _ => false

/-- Make a `p` when no `q` is present. -/
def pUnlessQ : Commit ℕ Cell := ⟨∅, ∅, {40}, [⟨isQ, ∅⟩]⟩

/-- Make a `q` when no `p` is present. -/
def qUnlessP : Commit ℕ Cell := ⟨∅, ∅, {41}, [⟨isP, ∅⟩]⟩

/-- An empty replica. -/
def empty : Replica ℕ := (∅, ∅)

theorem pUnlessQ_enabled : Enabled cellLabel empty.live pUnlessQ where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by
    intro read member
    simp only [pUnlessQ, List.mem_singleton] at member
    subst member
    decide

theorem qUnlessP_enabled : Enabled cellLabel empty.live qUnlessP where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by
    intro read member
    simp only [qUnlessP, List.mem_singleton] at member
    subst member
    decide

/-- **Write skew**: each absence read is spoiled by the other's addition, so the merge, which
holds both a `p` and a `q`, is not serial. -/
theorem write_skew :
    ¬ SerialAt cellLabel empty pUnlessQ qUnlessP ∧
      (empty.apply pUnlessQ ⊔ empty.apply qUnlessP).live = {40, 41} := by
  refine ⟨fun serial => ?_, by decide⟩
  obtain ⟨_, spoils⟩ := (serial_iff (by decide) pUnlessQ_enabled qUnlessP_enabled (by decide)
    (by decide)).mp serial
  have spoilsPQ : Spoils cellLabel pUnlessQ qUnlessP :=
    Or.inr ⟨⟨isP, ∅⟩, by simp [qUnlessP], 40, by simp [pUnlessQ], rfl⟩
  have spoilsQP : Spoils cellLabel qUnlessP pUnlessQ :=
    Or.inr ⟨⟨isQ, ∅⟩, by simp [pUnlessQ], 41, by simp [qUnlessP], rfl⟩
  rcases spoils with notPQ | notQP
  · exact notPQ spoilsPQ
  · exact notQP spoilsQP

/-- Three sends into the output region. -/
def sends : List (Commit ℕ Atom) := [⟨∅, ∅, {50}, []⟩, ⟨∅, ∅, {51}, []⟩, ⟨∅, ∅, {52}, []⟩]

/-- **Sends merge serially**: three replicas each send once; the merge is the serial run, and it is
legal. -/
theorem senders_serial :
    (mergeAll holdsToken sends).live = {0, 50, 51, 52} ∧ Executable label holdsToken.live sends := by
  have merged := monotone_merge_legal (label := label) holdsToken_wellFormed sends
    (by intro c member; simp only [sends, List.mem_cons, List.not_mem_nil,
      or_false] at member; rcases member with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩)
    (by
      intro c member
      simp only [sends, List.mem_cons, List.not_mem_nil, or_false] at member
      rw [holdsToken_live]
      rcases member with rfl | rfl | rfl <;>
        exact { taken_subset := by decide, kept_subset := by decide, apart := by decide,
                fresh := by decide, queries_hold := by simp })
    ⟨by
      intro c member
      simp only [sends, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide,
     by decide⟩
  refine ⟨?_, merged.2⟩
  rw [merged.1, holdsToken_live]
  decide

end Controls

end Mettapedia.GSLT.Coordination.ReplicaMerge
