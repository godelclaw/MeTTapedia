import Mettapedia.GSLT.Coordination.OwnerFailover

/-!
# Commits across owners by deterministic ordering

A commit whose footprint lies at several homes cannot run at any one of them
(`Declarations.crossOwner_not_homed`). Deterministic ordering, the design of Calvin (Thomson,
Diamond, Weng, Ren, Shao and Abadi, SIGMOD 2012), first agrees on one order of the commits and then
lets every home execute that order on its own part of the store, deciding each commit by a rule
that depends only on the order.

## The execution

Each **partition** holds the occurrences homed at it. For each commit of the agreed order, each
partition computes its **local vote**: the part of the commit's enabling condition that its own
occurrences decide (`LocalEnabled`): what the commit takes or keeps there is present, what it makes
is new there, and the slice of every predicate query that lives there is as seen. The commit is
committed when every vote is yes, and then each partition applies its part (`localFire`). Otherwise
it is aborted, by every partition alike.

## Theorems

* **The local votes decide the global condition** (`localEnabled_iff`): every partition votes yes
  exactly when the commit is enabled at the union of the partitions' stores. Predicate queries that
  span partitions are included: each partition checks its slice.
* **The local firings are the global firing** (`union_localFire`).
* **Deterministic ordering refines the atomic semantics** (`ordered_refines`): the union of the
  partition stores after executing an order is the store of the serial run that fires each commit
  of the order when it is enabled and skips it otherwise, and the committed commits form a legal
  run of the atomic semantics (`committed_legal`).
* **The decision is a function of the order** (`decision_of_order`): no vote is a free choice, so
  any replica of any partition can recompute any vote from the agreed order. Nothing waits for a
  particular process: a partition that crashes is replaced by a replica that replays the order,
  which is the failover of `OwnerFailover`; this is why the class theorem of
  `AtomicCommitClass` does not apply (there a process's vote is its own input).
* **Executions of comparable orders are one history** (`ordered_append`, `chosen_orders_agree`):
  the order may come from the replicated log of `OwnerFailover`, whose chosen logs form one history,
  so partitions that have executed different chosen prefixes are at states of one serial run.

## Controls

* `Controls.whim_diverges`: a partition that may refuse a commit at its own discretion (a free
  vote, as in two-phase commit) makes two executions of one order reach different stores.
* `Controls.cross_partition_read`: a commit that queries a region spanning two partitions is
  committed when both slices hold and aborted by every partition when one slice fails.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.DeterministicOrdering

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.GSLT.Coordination.ReplicaMerge

universe u v w

variable {O : Type u} [DecidableEq O] {R : Type v} {L : Type w} [DecidableEq L] [Fintype L] [Nonempty L]
variable (label : O → R) (homeOf : O → L)

/-- The occurrences of a set homed at `l`. -/
def homedPart (l : L) (X : Finset O) : Finset O := X.filter fun o => homeOf o = l

/-- **The local vote of partition `l`**: what the commit takes and keeps at `l` is present, what it
makes is new at `l`, nothing is both taken and kept, and the slice at `l` of every predicate query
is as seen. -/
def LocalEnabled (l : L) (store : Finset O) (c : Commit O R) : Prop :=
  homedPart homeOf l c.taken ⊆ store ∧ homedPart homeOf l c.kept ⊆ store ∧ Disjoint c.taken c.kept ∧
    Disjoint c.made store ∧
      ∀ read ∈ c.queries, regionOf label store read.region = homedPart homeOf l read.seen

/-- Partition `l` applies its part of a committed commit. -/
def localFire (l : L) (store : Finset O) (c : Commit O R) : Finset O :=
  (store \ c.taken) ∪ homedPart homeOf l c.made

/-- The union of the partitions' stores. -/
def union (stores : L → Finset O) : Finset O := Finset.univ.biUnion stores

/-- Each partition holds only occurrences homed there. -/
def Partitioned (stores : L → Finset O) : Prop := ∀ l, ∀ o ∈ stores l, homeOf o = l

variable {label homeOf}

omit [DecidableEq L] [Nonempty L] in
theorem mem_union {stores : L → Finset O} {o : O} : o ∈ union stores ↔ ∃ l, o ∈ stores l := by
  simp [union]

omit [DecidableEq L] [Nonempty L] in
theorem mem_union_iff_home {stores : L → Finset O} (parts : Partitioned homeOf stores) {o : O} :
    o ∈ union stores ↔ o ∈ stores (homeOf o) := by
  rw [mem_union]
  constructor
  · rintro ⟨l, member⟩
    rw [parts l o member]
    exact member
  · exact fun member => ⟨_, member⟩

/-- **The local votes decide the global condition.** -/
theorem localEnabled_iff {stores : L → Finset O} (parts : Partitioned homeOf stores) (c : Commit O R) :
    (∀ l, LocalEnabled label homeOf l (stores l) c) ↔ Enabled label (union stores) c := by
  constructor
  · intro votes
    refine ⟨fun o taken => ?_, fun o kept => ?_, ?_, ?_, fun read member => ?_⟩
    · exact (mem_union_iff_home parts).mpr ((votes (homeOf o)).1 (Finset.mem_filter.mpr ⟨taken, rfl⟩))
    · exact (mem_union_iff_home parts).mpr ((votes (homeOf o)).2.1 (Finset.mem_filter.mpr ⟨kept, rfl⟩))
    · exact (votes (Classical.arbitrary L)).2.2.1
    · refine Finset.disjoint_left.mpr fun o made inUnion => ?_
      obtain ⟨l, inL⟩ := mem_union.mp inUnion
      exact Finset.disjoint_left.mp (votes l).2.2.2.1 made inL
    · unfold PredicateQuery.Holds
      ext o
      rw [mem_regionOf, mem_union_iff_home parts]
      have slice := (votes (homeOf o)).2.2.2.2 read member
      constructor
      · intro ⟨inStore, inRegion⟩
        have : o ∈ regionOf label (stores (homeOf o)) read.region := mem_regionOf.mpr ⟨inStore, inRegion⟩
        rw [slice] at this
        exact (Finset.mem_filter.mp this).1
      · intro seen
        have : o ∈ homedPart homeOf (homeOf o) read.seen := Finset.mem_filter.mpr ⟨seen, rfl⟩
        rw [← slice] at this
        exact mem_regionOf.mp this
  · intro enabled l
    refine ⟨fun o member => ?_, fun o member => ?_, enabled.apart, ?_, fun read member => ?_⟩
    · obtain ⟨taken, isL⟩ := Finset.mem_filter.mp member
      have := (mem_union_iff_home parts).mp (enabled.taken_subset taken)
      rw [isL] at this; exact this
    · obtain ⟨kept, isL⟩ := Finset.mem_filter.mp member
      have := (mem_union_iff_home parts).mp (enabled.kept_subset kept)
      rw [isL] at this; exact this
    · refine Finset.disjoint_left.mpr fun o made inL => ?_
      exact Finset.disjoint_left.mp enabled.fresh made (mem_union.mpr ⟨l, inL⟩)
    · have holds := enabled.queries_hold read member
      unfold PredicateQuery.Holds at holds
      ext o
      simp only [mem_regionOf, homedPart, Finset.mem_filter]
      constructor
      · rintro ⟨inStore, inRegion⟩
        have home := parts l o inStore
        have : o ∈ regionOf label (union stores) read.region :=
          mem_regionOf.mpr ⟨mem_union.mpr ⟨l, inStore⟩, inRegion⟩
        rw [holds] at this
        exact ⟨this, home⟩
      · rintro ⟨seen, home⟩
        rw [← holds] at seen
        obtain ⟨inUnion, inRegion⟩ := mem_regionOf.mp seen
        rw [mem_union_iff_home parts, home] at inUnion
        exact ⟨inUnion, inRegion⟩

omit [Nonempty L] in
/-- **The local firings are the global firing.** -/
theorem union_localFire (stores : L → Finset O) (c : Commit O R) :
    union (fun l => localFire homeOf l (stores l) c) = fire (union stores) c := by
  ext o
  simp only [mem_union, localFire, homedPart, mem_fire, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_filter]
  constructor
  · rintro ⟨l, ⟨inStore, notTaken⟩ | ⟨made, _⟩⟩
    · exact Or.inl ⟨⟨l, inStore⟩, notTaken⟩
    · exact Or.inr made
  · rintro (⟨⟨l, inStore⟩, notTaken⟩ | made)
    · exact ⟨l, Or.inl ⟨inStore, notTaken⟩⟩
    · exact ⟨homeOf o, Or.inr ⟨made, rfl⟩⟩

omit [Fintype L] [Nonempty L] in
theorem partitioned_localFire {stores : L → Finset O} (parts : Partitioned homeOf stores) (c : Commit O R) :
    Partitioned homeOf (fun l => localFire homeOf l (stores l) c) := by
  intro l o member
  simp only [localFire, homedPart, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter] at member
  rcases member with ⟨inStore, _⟩ | ⟨_, home⟩
  · exact parts l o inStore
  · exact home

/-! ## Executing an agreed order -/

variable (label homeOf)

open Classical in
/-- Every partition executes the agreed order: a commit is committed when every local vote is yes,
and then each partition applies its part. -/
noncomputable def ordered (stores : L → Finset O) : List (Commit O R) → L → Finset O
  | [] => stores
  | c :: cs =>
      if ∀ l, LocalEnabled label homeOf l (stores l) c then
        ordered (fun l => localFire homeOf l (stores l) c) cs
      else ordered stores cs

open Classical in
/-- The serial run with deterministic aborts: fire each commit when it is enabled, skip it
otherwise. -/
noncomputable def serial (store : Finset O) : List (Commit O R) → Finset O
  | [] => store
  | c :: cs => if Enabled label store c then serial (fire store c) cs else serial store cs

open Classical in
/-- The commits the serial run fires. -/
noncomputable def committed (store : Finset O) : List (Commit O R) → List (Commit O R)
  | [] => []
  | c :: cs => if Enabled label store c then c :: committed (fire store c) cs else committed store cs

variable {label homeOf}

/-- **Deterministic ordering refines the atomic semantics**: the partitions' stores after the
order are the serial store, and they stay partitioned. -/
theorem ordered_refines :
    ∀ (cs : List (Commit O R)) (stores : L → Finset O), Partitioned homeOf stores →
      union (ordered label homeOf stores cs) = serial label (union stores) cs ∧
        Partitioned homeOf (ordered label homeOf stores cs) := by
  intro cs
  induction cs with
  | nil => intro stores parts; exact ⟨rfl, parts⟩
  | cons c rest ih =>
      intro stores parts
      by_cases votes : ∀ l, LocalEnabled label homeOf l (stores l) c
      · have enabled := (localEnabled_iff parts c).mp votes
        simp only [ordered, serial, if_pos votes, if_pos enabled]
        rw [← union_localFire stores c]
        exact ih _ (partitioned_localFire parts c)
      · have notEnabled : ¬ Enabled label (union stores) c := fun enabled =>
          votes ((localEnabled_iff parts c).mpr enabled)
        simp only [ordered, serial, if_neg votes, if_neg notEnabled]
        exact ih stores parts

/-- **The committed commits are a run of the atomic semantics**, ending at the serial store. -/
theorem committed_legal :
    ∀ (cs : List (Commit O R)) (store : Finset O),
      Executable label store (committed label store cs) ∧ fireList store (committed label store cs) = serial label store cs := by
  intro cs
  induction cs with
  | nil => intro store; exact ⟨Executable.nil _, rfl⟩
  | cons c rest ih =>
      intro store
      by_cases enabled : Enabled label store c
      · simp only [committed, serial, if_pos enabled]
        obtain ⟨legal, final⟩ := ih (fire store c)
        exact ⟨Executable.cons enabled legal, by simpa [fireList] using final⟩
      · simp only [committed, serial, if_neg enabled]
        exact ih store

open Classical in
/-- **The decision is a function of the order**: the vote on the `k`-th commit is determined by the
initial stores and the commits before it. -/
theorem decision_of_order (stores : L → Finset O) (pre : List (Commit O R)) (c : Commit O R)
    (parts : Partitioned homeOf stores) :
    (∀ l, LocalEnabled label homeOf l (ordered label homeOf stores pre l) c) ↔
      Enabled label (serial label (union stores) pre) c := by
  rw [← (ordered_refines pre stores parts).1]
  exact localEnabled_iff (ordered_refines pre stores parts).2 c

omit [Nonempty L] in
/-- Executing an order in two pieces is executing it at once. -/
theorem ordered_append (stores : L → Finset O) (first second : List (Commit O R)) :
    ordered label homeOf stores (first ++ second) =
      ordered label homeOf (ordered label homeOf stores first) second := by
  induction first generalizing stores with
  | nil => rfl
  | cons c rest ih =>
      simp only [List.cons_append, ordered]
      split_ifs
      · exact ih _
      · exact ih _

/-! ## The order from the replicated log -/

section FromLog

open Mettapedia.GSLT.Coordination.OwnerFailover

variable {V : Type*} [DecidableEq V] {P : Type*} [DecidableEq P] {C : Type*} [DecidableEq C]
variable {quorum : Finset V → Prop} [DecidablePred quorum]

omit [Nonempty L] in
/-- **Executions of chosen orders are one history**: when the order is a chosen log of the
replicated sequencer, the partition states reached by executing any two chosen logs are the
states after two prefixes of one order: one is the continuation of the other. -/
theorem chosen_orders_agree (system : QuorumSystem quorum) {s : State V P C}
    (reach : Reachable quorum true (fun _ _ => True) s) (meaning : C → Commit O R)
    (stores : L → Finset O) {e₁ e₂ : ℕ} {L₁ L₂ : List C} (chosen₁ : Chosen quorum s e₁ L₁)
    (chosen₂ : Chosen quorum s e₂ L₂) :
    (∃ rest, ordered label homeOf stores (L₂.map meaning) =
        ordered label homeOf (ordered label homeOf stores (L₁.map meaning)) rest) ∨
      ∃ rest, ordered label homeOf stores (L₁.map meaning) =
        ordered label homeOf (ordered label homeOf stores (L₂.map meaning)) rest := by
  rcases chosen_comparable system (inv_reachable rfl reach) chosen₁ chosen₂ with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · exact Or.inl ⟨d.map meaning, by rw [List.map_append, ordered_append]⟩
  · exact Or.inr ⟨d.map meaning, by rw [List.map_append, ordered_append]⟩

end FromLog

/-! ## Controls -/

namespace Controls

/-- Two partitions; occurrence `0` at `true`, occurrence `1` at `false`. -/
def homeOfTwo (o : ℕ) : Bool := decide (o % 2 = 0)

/-- Take both: a commit across the two partitions. -/
def takeBoth : Commit ℕ ℕ := ⟨{0, 1}, ∅, {2}, []⟩

open Classical in
/-- A partition that may refuse at its own discretion: `true` refuses when `whim` says so. -/
noncomputable def withWhim (whim : Bool) (stores : Bool → Finset ℕ) : Bool → Finset ℕ :=
  if (∀ l, LocalEnabled id homeOfTwo l (stores l) takeBoth) ∧ whim = false then
    fun l => localFire homeOfTwo l (stores l) takeBoth
  else stores

/-- The initial partition stores. -/
def startStores : Bool → Finset ℕ := fun l => if l then {0} else {1}

/-- **A free vote diverges**: with the same order and the same stores, a partition that may refuse
at its discretion makes one execution commit and another abort. -/
theorem whim_diverges :
    union (withWhim false startStores) = {2} ∧ union (withWhim true startStores) = {0, 1} := by
  have votes : ∀ l, LocalEnabled id homeOfTwo l (startStores l) takeBoth := by
    intro l
    cases l <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  constructor
  · rw [withWhim, if_pos ⟨votes, rfl⟩]
    decide
  · rw [withWhim, if_neg (fun h => absurd h.2 (by decide))]
    decide

/-- Labels: the parity of an occurrence. -/
def parity (o : ℕ) : ℕ := o % 2

/-- Every occurrence is in the region. -/
def everything : ℕ → Bool := fun _ => true

/-- Make `4` if the store is exactly `{0, 1}`: a predicate query across both partitions. -/
def readAll : Commit ℕ ℕ := ⟨∅, ∅, {4}, [⟨everything, {0, 1}⟩]⟩

/-- **A predicate query across partitions**: both slices hold at the start, so every partition votes
yes; after occurrence `1` is replaced by `3`, the slice at `false` fails, and the commit is
aborted. -/
theorem cross_partition_read :
    (∀ l, LocalEnabled parity homeOfTwo l (startStores l) readAll) ∧
      ¬ LocalEnabled parity homeOfTwo false ({3} : Finset ℕ) readAll := by
  refine ⟨fun l => ?_, ?_⟩
  · cases l <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · rintro ⟨-, -, -, -, reads⟩
    have := reads _ (List.mem_singleton_self _)
    revert this
    decide

end Controls

end Mettapedia.GSLT.Coordination.DeterministicOrdering
