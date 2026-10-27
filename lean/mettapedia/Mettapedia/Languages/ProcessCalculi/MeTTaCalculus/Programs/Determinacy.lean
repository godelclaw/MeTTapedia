import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Traces
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes.Facets

/-!
# Determinism as a capability fact

A program runs as a **system of commits**: the ground firings its processes can make. A run fires
enabled commits one after another; a scheduler picks which. The program is **determinate** from a
store when its observable result does not depend on that choice. This module proves when that is
so, and states the condition on the rights that processes hold, not on a mode of execution.

## Keller's theorem for commits

A system is **conflict-free** from a store when, at every store it reaches, two distinct enabled
commits of the system are independent (`Exactness.Independent`: no clash, neither spoils the
other). Then:

* an enabled commit stays enabled along every run that does not fire it (`ConflictFree.persists`);
* a commit enabled at the start can be moved to the front of any run that fires it
  (`ConflictFree.bubble`);
* **any two maximal runs fire the same commits, each as often, and end at one store**
  (`ConflictFree.maximal_agree`);
* **any two runs extend to runs that fire the same commits and end at one store**
  (`ConflictFree.reconcile`). This is the statement for programs that never stop.

This is the theorem of Keller (1975) for persistent, commutative transition systems, in the commit
semantics; the diamond is `Exactness.fire_comm`.

## Which rights make a system conflict-free

Each process holds rights (`InteractionTypes.Rights`): the facets `send`, `receive`, `peek` and
`observe` at each name, and its commits are formed under them (`FormedUnder`). Two facets
**conflict** (`conflicts`) when commits of two different processes holding them at one name can
disturb each other: two receivers can take one occurrence; a receiver can take what a peeker keeps;
a receiver or a sender can change a region an observer queries. A name is **safe** when no two
different processes hold conflicting facets there (`SafeAt`).

* **Different processes never disturb each other at safe names** (`independent_of_safe`): when
  every name is safe and two processes make apart identities, any two of their formed commits are
  independent.
* **The criterion is exact** (`exists_not_perm_of_not_safe`): if one name is not safe, a system of
  two processes with one formed commit each, located identities and nothing else, has two maximal
  runs that are not permutations of each other.
* **The system theorem** (`conflictFree_of_safe`, `determinate_of_safe`): safe names, located
  identities and processes that are each determinate on their own make the whole system
  determinate.

The safe names include the two classical cases:

* **monotone names** (`safeAt_of_monotoneAt`): nobody receives or observes there. A system all of
  whose commits are monotone is conflict-free with no condition on processes at all
  (`conflictFree_of_monotone`): this is the CALM theorem of Hellerstein (2010) and of Ameloot,
  Neven and Van den Bussche (2013) for commits. Its lattice form, where identities are forgotten,
  is that fair chaotic iteration of monotone rules is schedule-independent
  (`GSLT.OpenEnded.ChaoticIteration.schedule_independent`), the meet-closed fibre.
* **Kahn names** (`safeAt_of_kahnAt`): one process receives and peeks there, the others only send,
  and nobody observes. This is the single-reader channel of Kahn (1974).

and two more: names private to one process (`safeAt_of_privateAt`), and **boards**, where one
process writes and observes and the others only peek (`Profiles.board_safe`).

Real choice lives exactly at the conflicting pairs: a shared `receive` (competing consumers), a
`receive` against a `peek`, and a `receive` or `send` against an `observe` (a predicate query
racing with takes or makes).

## The profiles of regions

`Profiles` classifies the five region profiles of the interaction kernel (holder facets, and the
facets a handed-out handle may carry): a `board` is safe; a `space`, a `channel`, a `mailbox` and a
`log` are not. A mailbox whose holder never observes, a log whose holder never observes, and a
channel handed out with `send` alone are safe. So determinism comes out of the declared profile as
a certified property of the region; no execution mode is involved.

## Controls

* `Controls.competing_consumers`: two receivers of one name (a `receive`/`receive` pair).
* `Controls.unordered_reader`: one reader taking from a bag in either order, with the order
  visible in its output: the condition that each process be determinate on its own.
* `Controls.shared_allocator`: two monotone makers that claim one identity: the located-identity
  condition.
* `Controls.calm_closure`, `Controls.kahn_pipeline`: determinate systems, by the two theorems.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes

universe uO uR uN uI

/-! ## Runs of a system of commits -/

section Runs

variable {O : Type uO} [DecidableEq O] {R : Type uR}

/-- A run of a system of commits from a store: an executable sequence of the system's commits. -/
def IsRun (label : O → R) (sys : Commit O R → Prop) (store : Finset O)
    (run : List (Commit O R)) : Prop :=
  Executable label store run ∧ ∀ c ∈ run, sys c

/-- The stores a system reaches from a store. -/
def Reaches (label : O → R) (sys : Commit O R → Prop) (store target : Finset O) : Prop :=
  ∃ run, IsRun label sys store run ∧ fireList store run = target

/-- No commit of the system is enabled at the store. -/
def Terminal (label : O → R) (sys : Commit O R → Prop) (store : Finset O) : Prop :=
  ∀ c, sys c → ¬ Enabled label store c

/-- A maximal run ends at a store where no commit of the system is enabled. -/
def Maximal (label : O → R) (sys : Commit O R → Prop) (store : Finset O)
    (run : List (Commit O R)) : Prop :=
  IsRun label sys store run ∧ Terminal label sys (fireList store run)

/-- **Conflict-free from a store**: at every store the system reaches, two distinct commits of the
system that are both enabled there are independent. -/
def ConflictFree (label : O → R) (sys : Commit O R → Prop) (store : Finset O) : Prop :=
  ∀ t, Reaches label sys store t → ∀ c d, sys c → sys d → c ≠ d →
    Enabled label t c → Enabled label t d → Independent label c d

variable {label : O → R} {sys : Commit O R → Prop}

theorem IsRun.nil (store : Finset O) : IsRun label sys store [] :=
  ⟨.nil _, fun _ member => by simp at member⟩

theorem isRun_cons_iff {store : Finset O} {c : Commit O R} {rest : List (Commit O R)} :
    IsRun label sys store (c :: rest) ↔
      sys c ∧ Enabled label store c ∧ IsRun label sys (fire store c) rest := by
  simp only [IsRun, executable_cons_iff, List.mem_cons, forall_eq_or_imp]
  tauto

theorem isRun_append_iff {store : Finset O} {first second : List (Commit O R)} :
    IsRun label sys store (first ++ second) ↔
      IsRun label sys store first ∧ IsRun label sys (fireList store first) second := by
  simp only [IsRun, executable_append_iff, List.mem_append]
  constructor
  · rintro ⟨⟨executableFirst, executableSecond⟩, all⟩
    exact ⟨⟨executableFirst, fun c member => all c (Or.inl member)⟩,
      ⟨executableSecond, fun c member => all c (Or.inr member)⟩⟩
  · rintro ⟨⟨executableFirst, allFirst⟩, ⟨executableSecond, allSecond⟩⟩
    exact ⟨⟨executableFirst, executableSecond⟩, fun c member => member.elim (allFirst c) (allSecond c)⟩

theorem Reaches.refl (store : Finset O) : Reaches label sys store store :=
  ⟨[], IsRun.nil store, rfl⟩

/-- What a store reached by a run reaches, the start of the run reaches. -/
theorem Reaches.of_run {store : Finset O} {run : List (Commit O R)}
    (isRun : IsRun label sys store run) {target : Finset O}
    (reaches : Reaches label sys (fireList store run) target) : Reaches label sys store target := by
  obtain ⟨more, isMore, eq⟩ := reaches
  exact ⟨run ++ more, isRun_append_iff.mpr ⟨isRun, isMore⟩, by rw [fireList_append, eq]⟩

/-- The end of a run is reached. -/
theorem Reaches.end {store : Finset O} {run : List (Commit O R)}
    (isRun : IsRun label sys store run) : Reaches label sys store (fireList store run) :=
  ⟨run, isRun, rfl⟩

/-- Conflict-freedom passes to every store a run reaches. -/
theorem ConflictFree.of_run {store : Finset O} (free : ConflictFree label sys store)
    {run : List (Commit O R)} (isRun : IsRun label sys store run) :
    ConflictFree label sys (fireList store run) :=
  fun t reaches => free t (Reaches.of_run isRun reaches)

theorem ConflictFree.after {store : Finset O} (free : ConflictFree label sys store)
    {c : Commit O R} (member : sys c) (enabled : Enabled label store c) :
    ConflictFree label sys (fire store c) := by
  have := free.of_run (run := [c]) (isRun_cons_iff.mpr ⟨member, enabled, IsRun.nil _⟩)
  simpa using this

/-- The first occurrence of an element splits a list. -/
theorem exists_first_split {α : Type*} {a : α} :
    ∀ {l : List α}, a ∈ l → ∃ pre post, l = pre ++ a :: post ∧ a ∉ pre
  | [], member => by simp at member
  | b :: rest, member => by
      rcases Classical.em (a = b) with same | other
      · exact ⟨[], rest, by simp [same], by simp⟩
      · obtain ⟨pre, post, eq, notIn⟩ := exists_first_split (List.mem_of_ne_of_mem other member)
        exact ⟨b :: pre, post, by simp [eq], by simp [notIn, other]⟩

/-! ## Keller's theorem for commits -/

/-- **Persistence.** In a conflict-free system, a commit enabled at the start stays enabled along
any run that does not fire it. -/
theorem ConflictFree.persists {store : Finset O} (free : ConflictFree label sys store)
    {d : Commit O R} (memberD : sys d) (enabledD : Enabled label store d)
    {run : List (Commit O R)} (isRun : IsRun label sys store run) (notIn : d ∉ run) :
    Enabled label (fireList store run) d := by
  induction run generalizing store with
  | nil => simpa using enabledD
  | cons c rest ih =>
      obtain ⟨memberC, enabledC, isRest⟩ := isRun_cons_iff.mp isRun
      have ne : d ≠ c := fun same => notIn (same ▸ List.mem_cons_self)
      have independent := free store (Reaches.refl store) d c memberD memberC ne enabledD enabledC
      have afterC : Enabled label (fire store c) d :=
        ((independent_iff_both_orders enabledD enabledC).mp independent).2
      exact ih (free.after memberC enabledC) afterC isRest
        (fun member => notIn (List.mem_cons_of_mem _ member))

/-- **Bubbling.** In a conflict-free system, a commit enabled at the start that fires later in a
run can fire first instead: the run with it moved to the front is a run and reaches the same
store. -/
theorem ConflictFree.bubble {store : Finset O} (free : ConflictFree label sys store)
    {d : Commit O R} (enabledD : Enabled label store d) {pre post : List (Commit O R)}
    (isRun : IsRun label sys store (pre ++ d :: post)) (notIn : d ∉ pre) :
    IsRun label sys store (d :: (pre ++ post)) ∧
      fireList store (d :: (pre ++ post)) = fireList store (pre ++ d :: post) := by
  induction pre generalizing store with
  | nil => exact ⟨by simpa using isRun, rfl⟩
  | cons c pre' ih =>
      rw [List.cons_append, isRun_cons_iff] at isRun
      obtain ⟨memberC, enabledC, isRest⟩ := isRun
      have memberD : sys d := isRest.2 d (by simp)
      have ne : d ≠ c := fun same => notIn (same ▸ List.mem_cons_self)
      have independent := free store (Reaches.refl store) d c memberD memberC ne enabledD enabledC
      obtain ⟨cAfterD, dAfterC⟩ := (independent_iff_both_orders enabledD enabledC).mp independent
      obtain ⟨isBubbled, sameStore⟩ :=
        ih (free.after memberC enabledC) dAfterC isRest
          (fun member => notIn (List.mem_cons_of_mem _ member))
      obtain ⟨_, _, isTail⟩ := isRun_cons_iff.mp isBubbled
      have comm : fire (fire store d) c = fire (fire store c) d := fire_comm enabledD enabledC
      refine ⟨isRun_cons_iff.mpr ⟨memberD, enabledD, isRun_cons_iff.mpr ⟨memberC, cAfterD, ?_⟩⟩, ?_⟩
      · rw [comm]; exact isTail
      · simp only [List.cons_append, fireList_cons] at sameStore ⊢
        rw [comm, sameStore]

/-- **Keller's theorem for commits.** In a conflict-free system, any two maximal runs from one
store fire the same commits, each as often, and end at the same store. -/
theorem ConflictFree.maximal_agree {store : Finset O} (free : ConflictFree label sys store)
    {first second : List (Commit O R)} (maxFirst : Maximal label sys store first)
    (maxSecond : Maximal label sys store second) :
    first.Perm second ∧ fireList store first = fireList store second := by
  induction first generalizing store second with
  | nil =>
      cases second with
      | nil => exact ⟨List.Perm.refl _, rfl⟩
      | cons d rest =>
          obtain ⟨memberD, enabledD, _⟩ := isRun_cons_iff.mp maxSecond.1
          exact absurd enabledD (maxFirst.2 d memberD)
  | cons c rest ih =>
      obtain ⟨memberC, enabledC, isRest⟩ := isRun_cons_iff.mp maxFirst.1
      rcases Classical.em (c ∈ second) with inSecond | notIn
      · obtain ⟨pre, post, rfl, notInPre⟩ := exists_first_split inSecond
        obtain ⟨isBubbled, sameStore⟩ := free.bubble enabledC maxSecond.1 notInPre
        obtain ⟨_, _, isTail⟩ := isRun_cons_iff.mp isBubbled
        have tailStore : fireList (fire store c) (pre ++ post) = fireList store (pre ++ c :: post) := by
          simpa using sameStore
        have maxTail : Maximal label sys (fire store c) (pre ++ post) :=
          ⟨isTail, by rw [tailStore]; exact maxSecond.2⟩
        have maxRest : Maximal label sys (fire store c) rest := ⟨isRest, by simpa using maxFirst.2⟩
        obtain ⟨perm, same⟩ := ih (free.after memberC enabledC) maxRest maxTail
        refine ⟨(perm.cons c).trans List.perm_middle.symm, ?_⟩
        simp only [fireList_cons]
        rw [same, tailStore]
      · exact absurd (free.persists memberC enabledC maxSecond.1 notIn) (maxSecond.2 c memberC)

/-- **Confluence of runs.** In a conflict-free system, any two runs from one store extend to runs
that fire the same commits and end at the same store. It says, for programs that never stop, that
no schedule loses what another reaches. -/
theorem ConflictFree.reconcile {store : Finset O} (free : ConflictFree label sys store)
    {first second : List (Commit O R)} (isFirst : IsRun label sys store first)
    (isSecond : IsRun label sys store second) :
    ∃ more₁ more₂, IsRun label sys store (first ++ more₁) ∧
      IsRun label sys store (second ++ more₂) ∧ (first ++ more₁).Perm (second ++ more₂) ∧
      fireList store (first ++ more₁) = fireList store (second ++ more₂) := by
  induction first generalizing store second with
  | nil =>
      exact ⟨second, [], by simpa using isSecond, by simpa using isSecond, by simp, by simp⟩
  | cons c rest ih =>
      obtain ⟨memberC, enabledC, isRest⟩ := isRun_cons_iff.mp isFirst
      rcases Classical.em (c ∈ second) with inSecond | notIn
      · obtain ⟨pre, post, rfl, notInPre⟩ := exists_first_split inSecond
        obtain ⟨isBubbled, sameStore⟩ := free.bubble enabledC isSecond notInPre
        obtain ⟨_, _, isTail⟩ := isRun_cons_iff.mp isBubbled
        have tailStore : fireList (fire store c) (pre ++ post) = fireList store (pre ++ c :: post) := by
          simpa using sameStore
        obtain ⟨more₁, more₂, run₁, run₂, perm, same⟩ := ih (free.after memberC enabledC) isRest isTail
        refine ⟨more₁, more₂, ?_, ?_, ?_, ?_⟩
        · rw [List.cons_append]; exact isRun_cons_iff.mpr ⟨memberC, enabledC, run₁⟩
        · rw [isRun_append_iff]
          refine ⟨isSecond, ?_⟩
          rw [← tailStore]
          exact (isRun_append_iff.mp run₂).2
        · rw [List.cons_append]
          refine (perm.cons c).trans ?_
          simp only [List.append_assoc, List.cons_append]
          exact List.perm_middle.symm
        · rw [List.cons_append, fireList_cons, same, fireList_append (fire store c) (pre ++ post) more₂,
            fireList_append store (pre ++ c :: post) more₂, tailStore]
      · have enabledAtEnd := free.persists memberC enabledC isSecond notIn
        have isSnoc : IsRun label sys store (second ++ [c]) :=
          isRun_append_iff.mpr ⟨isSecond, isRun_cons_iff.mpr ⟨memberC, enabledAtEnd, IsRun.nil _⟩⟩
        obtain ⟨isBubbled, sameStore⟩ := free.bubble enabledC isSnoc notIn
        simp only [List.append_nil] at isBubbled sameStore
        obtain ⟨_, _, isTail⟩ := isRun_cons_iff.mp isBubbled
        have snocStore : fireList (fire store c) second = fireList store (second ++ [c]) := by
          simpa using sameStore
        obtain ⟨more₁, more₂, run₁, run₂, perm, same⟩ :=
          ih (free.after memberC enabledC) isRest isTail
        refine ⟨more₁, c :: more₂, ?_, ?_, ?_, ?_⟩
        · rw [List.cons_append]; exact isRun_cons_iff.mpr ⟨memberC, enabledC, run₁⟩
        · have split : second ++ c :: more₂ = (second ++ [c]) ++ more₂ := by simp
          rw [split, isRun_append_iff]
          refine ⟨isSnoc, ?_⟩
          rw [← snocStore]
          exact (isRun_append_iff.mp run₂).2
        · rw [List.cons_append]
          exact (perm.cons c).trans List.perm_middle.symm
        · have split : second ++ c :: more₂ = (second ++ [c]) ++ more₂ := by simp
          rw [List.cons_append, fireList_cons, same, split, fireList_append (fire store c) second more₂,
            fireList_append store (second ++ [c]) more₂, snocStore]

end Runs

/-! ## Which facets conflict across processes -/

/-- Two facets **conflict** when one process holding the first and another holding the second at
one name can have commits that disturb each other: two receivers can take one occurrence; a
receiver can take what a peeker keeps; a receiver or a sender can change a region that an observer
queries. Sending against sending, receiving or peeking, and peeking or observing against peeking or
observing, never conflict. -/
def conflicts : Facet → Facet → Bool
  | .receive, .receive => true
  | .receive, .peek => true
  | .peek, .receive => true
  | .receive, .observe => true
  | .observe, .receive => true
  | .send, .observe => true
  | .observe, .send => true
  | _, _ => false

theorem conflicts_symm (f g : Facet) : conflicts f g = conflicts g f := by
  cases f <;> cases g <;> rfl

/-- A name is **safe** for a family of rights when no two different processes hold conflicting
facets there. -/
def SafeAt {ι : Type uI} {N : Type uN} (Γ : ι → Rights N) (n : N) : Prop :=
  ∀ p q, p ≠ q → ∀ f g, Γ p n f = true → Γ q n g = true → conflicts f g = false

section Names

variable {ι : Type uI} {N : Type uN}

/-- **A monotone name**: nobody receives or observes there. -/
def MonotoneAt (Γ : ι → Rights N) (n : N) : Prop :=
  ∀ p, Γ p n .receive = false ∧ Γ p n .observe = false

/-- **A Kahn name**: only the reader receives or peeks there, and nobody observes. The others may
only send. -/
def KahnAt (Γ : ι → Rights N) (n : N) (reader : ι) : Prop :=
  (∀ q, q ≠ reader → Γ q n .receive = false ∧ Γ q n .peek = false) ∧ ∀ q, Γ q n .observe = false

/-- **A private name**: only its owner holds any facet there. -/
def PrivateAt (Γ : ι → Rights N) (n : N) (owner : ι) : Prop :=
  ∀ q, q ≠ owner → ∀ f, Γ q n f = false

variable {Γ : ι → Rights N} {n : N}

theorem safeAt_of_monotoneAt (monotone : MonotoneAt Γ n) : SafeAt Γ n := by
  intro p q _ f g held held'
  obtain ⟨noReceiveP, noObserveP⟩ := monotone p
  obtain ⟨noReceiveQ, noObserveQ⟩ := monotone q
  cases f <;> cases g <;> simp_all [conflicts]

theorem safeAt_of_kahnAt {reader : ι} (kahn : KahnAt Γ n reader) : SafeAt Γ n := by
  intro p q ne f g held held'
  obtain ⟨others, noObserve⟩ := kahn
  have noObserveP := noObserve p
  have noObserveQ := noObserve q
  rcases Classical.em (p = reader) with rfl | otherP
  · have ⟨noReceiveQ, noPeekQ⟩ := others q (Ne.symm ne)
    cases f <;> cases g <;> simp_all [conflicts]
  · have ⟨noReceiveP, noPeekP⟩ := others p otherP
    cases f <;> cases g <;> simp_all [conflicts]

theorem safeAt_of_privateAt {owner : ι} (private_ : PrivateAt Γ n owner) : SafeAt Γ n := by
  intro p q ne f g held held'
  rcases Classical.em (p = owner) with rfl | otherP
  · rw [private_ q (Ne.symm ne) g] at held'; exact absurd held' (by decide)
  · rw [private_ p otherP f] at held; exact absurd held (by decide)

/-- If a name is not safe, two different processes hold conflicting facets there. -/
theorem exists_conflict_of_not_safe (notSafe : ¬ SafeAt Γ n) :
    ∃ p q, p ≠ q ∧ ∃ f g, Γ p n f = true ∧ Γ q n g = true ∧ conflicts f g = true := by
  unfold SafeAt at notSafe
  push Not at notSafe
  obtain ⟨p, q, ne, f, g, held, held', conflict⟩ := notSafe
  exact ⟨p, q, ne, f, g, held, held', by simpa using conflict⟩

end Names

/-! ## Different processes never disturb each other at safe names -/

section CrossProcess

variable {O : Type uO} [DecidableEq O] {R : Type uR} {N : Type uN} {ι : Type uI}
  {label : O → R} {loc : R → N} {Γ : ι → Rights N}

/-- **Independence across processes.** At safe names, formed commits of two different processes
that make apart identities are independent. -/
theorem independent_of_safe (safe : ∀ n, SafeAt Γ n) {p q : ι} (ne : p ≠ q) {c d : Commit O R}
    (formedC : FormedUnder label loc (Γ p) c) (formedD : FormedUnder label loc (Γ q) d)
    (madeApart : Disjoint c.made d.made) : Independent label c d := by
  have noConflict : ∀ {p q : ι}, p ≠ q → ∀ {m : N} {f g : Facet}, Γ p m f = true →
      Γ q m g = true → conflicts f g = false :=
    fun {p q} ne {m f g} held held' => safe m p q ne f g held held'
  refine ⟨?_, ?_, ?_⟩
  · rintro (taken | made)
    · obtain ⟨o, inC, inD⟩ := Finset.not_disjoint_iff.mp taken
      have := noConflict ne (formedC.taken o inC) (formedD.taken o inD)
      simp [conflicts] at this
    · exact made madeApart
  · rintro (kept | ⟨read, member, o, written, inRegion⟩)
    · obtain ⟨o, inC, inD⟩ := Finset.not_disjoint_iff.mp kept
      have := noConflict ne (formedC.taken o inC) (formedD.kept o inD)
      simp [conflicts] at this
    · have observes := formedD.queries read member (label o) inRegion
      rcases Finset.mem_union.mp written with taken | made
      · have := noConflict ne (formedC.taken o taken) observes
        simp [conflicts] at this
      · have := noConflict ne (formedC.made o made) observes
        simp [conflicts] at this
  · rintro (kept | ⟨read, member, o, written, inRegion⟩)
    · obtain ⟨o, inD, inC⟩ := Finset.not_disjoint_iff.mp kept
      have := noConflict (Ne.symm ne) (formedD.taken o inD) (formedC.kept o inC)
      simp [conflicts] at this
    · have observes := formedC.queries read member (label o) inRegion
      rcases Finset.mem_union.mp written with taken | made
      · have := noConflict (Ne.symm ne) (formedD.taken o taken) observes
        simp [conflicts] at this
      · have := noConflict (Ne.symm ne) (formedD.made o made) observes
        simp [conflicts] at this

/-- The commits of a system of processes: those of some process. -/
def systemOf (commits : ι → Commit O R → Prop) : Commit O R → Prop := fun c => ∃ p, commits p c

/-- A process is **determinate on its own** from a store: at every store the whole system reaches,
two distinct commits of the process that are both enabled there are independent. A sequential
process meets it when at most one of its commits is enabled at a time. -/
def LocallyDeterminate (label : O → R) (commits : ι → Commit O R → Prop) (store : Finset O)
    (p : ι) : Prop :=
  ∀ t, Reaches label (systemOf commits) store t → ∀ c d, commits p c → commits p d → c ≠ d →
    Enabled label t c → Enabled label t d → Independent label c d

/-- **The system theorem.** Safe names, located identities (commits of different processes make
apart identities), and processes each determinate on its own make the system conflict-free. -/
theorem conflictFree_of_safe {commits : ι → Commit O R → Prop} {store : Finset O}
    (safe : ∀ n, SafeAt Γ n) (formed : ∀ p c, commits p c → FormedUnder label loc (Γ p) c)
    (located : ∀ p q c d, p ≠ q → commits p c → commits q d → Disjoint c.made d.made)
    (locally : ∀ p, LocallyDeterminate label commits store p) :
    ConflictFree label (systemOf commits) store := by
  rintro t reaches c d ⟨p, inP⟩ ⟨q, inQ⟩ ne enabledC enabledD
  rcases Classical.em (p = q) with rfl | other
  · exact locally p t reaches c d inP inQ ne enabledC enabledD
  · exact independent_of_safe safe other (formed p c inP) (formed q d inQ)
      (located p q c d other inP inQ)

/-- **Determinism from capabilities.** Under the hypotheses of the system theorem, maximal runs fire
the same commits and end at the same store, and any two runs reconcile. -/
theorem determinate_of_safe {commits : ι → Commit O R → Prop} {store : Finset O}
    (safe : ∀ n, SafeAt Γ n) (formed : ∀ p c, commits p c → FormedUnder label loc (Γ p) c)
    (located : ∀ p q c d, p ≠ q → commits p c → commits q d → Disjoint c.made d.made)
    (locally : ∀ p, LocallyDeterminate label commits store p) :
    (∀ first second, Maximal label (systemOf commits) store first →
        Maximal label (systemOf commits) store second →
        first.Perm second ∧ fireList store first = fireList store second) ∧
      (∀ first second, IsRun label (systemOf commits) store first →
        IsRun label (systemOf commits) store second →
        ∃ more₁ more₂, IsRun label (systemOf commits) store (first ++ more₁) ∧
          IsRun label (systemOf commits) store (second ++ more₂) ∧
          (first ++ more₁).Perm (second ++ more₂) ∧
          fireList store (first ++ more₁) = fireList store (second ++ more₂)) := by
  have free := conflictFree_of_safe safe formed located locally
  exact ⟨fun _ _ maxFirst maxSecond => free.maximal_agree maxFirst maxSecond,
    fun _ _ isFirst isSecond => free.reconcile isFirst isSecond⟩

end CrossProcess

/-! ## CALM: monotone systems need no condition on processes -/

section Calm

variable {O : Type uO} [DecidableEq O] {R : Type uR} {label : O → R} {sys : Commit O R → Prop}

/-- Two monotone commits that make apart identities are independent. -/
theorem independent_of_monotone {c d : Commit O R} (monotoneC : c.Monotone)
    (monotoneD : d.Monotone) (madeApart : Disjoint c.made d.made) : Independent label c d := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (taken | made)
    · exact taken (by rw [monotoneC.1]; exact Finset.disjoint_empty_left _)
    · exact made madeApart
  · rintro (kept | ⟨read, member, _⟩)
    · exact kept (by rw [monotoneC.1]; exact Finset.disjoint_empty_left _)
    · rw [monotoneD.2] at member; simp at member
  · rintro (kept | ⟨read, member, _⟩)
    · exact kept (by rw [monotoneD.1]; exact Finset.disjoint_empty_left _)
    · rw [monotoneC.2] at member; simp at member

/-- **CALM for commits.** A system of monotone commits (none takes, none queries) whose distinct
commits make apart identities is conflict-free from every store, whatever its processes are: no
coordination and no determinacy of any process is needed. -/
theorem conflictFree_of_monotone (monotone : ∀ c, sys c → c.Monotone)
    (located : ∀ c d, sys c → sys d → c ≠ d → Disjoint c.made d.made) (store : Finset O) :
    ConflictFree label sys store :=
  fun _ _ c d memberC memberD ne _ _ =>
    independent_of_monotone (monotone c memberC) (monotone d memberD)
      (located c d memberC memberD ne)

end Calm

/-! ## The profiles of regions

A region profile names the facets of the region's holder and the most a handed-out handle may
carry (the kernel's profile table). With one holder and handed-out handles held by two or more
other processes, the region's name is safe exactly when no holder facet conflicts with a handed-out
facet and no two handed-out facets conflict. -/

namespace Profiles

/-- A region profile: the holder's facets, and the facets a handed-out handle may carry. -/
structure Profile where
  holder : Facet → Bool
  delegable : Facet → Bool

/-- The four facets. -/
def allFacets : List Facet := [.send, .receive, .peek, .observe]

theorem mem_allFacets (f : Facet) : f ∈ allFacets := by cases f <;> simp [allFacets]

/-- The rights at the region's name of three processes: process `0` holds the region, and
processes `1` and `2` each hold a handed-out handle with every delegable facet. -/
def rightsOf (P : Profile) : Fin 3 → Rights Unit :=
  fun p _ => if p = 0 then P.holder else P.delegable

/-- A profile is **safe** when no holder facet conflicts with a delegable one and no two delegable
facets conflict. -/
def Profile.safe (P : Profile) : Bool :=
  allFacets.all fun f => allFacets.all fun g =>
    !(P.holder f && P.delegable g && conflicts f g) && !(P.delegable f && P.delegable g && conflicts f g)

/-- **The profile check is exact**: a profile is safe exactly when its region's name is safe for one
holder and two other processes with handed-out handles. -/
theorem safe_iff (P : Profile) : P.safe = true ↔ SafeAt (rightsOf P) () := by
  constructor
  · intro safe p q ne f g held held'
    have check := List.all_eq_true.mp (List.all_eq_true.mp safe f (mem_allFacets f)) g
      (mem_allFacets g)
    simp only [rightsOf] at held held'
    by_cases hp : p = 0
    · have hq : q ≠ 0 := fun hq => ne (hp.trans hq.symm)
      simp only [hp, ↓reduceIte, hq] at held held'
      simp_all
    · by_cases hq : q = 0
      · simp only [hp, ↓reduceIte, hq] at held held'
        have check' := List.all_eq_true.mp (List.all_eq_true.mp safe g (mem_allFacets g)) f
          (mem_allFacets f)
        rw [conflicts_symm]
        simp_all
      · simp only [hp, ↓reduceIte, hq] at held held'
        simp_all
  · intro safe
    refine List.all_eq_true.mpr fun f _ => List.all_eq_true.mpr fun g _ => ?_
    have holderVsOther := safe 0 1 (by decide) f g
    have otherVsOther := safe 1 2 (by decide) f g
    simp only [rightsOf, ↓reduceIte, show (1 : Fin 3) ≠ 0 by decide,
      show (2 : Fin 3) ≠ 0 by decide] at holderVsOther otherVsOther
    cases hh : P.holder f <;> cases hd : P.delegable f <;> cases hg : P.delegable g <;>
      cases hc : conflicts f g <;> simp_all

/-- Facet sets as functions. -/
def facets (send receive peek observe : Bool) : Facet → Bool
  | .send => send
  | .receive => receive
  | .peek => peek
  | .observe => observe

/-- `space`: every facet, all of them handed out. -/
def space : Profile := ⟨facets true true true true, facets true true true true⟩
/-- `channel`: receive, peek and send, all of them handed out. -/
def channel : Profile := ⟨facets true true true false, facets true true true false⟩
/-- `mailbox`: the holder has every facet; handed out, only send. -/
def mailbox : Profile := ⟨facets true true true true, facets true false false false⟩
/-- `log`: peek, send and observe; handed out, peek and send. -/
def log : Profile := ⟨facets true false true true, facets true false true false⟩
/-- `board`: send, peek and observe; handed out, only peek. -/
def board : Profile := ⟨facets true false true true, facets false false true false⟩

/-- A mailbox whose holder never observes. -/
def quietMailbox : Profile := ⟨facets true true true false, facets true false false false⟩
/-- A log whose holder never observes: a monotone region. -/
def quietLog : Profile := ⟨facets true false true false, facets true false true false⟩
/-- A channel handed out with `send` alone: a Kahn channel. -/
def sendOnlyChannel : Profile := ⟨facets true true true false, facets true false false false⟩

/-- **A board is safe**: one writer that observes, readers that peek. -/
theorem board_safe : SafeAt (rightsOf board) () := (safe_iff board).mp (by decide)

/-- **A space is not safe**: two receivers, among other pairs. -/
theorem space_not_safe : ¬ SafeAt (rightsOf space) () := fun safe =>
  absurd ((safe_iff space).mpr safe) (by decide)

/-- **A channel is not safe**: two handed-out receivers compete. -/
theorem channel_not_safe : ¬ SafeAt (rightsOf channel) () := fun safe =>
  absurd ((safe_iff channel).mpr safe) (by decide)

/-- **A mailbox is not safe**: the holder's predicate query races with the senders. -/
theorem mailbox_not_safe : ¬ SafeAt (rightsOf mailbox) () := fun safe =>
  absurd ((safe_iff mailbox).mpr safe) (by decide)

/-- **A log is not safe**: the holder's predicate query races with the appenders. -/
theorem log_not_safe : ¬ SafeAt (rightsOf log) () := fun safe =>
  absurd ((safe_iff log).mpr safe) (by decide)

/-- **A mailbox whose holder never observes is safe**: a Kahn region. -/
theorem quietMailbox_safe : SafeAt (rightsOf quietMailbox) () := (safe_iff quietMailbox).mp (by decide)

/-- **A log whose holder never observes is safe**: a monotone region. -/
theorem quietLog_safe : SafeAt (rightsOf quietLog) () := (safe_iff quietLog).mp (by decide)

/-- **A channel handed out with `send` alone is safe.** -/
theorem sendOnlyChannel_safe : SafeAt (rightsOf sendOnlyChannel) () :=
  (safe_iff sendOnlyChannel).mp (by decide)

end Profiles

/-! ## The criterion is exact

If a name is not safe, there is a determinacy failure using nothing but the conflicting facets: a
system of two processes, each with one commit formed under its rights at that name, with apart
identities, has two maximal runs that are not permutations of each other. Each process alone is
trivially determinate, so the failure is the unsafe name's. Occurrences carry the label `()` and
lie at the name. -/

section Exact

variable {ι : Type uI} {N : Type uN} {Γ : ι → Rights N} {n : N}

/-- The one-label model of a name: every occurrence lies at `n`. -/
def atName (_ : ℕ) : Unit := ()

/-- The region of everything at the name. -/
def everything (_ : Unit) : Bool := true

/-- Take the occurrences `X`. -/
def takeAll (X : Finset ℕ) : Commit ℕ Unit := ⟨X, ∅, ∅, []⟩
/-- Keep the occurrences `X`. -/
def keepAll (X : Finset ℕ) : Commit ℕ Unit := ⟨∅, X, ∅, []⟩
/-- Make the occurrences `X`. -/
def makeAll (X : Finset ℕ) : Commit ℕ Unit := ⟨∅, ∅, X, []⟩
/-- Query that the name holds exactly `X`. -/
def queryIs (X : Finset ℕ) : Commit ℕ Unit := ⟨∅, ∅, ∅, [⟨everything, X⟩]⟩

theorem formed_takeAll {Γ' : Rights N} (held : Γ' n .receive = true) (X : Finset ℕ) :
    FormedUnder atName (fun _ => n) Γ' (takeAll X) where
  taken _ _ := held
  kept _ member := by simp [takeAll] at member
  made _ member := by simp [takeAll] at member
  queries _ member := by simp [takeAll] at member

theorem formed_keepAll {Γ' : Rights N} (held : Γ' n .peek = true) (X : Finset ℕ) :
    FormedUnder atName (fun _ => n) Γ' (keepAll X) where
  taken _ member := by simp [keepAll] at member
  kept _ _ := held
  made _ member := by simp [keepAll] at member
  queries _ member := by simp [keepAll] at member

theorem formed_makeAll {Γ' : Rights N} (held : Γ' n .send = true) (X : Finset ℕ) :
    FormedUnder atName (fun _ => n) Γ' (makeAll X) where
  taken _ member := by simp [makeAll] at member
  kept _ member := by simp [makeAll] at member
  made _ _ := held
  queries _ member := by simp [makeAll] at member

theorem formed_queryIs {Γ' : Rights N} (held : Γ' n .observe = true) (X : Finset ℕ) :
    FormedUnder atName (fun _ => n) Γ' (queryIs X) where
  taken _ member := by simp [queryIs] at member
  kept _ member := by simp [queryIs] at member
  made _ member := by simp [queryIs] at member
  queries _ _ _ _ := held

/-- The system of two commits. -/
def pair (c d : Commit ℕ Unit) : Commit ℕ Unit → Prop := fun e => e = c ∨ e = d

/-- Maximality of a concrete run, from enabling checks. -/
theorem maximal_pair {c d : Commit ℕ Unit} {store : Finset ℕ} {run : List (Commit ℕ Unit)}
    (executable : Executable atName store run) (inPair : ∀ e ∈ run, e = c ∨ e = d)
    (stopC : ¬ Enabled atName (fireList store run) c)
    (stopD : ¬ Enabled atName (fireList store run) d) : Maximal atName (pair c d) store run :=
  ⟨⟨executable, inPair⟩, fun e member => by rcases member with rfl | rfl <;> assumption⟩

/-- **Exactness of the safe-name criterion.** If a name is not safe, two processes with one formed
commit each, located identities and no other structure, have two maximal runs from one store that
are not permutations of each other. -/
theorem exists_not_perm_of_not_safe (notSafe : ¬ SafeAt Γ n) :
    ∃ p q, p ≠ q ∧ ∃ (c d : Commit ℕ Unit) (store : Finset ℕ) (first second : List (Commit ℕ Unit)),
      FormedUnder atName (fun _ => n) (Γ p) c ∧ FormedUnder atName (fun _ => n) (Γ q) d ∧
      Disjoint c.made d.made ∧ Maximal atName (pair c d) store first ∧
      Maximal atName (pair c d) store second ∧ ¬ first.Perm second := by
  obtain ⟨p, q, ne, f, g, held, held', conflict⟩ := exists_conflict_of_not_safe notSafe
  refine ⟨p, q, ne, ?_⟩
  cases f <;> cases g <;> simp [conflicts] at conflict
  · -- send at p, observe at q: the query of emptiness races with the make
    refine ⟨makeAll {0}, queryIs ∅, ∅, [makeAll {0}], [queryIs ∅, makeAll {0}],
      formed_makeAll held _, formed_queryIs held' _, by decide, ?_, ?_, ?_⟩
    · exact maximal_pair (.cons (by decide) (.nil _)) (by simp) (by decide) (by decide)
    · exact maximal_pair (.cons (by decide) (.cons (by decide) (.nil _))) (by simp)
        (by decide) (by decide)
    · intro perm; have := perm.length_eq; simp at this
  · -- receive at both: two takers of one occurrence
    refine ⟨takeAll {0, 1}, takeAll {0}, {0, 1}, [takeAll {0, 1}], [takeAll {0}],
      formed_takeAll held _, formed_takeAll held' _, by decide, ?_, ?_, ?_⟩
    · exact maximal_pair (.cons (by decide) (.nil _)) (by simp) (by decide) (by decide)
    · exact maximal_pair (.cons (by decide) (.nil _)) (by simp) (by decide) (by decide)
    · intro perm
      have member := perm.mem_iff.mp (List.mem_singleton_self (takeAll {0, 1}))
      rw [List.mem_singleton] at member
      exact absurd (congrArg Commit.taken member) (by decide)
  · -- receive at p, peek at q: the take races with the keep
    refine ⟨takeAll {0}, keepAll {0}, {0}, [takeAll {0}], [keepAll {0}, takeAll {0}],
      formed_takeAll held _, formed_keepAll held' _, by decide, ?_, ?_, ?_⟩
    · exact maximal_pair (.cons (by decide) (.nil _)) (by simp) (by decide) (by decide)
    · exact maximal_pair (.cons (by decide) (.cons (by decide) (.nil _))) (by simp)
        (by decide) (by decide)
    · intro perm; have := perm.length_eq; simp at this
  · -- receive at p, observe at q: the take races with the query
    refine ⟨takeAll {0}, queryIs {0}, {0}, [takeAll {0}], [queryIs {0}, takeAll {0}],
      formed_takeAll held _, formed_queryIs held' _, by decide, ?_, ?_, ?_⟩
    · exact maximal_pair (.cons (by decide) (.nil _)) (by simp) (by decide) (by decide)
    · exact maximal_pair (.cons (by decide) (.cons (by decide) (.nil _))) (by simp)
        (by decide) (by decide)
    · intro perm; have := perm.length_eq; simp at this
  · -- peek at p, receive at q
    refine ⟨keepAll {0}, takeAll {0}, {0}, [takeAll {0}], [keepAll {0}, takeAll {0}],
      formed_keepAll held _, formed_takeAll held' _, by decide, ?_, ?_, ?_⟩
    · exact maximal_pair (.cons (by decide) (.nil _)) (by simp) (by decide) (by decide)
    · exact maximal_pair (.cons (by decide) (.cons (by decide) (.nil _))) (by simp)
        (by decide) (by decide)
    · intro perm; have := perm.length_eq; simp at this
  · -- observe at p, send at q
    refine ⟨queryIs ∅, makeAll {0}, ∅, [makeAll {0}], [queryIs ∅, makeAll {0}],
      formed_queryIs held _, formed_makeAll held' _, by decide, ?_, ?_, ?_⟩
    · exact maximal_pair (.cons (by decide) (.nil _)) (by simp) (by decide) (by decide)
    · exact maximal_pair (.cons (by decide) (.cons (by decide) (.nil _))) (by simp)
        (by decide) (by decide)
    · intro perm; have := perm.length_eq; simp at this
  · -- observe at p, receive at q
    refine ⟨queryIs {0}, takeAll {0}, {0}, [takeAll {0}], [queryIs {0}, takeAll {0}],
      formed_queryIs held _, formed_takeAll held' _, by decide, ?_, ?_, ?_⟩
    · exact maximal_pair (.cons (by decide) (.nil _)) (by simp) (by decide) (by decide)
    · exact maximal_pair (.cons (by decide) (.cons (by decide) (.nil _))) (by simp)
        (by decide) (by decide)
    · intro perm; have := perm.length_eq; simp at this

end Exact

/-! ## Controls -/

namespace Controls

/-- The labels of the controls: control tokens, messages, and log entries recording a position and
a value. -/
inductive Cell where
  | token (state : ℕ)
  | message (value : ℕ)
  | entry (position value : ℕ)
  deriving DecidableEq, Repr

/-- Identities and their labels: `0`, `3`, `4` are the reader's control tokens; `1` and `2` the two
messages; `10 + 10 * v + p` records value `v` at position `p`. -/
def label : ℕ → Cell
  | 0 => .token 0
  | 1 => .message 1
  | 2 => .message 2
  | 3 => .token 1
  | 4 => .token 2
  | k => .entry ((k - 10) % 10) ((k - 10) / 10)

/-! ### The condition that each process be determinate on its own -/

/-- The reader takes message `1` first: it writes value `1` at position `0` (identity `20`). -/
def firstOne : Commit ℕ Cell := ⟨{0, 1}, ∅, {3, 20}, []⟩
/-- Then message `2`, at position `1` (identity `31`). -/
def thenTwo : Commit ℕ Cell := ⟨{3, 2}, ∅, {4, 31}, []⟩
/-- Or the reader takes message `2` first, at position `0` (identity `30`). -/
def firstTwo : Commit ℕ Cell := ⟨{0, 2}, ∅, {3, 30}, []⟩
/-- Then message `1`, at position `1` (identity `21`). -/
def thenOne : Commit ℕ Cell := ⟨{3, 1}, ∅, {4, 21}, []⟩

/-- The reader: one process taking from a bag in either order. -/
def reader : Commit ℕ Cell → Prop :=
  fun c => c = firstOne ∨ c = thenTwo ∨ c = firstTwo ∨ c = thenOne

theorem reader_terminal_one : Terminal label reader ({4, 20, 31} : Finset ℕ) := by
  rintro c (rfl | rfl | rfl | rfl) <;> decide

theorem reader_terminal_two : Terminal label reader ({4, 30, 21} : Finset ℕ) := by
  rintro c (rfl | rfl | rfl | rfl) <;> decide

/-- **Negative control, the reader's own choice.** One process, so every name is private to it and
safe, and it makes nothing another process makes; but it takes either message first, and its log
shows the order: two maximal runs end at different stores. -/
theorem unordered_reader :
    Maximal label reader {0, 1, 2} [firstOne, thenTwo] ∧
      Maximal label reader {0, 1, 2} [firstTwo, thenOne] ∧
      fireList ({0, 1, 2} : Finset ℕ) [firstOne, thenTwo] ≠
        fireList ({0, 1, 2} : Finset ℕ) [firstTwo, thenOne] := by
  have storeOne : fireList ({0, 1, 2} : Finset ℕ) [firstOne, thenTwo] = {4, 20, 31} := by decide
  have storeTwo : fireList ({0, 1, 2} : Finset ℕ) [firstTwo, thenOne] = {4, 30, 21} := by decide
  refine ⟨⟨⟨.cons (by decide) (.cons (by decide) (.nil _)), by simp [reader]⟩, ?_⟩,
    ⟨⟨.cons (by decide) (.cons (by decide) (.nil _)), by simp [reader]⟩, ?_⟩, ?_⟩
  · rw [storeOne]; exact reader_terminal_one
  · rw [storeTwo]; exact reader_terminal_two
  · rw [storeOne, storeTwo]; decide

/-- The reader is not determinate on its own: its two first commits are both enabled at the start
and clash on its control token. -/
theorem reader_not_conflictFree : ¬ ConflictFree label reader {0, 1, 2} := by
  intro free
  have := free _ (Reaches.refl _) firstOne firstTwo (by simp [reader]) (by simp [reader])
    (fun same => absurd (congrArg Commit.taken same) (by decide)) (by decide) (by decide)
  exact this.1 (Or.inl (by decide))

/-! ### Competing consumers: a shared `receive` -/

/-- Worker `a` takes the job (identity `1`) and records it (identity `40`). -/
def workerA : Commit ℕ Cell := ⟨{1}, ∅, {40}, []⟩
/-- Worker `b` takes the same job and records it (identity `50`). -/
def workerB : Commit ℕ Cell := ⟨{1}, ∅, {50}, []⟩

/-- **Negative control, competing consumers.** Two workers each take the one job: two maximal runs
end at different stores. -/
theorem competing_consumers :
    Maximal label (fun c => c = workerA ∨ c = workerB) {1} [workerA] ∧
      Maximal label (fun c => c = workerA ∨ c = workerB) {1} [workerB] ∧
      fireList ({1} : Finset ℕ) [workerA] ≠ fireList ({1} : Finset ℕ) [workerB] := by
  refine ⟨⟨⟨.cons (by decide) (.nil _), by simp⟩, ?_⟩, ⟨⟨.cons (by decide) (.nil _), by simp⟩, ?_⟩,
    by decide⟩
  · rintro c (rfl | rfl) <;> decide
  · rintro c (rfl | rfl) <;> decide

/-! ### Located identities -/

/-- Maker `a` makes identities `0` and `5`. -/
def makerA : Commit ℕ Cell := ⟨∅, ∅, {0, 5}, []⟩
/-- Maker `b` makes identities `0` and `6`. -/
def makerB : Commit ℕ Cell := ⟨∅, ∅, {0, 6}, []⟩

/-- **Negative control, a shared allocator.** Two monotone makers claim identity `0`: whichever runs
first wins it, and two maximal runs end at different stores. A shared allocator is a shared take in
disguise; located identities rule it out. -/
theorem shared_allocator :
    makerA.Monotone ∧ makerB.Monotone ∧
      Maximal label (fun c => c = makerA ∨ c = makerB) ∅ [makerA] ∧
      Maximal label (fun c => c = makerA ∨ c = makerB) ∅ [makerB] ∧
      fireList (∅ : Finset ℕ) [makerA] ≠ fireList (∅ : Finset ℕ) [makerB] := by
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨⟨.cons (by decide) (.nil _), by simp⟩, ?_⟩,
    ⟨⟨.cons (by decide) (.nil _), by simp⟩, ?_⟩, by decide⟩
  · rintro c (rfl | rfl) <;> decide
  · rintro c (rfl | rfl) <;> decide

/-! ### Positive controls -/

/-- Three monotone derivations of a closure: each reads facts and adds one fact with its own
identity. -/
def deriveA : Commit ℕ Cell := ⟨∅, {1}, {41}, []⟩
def deriveB : Commit ℕ Cell := ⟨∅, {2}, {42}, []⟩
def deriveC : Commit ℕ Cell := ⟨∅, {41, 42}, {43}, []⟩

/-- The closure system. -/
def closure : Commit ℕ Cell → Prop := fun c => c = deriveA ∨ c = deriveB ∨ c = deriveC

/-- **Positive control, CALM.** The closure is conflict-free: its maximal runs agree. -/
theorem calm_closure : ConflictFree label closure {1, 2} := by
  refine conflictFree_of_monotone ?_ ?_ _
  · rintro c (rfl | rfl | rfl) <;> exact ⟨rfl, rfl⟩
  · rintro c d (rfl | rfl | rfl) (rfl | rfl | rfl) ne <;> first | exact absurd rfl ne | decide

/-- Two maximal runs of the closure, in different orders, agree. -/
theorem calm_closure_agrees :
    fireList ({1, 2} : Finset ℕ) [deriveA, deriveB, deriveC] =
      fireList ({1, 2} : Finset ℕ) [deriveB, deriveA, deriveC] := by
  have maxFirst : Maximal label closure {1, 2} [deriveA, deriveB, deriveC] := by
    refine ⟨⟨.cons (by decide) (.cons (by decide) (.cons (by decide) (.nil _))),
      by simp [closure]⟩, ?_⟩
    rintro c (rfl | rfl | rfl) <;> decide
  have maxSecond : Maximal label closure {1, 2} [deriveB, deriveA, deriveC] := by
    refine ⟨⟨.cons (by decide) (.cons (by decide) (.cons (by decide) (.nil _))),
      by simp [closure]⟩, ?_⟩
    rintro c (rfl | rfl | rfl) <;> decide
  exact (calm_closure.maximal_agree maxFirst maxSecond).2

/-- The names of the pipeline: the channel, and the reader's output. -/
inductive PipeName where
  | channel
  | output
  deriving DecidableEq, Repr

/-- Where an item lies: messages on the channel, everything else in the output. -/
def pipeLoc : Cell → PipeName
  | .message _ => .channel
  | _ => .output

/-- The two processes of the pipeline: the writer (`false`) sends on the channel; the reader
(`true`) receives on the channel and sends to its output. -/
def pipeRights : Bool → Rights PipeName
  | false, .channel, .send => true
  | true, .channel, .receive => true
  | true, .output, .send => true
  | _, _, _ => false

/-- The writer sends message `1`. -/
def write : Commit ℕ Cell := ⟨∅, ∅, {1}, []⟩
/-- The reader takes it and records it. -/
def readOne : Commit ℕ Cell := ⟨{1}, ∅, {20}, []⟩

/-- The commits of each process. -/
def pipeCommits : Bool → Commit ℕ Cell → Prop
  | false, c => c = write
  | true, c => c = readOne

/-- The channel is a Kahn name and the output is private to the reader. -/
theorem pipe_safe : ∀ m, SafeAt pipeRights m := by
  intro m
  cases m
  · exact safeAt_of_kahnAt (reader := true)
      ⟨fun q ne => by cases q <;> simp_all [pipeRights], fun q => by cases q <;> rfl⟩
  · exact safeAt_of_privateAt (owner := true) fun q ne f => by
      cases q <;> cases f <;> simp_all [pipeRights]

/-- **Positive control, a Kahn pipeline.** A writer and a reader over a Kahn channel are
conflict-free, by the system theorem. -/
theorem kahn_pipeline : ConflictFree label (systemOf pipeCommits) ∅ := by
  refine conflictFree_of_safe (loc := pipeLoc) pipe_safe ?_ ?_ ?_
  · intro p c member
    cases p
    · cases member
      exact ⟨fun _ member => by simp [write] at member, fun _ member => by simp [write] at member,
        fun o member => by simp [write] at member; subst member; rfl,
        fun _ member => by simp [write] at member⟩
    · cases member
      exact ⟨fun o member => by simp [readOne] at member; subst member; rfl,
        fun _ member => by simp [readOne] at member,
        fun o member => by simp [readOne] at member; subst member; rfl,
        fun _ member => by simp [readOne] at member⟩
  · intro p q c d ne inP inQ
    cases p <;> cases q <;> simp_all [pipeCommits] <;> decide
  · intro p t _ c d inP inQ ne
    cases p <;> simp_all [pipeCommits]

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs
