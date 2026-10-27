import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ChannelAddressing

/-!
# For-each as a persistent receive on a private channel

A collection becomes a fresh channel holding its elements, one occurrence each. A persistent
receiver sits on the channel. Each firing takes one element, keeps the receiver, and makes the
body's results. This module proves that this is a loop with the right laws.

* **Each element fires exactly once, in any order** (`loop_every_order`, `loop_maximal_iff`,
  `executable_loop_nodup`): the firings on distinct elements are pairwise independent, so every
  order of them executes and reaches one store; a run of firings can take an element only once;
  and a run is maximal (no firing enabled) exactly when it has fired every element.
* **Nothing outside the scope can change the iteration** (`elements_fireList_outside`): commits
  of processes that do not hold the channel's name neither add nor remove elements.
* **The same laws for runs that interleave the loop with outsiders** (`interleaved_elements`,
  `interleaved_unfired_enabled`, `interleaved_maximal_iff`): an outsider holds no name of the
  channel, and the identities it makes are allocated apart from the loop's results (`Outsider`).
  Along every interleaved run no element fires twice, the elements left are those not fired,
  every element not fired can still fire, and the loop has nothing left to fire exactly when it
  has fired every element. The allocation is needed: an outsider that makes a result's identity
  stalls the loop (`Controls.squatter_stalls_loop`), and it is not an outsider in this sense
  (`Controls.squatter_not_outsider`).
* **The end of the loop** (`exhausted_stays_exhausted`, `exhausted_runs_are_outside`,
  `receiver_garbage`): once the channel holds no element, no firing is ever enabled again,
  whatever outsiders do, and every interleaved run from there is a run of outsiders. The receiver
  is unobservable to outsiders at every store, so a store with it and a store without it run
  every outside process alike; at exhaustion the loop no longer uses it either, which is the
  ν-garbage law and what "the loop ends" means.
* **On a public channel an injected element changes the outcomes**
  (`Controls.public_channel_injection`): a holder of the name adds an element and the loop
  fires on it, reaching a store the private loop cannot reach.

The iteration is a bag: decision §11 gives no order, and an ordered loop needs a protocol (a
counter or a linked list of elements) or an order observer. With the body's results kept off the
channel, the loop cannot feed itself.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v w

variable {O : Type u} [DecidableEq O] {R : Type v} {N : Type w} [DecidableEq N]

section Loop

variable (label : O → R) (loc : R → N) (channel : N) (receiver : O) (body : O → Finset O)

/-- One firing of the loop: take the element, keep the receiver, make the body's results. -/
def loopFire (R : Type v) (receiver : O) (body : O → Finset O) (o : O) : Commit O R :=
  ⟨{o}, {receiver}, body o, []⟩

/-- The names at the channel. -/
def atChannel (n : N) : Bool := decide (n = channel)

/-- The elements of a store: the occurrences at the channel other than the receiver. -/
def elements (store : Finset O) : Finset O :=
  (restrict label loc (atChannel channel) store).erase receiver

/-- The setting of a loop over a start store. -/
structure LoopSetup (start : Finset O) : Prop where
  receiver_mem : receiver ∈ start
  receiver_at : loc (label receiver) = channel
  body_fresh : ∀ o, Disjoint (body o) start
  body_apart : ∀ o o', o ≠ o' → Disjoint (body o) (body o')
  body_off_channel : ∀ o, ∀ x ∈ body o, loc (label x) ≠ channel

variable {label loc channel receiver body}

theorem mem_elements {store : Finset O} {o : O} :
    o ∈ elements label loc channel receiver store ↔
      o ∈ store ∧ loc (label o) = channel ∧ o ≠ receiver := by
  simp only [elements, Finset.mem_erase, mem_restrict, atChannel, decide_eq_true_eq]
  tauto

omit [DecidableEq O] [DecidableEq N] in
theorem loopFire_enabled_iff {store : Finset O} {o : O} :
    Enabled label store (loopFire R receiver body o) ↔
      o ∈ store ∧ receiver ∈ store ∧ o ≠ receiver ∧ Disjoint (body o) store := by
  constructor
  · intro enabled
    exact ⟨enabled.taken_subset (by simp [loopFire]), enabled.kept_subset (by simp [loopFire]),
      fun equal => by have := enabled.apart; simp [loopFire, equal] at this, enabled.fresh⟩
  · rintro ⟨member, receiverIn, different, fresh⟩
    exact ⟨by simpa [loopFire] using member, by simpa [loopFire] using receiverIn,
      by simpa [loopFire] using different, fresh, by simp [loopFire]⟩

omit [DecidableEq N] in
/-- Firings on distinct elements of the start store are independent. -/
theorem loopFire_independent (apart : ∀ o o', o ≠ o' → Disjoint (body o) (body o'))
    {o o' : O} (different : o ≠ o')
    (notReceiver : o ≠ receiver) (notReceiver' : o' ≠ receiver) :
    Independent label (loopFire R receiver body o) (loopFire R receiver body o') := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (taken | made)
    · exact taken (by simp [loopFire, different])
    · exact made (apart o o' different)
  · rintro (kept | ⟨read, member, -⟩)
    · exact kept (by simp [loopFire, notReceiver])
    · simp [loopFire] at member
  · rintro (kept | ⟨read, member, -⟩)
    · exact kept (by simp [loopFire, notReceiver'])
    · simp [loopFire] at member

/-- **Every order of firings on distinct elements executes**, and reaches one store. -/
theorem loop_every_order {start : Finset O} (setup : LoopSetup label loc channel receiver body start)
    {l : List O} (nodup : l.Nodup) (inElements : ∀ o ∈ l, o ∈ elements label loc channel receiver start) :
    Executable label start (l.map (loopFire R receiver body)) := by
  have member : ∀ o ∈ l, o ∈ start ∧ loc (label o) = channel ∧ o ≠ receiver := fun o inL =>
    mem_elements.mp (inElements o inL)
  refine executable_of_pairwise_independent ?_ ?_
  · intro c inMap
    obtain ⟨o, inL, rfl⟩ := List.mem_map.mp inMap
    exact loopFire_enabled_iff.mpr ⟨(member o inL).1, setup.receiver_mem, (member o inL).2.2,
      setup.body_fresh o⟩
  · refine List.pairwise_map.mpr (List.Pairwise.imp_of_mem (fun {o o'} inO inO' different => ?_) nodup)
    exact loopFire_independent setup.body_apart different (member o inO).2.2 (member o' inO').2.2

theorem loopFires_enabled {start : Finset O} (setup : LoopSetup label loc channel receiver body start)
    {l : List O} (inElements : ∀ o ∈ l, o ∈ elements label loc channel receiver start) :
    ∀ c ∈ l.map (loopFire R receiver body), Enabled label start c := by
  intro c inMap
  obtain ⟨o, inL, rfl⟩ := List.mem_map.mp inMap
  have member := mem_elements.mp (inElements o inL)
  exact loopFire_enabled_iff.mpr ⟨member.1, setup.receiver_mem, member.2.2, setup.body_fresh o⟩

/-- **No element fires twice**: a run of firings on elements of the start store never repeats an
element. -/
theorem executable_loop_nodup {start : Finset O} (setup : LoopSetup label loc channel receiver body start)
    {l : List O} (inElements : ∀ o ∈ l, o ∈ elements label loc channel receiver start)
    (executable : Executable label start (l.map (loopFire R receiver body))) : l.Nodup := by
  have pairwise := (executable_iff_pairwise (loopFires_enabled setup inElements)).mp executable
  rw [List.pairwise_map] at pairwise
  refine pairwise.imp fun {o o'} ⟨noClash, _⟩ equal => noClash ?_
  subst equal
  exact Or.inl (by simp [loopFire])

/-- What a run of firings leaves of the elements: those not fired. -/
theorem elements_after_loop {start : Finset O} (setup : LoopSetup label loc channel receiver body start)
    {l : List O} (inElements : ∀ o ∈ l, o ∈ elements label loc channel receiver start) :
    elements label loc channel receiver (fireList start (l.map (loopFire R receiver body))) =
      elements label loc channel receiver start \ l.toFinset := by
  rw [fireList_eq_fire_effectOf (MatchedAt.of_enabled (loopFires_enabled setup inElements))]
  ext x
  simp only [mem_elements, mem_fire, effectOf, mem_takenOf, mem_madeOf, List.mem_map,
    Finset.mem_sdiff, List.mem_toFinset]
  constructor
  · rintro ⟨⟨inStart, notTaken⟩ | ⟨c, ⟨o, inL, rfl⟩, made⟩, atChannel, notReceiver⟩
    · refine ⟨⟨inStart, atChannel, notReceiver⟩, fun inL => notTaken ⟨_, ⟨x, inL, rfl⟩, ?_⟩⟩
      simp [loopFire]
    · exact absurd atChannel (setup.body_off_channel o x made)
  · rintro ⟨⟨inStart, atChannel, notReceiver⟩, notInL⟩
    refine ⟨Or.inl ⟨inStart, ?_⟩, atChannel, notReceiver⟩
    rintro ⟨c, ⟨o, inL, rfl⟩, taken⟩
    simp only [loopFire, Finset.mem_singleton] at taken
    exact notInL (taken ▸ inL)

/-- **A run of firings is maximal exactly when it has fired every element.** Together with
`executable_loop_nodup`: every fair run fires each element exactly once. -/
theorem loop_maximal_iff {start : Finset O} (setup : LoopSetup label loc channel receiver body start)
    {l : List O} (inElements : ∀ o ∈ l, o ∈ elements label loc channel receiver start) :
    (∀ o ∈ elements label loc channel receiver start,
        ¬ Enabled label (fireList start (l.map (loopFire R receiver body))) (loopFire R receiver body o)) ↔
      ∀ o ∈ elements label loc channel receiver start, o ∈ l := by
  have enabledAll := loopFires_enabled setup inElements
  have matched := MatchedAt.of_enabled enabledAll
  constructor
  · intro maximal o inE
    by_contra notIn
    apply maximal o inE
    have member := mem_elements.mp inE
    have enabledO : Enabled label start (loopFire R receiver body o) :=
      loopFire_enabled_iff.mpr ⟨member.1, setup.receiver_mem, member.2.2, setup.body_fresh o⟩
    refine (enabled_fireList_iff enabledO matched).mpr fun c inMap => ?_
    obtain ⟨o', inL, rfl⟩ := List.mem_map.mp inMap
    have different : o ≠ o' := fun equal => notIn (equal ▸ inL)
    have independent := loopFire_independent (label := label) setup.body_apart different member.2.2
      (mem_elements.mp (inElements o' inL)).2.2
    exact ⟨independent.1, independent.2.2⟩
  · intro covered o inE enabledEnd
    have gone := elements_after_loop setup inElements
    have stillThere : o ∈ elements label loc channel receiver
        (fireList start (l.map (loopFire R receiver body))) := by
      have member := mem_elements.mp inE
      exact mem_elements.mpr ⟨(loopFire_enabled_iff.mp enabledEnd).1, member.2.1, member.2.2⟩
    rw [gone] at stillThere
    exact (Finset.mem_sdiff.mp stillThere).2 (List.mem_toFinset.mpr (covered o inE))

/-! ## The scope: nothing outside changes the iteration -/

/-- A commit of a process that does not hold the channel leaves the channel's occurrences as they
were. -/
theorem restrict_channel_fire_outside {others : N → Bool} (unheld : others channel = false)
    {e : Commit O R} (inScope : Scoped label loc others e) (store : Finset O) :
    restrict label loc (atChannel channel) (fire store e) =
      restrict label loc (atChannel channel) store := by
  ext o
  simp only [mem_restrict, mem_fire, atChannel, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨inStore, _⟩ | made, here⟩
    · exact ⟨inStore, here⟩
    · have := inScope.made o made
      rw [here, unheld] at this
      exact absurd this (by decide)
  · rintro ⟨inStore, here⟩
    refine ⟨Or.inl ⟨inStore, fun taken => ?_⟩, here⟩
    have := inScope.taken o taken
    rw [here, unheld] at this
    exact absurd this (by decide)

/-- **Non-interference for the loop**: no run of outside commits adds or removes an element. -/
theorem elements_fireList_outside {others : N → Bool} (unheld : others channel = false)
    {run : List (Commit O R)} (inScope : ∀ e ∈ run, Scoped label loc others e) (store : Finset O) :
    elements label loc channel receiver (fireList store run) =
      elements label loc channel receiver store := by
  induction run generalizing store with
  | nil => rfl
  | cons e rest ih =>
      rw [fireList_cons, ih (fun d member => inScope d (List.mem_cons_of_mem _ member))]
      unfold elements
      rw [restrict_channel_fire_outside unheld (inScope e List.mem_cons_self)]

/-! ## The end of the loop -/

/-- **An exhausted loop stays exhausted**: whatever outsiders do, no firing on an occurrence of the
channel is ever enabled again. -/
theorem exhausted_stays_exhausted {others : N → Bool} (unheld : others channel = false)
    {run : List (Commit O R)} (inScope : ∀ e ∈ run, Scoped label loc others e) {store : Finset O}
    (exhausted : elements label loc channel receiver store = ∅) {o : O}
    (atChannel' : loc (label o) = channel) :
    ¬ Enabled label (fireList store run) (loopFire R receiver body o) := by
  intro enabled
  obtain ⟨present, _, notReceiver, _⟩ := loopFire_enabled_iff.mp enabled
  have : o ∈ elements label loc channel receiver (fireList store run) :=
    mem_elements.mpr ⟨present, atChannel', notReceiver⟩
  rw [elements_fireList_outside unheld inScope, exhausted] at this
  simp at this

omit [DecidableEq N] in
/-- **The receiver is unobservable outside the scope** (the ν-garbage law): to processes that do
not hold the channel, a store with the receiver and the store without it run every scoped list of
commits alike, and reach stores that agree on everything those processes hold. This holds at every
store; what exhaustion adds is that the loop itself can no longer use the receiver
(`exhausted_runs_are_outside`), so collecting it is invisible to everyone. -/
theorem receiver_garbage {others : N → Bool} (unheld : others channel = false)
    {run : List (Commit O R)} (inScope : ∀ e ∈ run, Scoped label loc others e) {store : Finset O}
    (receiverAt : loc (label receiver) = channel) :
    (Executable label (store.erase receiver) run ↔ Executable label (store.erase receiver ∪ {receiver}) run) ∧
      restrict label loc others (fireList (store.erase receiver) run) =
        restrict label loc others (fireList (store.erase receiver ∪ {receiver}) run) :=
  garbage_unobservable inScope (fun o member => by
    rw [Finset.mem_singleton] at member
    subst member
    rw [receiverAt, unheld])

/-! ## Interleaved runs: the loop together with outsiders -/

/-- A step of an interleaved run: the loop fires on an occurrence, or an outsider commits. -/
def stepCommit (R : Type v) (receiver : O) (body : O → Finset O) : O ⊕ Commit O R → Commit O R :=
  Sum.elim (loopFire R receiver body) id

/-- The occurrences the loop fires on, in order. -/
def firedOf (run : List (O ⊕ Commit O R)) : List O := run.filterMap Sum.getLeft?

omit [DecidableEq O] in
@[simp] theorem firedOf_nil : firedOf ([] : List (O ⊕ Commit O R)) = [] := rfl

omit [DecidableEq O] in
@[simp] theorem firedOf_inl (o : O) (rest : List (O ⊕ Commit O R)) :
    firedOf (Sum.inl o :: rest) = o :: firedOf rest := rfl

omit [DecidableEq O] in
@[simp] theorem firedOf_inr (e : Commit O R) (rest : List (O ⊕ Commit O R)) :
    firedOf (Sum.inr e :: rest) = firedOf rest := rfl

/-- **An outsider**: it holds only names other than the channel's, and the identities it makes are
allocated apart from those of the loop's results. The allocation is the allocator's guarantee;
without it an outsider can squat on a result's identity and stall the loop
(`Controls.squatter_stalls_loop`). -/
structure Outsider (label : O → R) (loc : R → N) (body : O → Finset O) (others : N → Bool)
    (e : Commit O R) : Prop where
  inScope : Scoped label loc others e
  allocated : ∀ o, Disjoint e.made (body o)

/-- The steps of an interleaved run: outsiders, and firings of the loop on occurrences at the
channel. -/
structure Interleaved (label : O → R) (loc : R → N) (channel : N) (body : O → Finset O)
    (others : N → Bool) (run : List (O ⊕ Commit O R)) : Prop where
  outsiders : ∀ e, Sum.inr e ∈ run → Outsider label loc body others e
  onChannel : ∀ o, Sum.inl o ∈ run → loc (label o) = channel

omit [DecidableEq O] [DecidableEq N] in
theorem Interleaved.tail {others : N → Bool} {s : O ⊕ Commit O R} {rest : List (O ⊕ Commit O R)}
    (interleaved : Interleaved label loc channel body others (s :: rest)) :
    Interleaved label loc channel body others rest :=
  ⟨fun e member => interleaved.outsiders e (List.mem_cons_of_mem _ member),
    fun o member => interleaved.onChannel o (List.mem_cons_of_mem _ member)⟩

/-- What the loop guarantees along an interleaved run from `start`, having fired `done`: the
elements left are those not fired, the receiver is present, the results of every element not
fired are still fresh, and no element has fired twice. -/
structure LoopInvariant (label : O → R) (loc : R → N) (channel : N) (receiver : O)
    (body : O → Finset O) (start : Finset O) (done : List O) (store : Finset O) : Prop where
  elements_eq : elements label loc channel receiver store =
    elements label loc channel receiver start \ done.toFinset
  receiver_mem : receiver ∈ store
  unfired_fresh : ∀ o ∈ elements label loc channel receiver start, o ∉ done → Disjoint (body o) store
  nodup : done.Nodup
  done_sub : ∀ o ∈ done, o ∈ elements label loc channel receiver start

theorem LoopInvariant.initial {start : Finset O}
    (setup : LoopSetup label loc channel receiver body start) :
    LoopInvariant label loc channel receiver body start [] start where
  elements_eq := by simp
  receiver_mem := setup.receiver_mem
  unfired_fresh o _ _ := setup.body_fresh o
  nodup := List.nodup_nil
  done_sub _ member := absurd member List.not_mem_nil

theorem LoopInvariant.loopStep {start : Finset O}
    (setup : LoopSetup label loc channel receiver body start) {done : List O} {store : Finset O}
    (inv : LoopInvariant label loc channel receiver body start done store) {o : O}
    (atChannel' : loc (label o) = channel) (enabled : Enabled label store (loopFire R receiver body o)) :
    LoopInvariant label loc channel receiver body start (done ++ [o])
      (fire store (loopFire R receiver body o)) := by
  obtain ⟨present, _, notReceiver, _⟩ := loopFire_enabled_iff.mp enabled
  have inElements : o ∈ elements label loc channel receiver store :=
    mem_elements.mpr ⟨present, atChannel', notReceiver⟩
  rw [inv.elements_eq, Finset.mem_sdiff, List.mem_toFinset] at inElements
  obtain ⟨inStart, notDone⟩ := inElements
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext x
    have before := congrArg (x ∈ ·) inv.elements_eq
    simp only [eq_iff_iff, mem_elements, Finset.mem_sdiff, List.mem_toFinset] at before
    simp only [mem_elements, mem_fire, loopFire, Finset.mem_sdiff, List.mem_toFinset,
      List.mem_append, List.mem_singleton, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨inStore, notO⟩ | made, here, notR⟩
      · obtain ⟨start', notDone'⟩ := before.mp ⟨inStore, here, notR⟩
        exact ⟨start', fun done' => done'.elim notDone' notO⟩
      · exact absurd here (setup.body_off_channel o x made)
    · rintro ⟨inStart', notDoneO⟩
      have fresh := before.mpr ⟨inStart', fun inDone => notDoneO (Or.inl inDone)⟩
      exact ⟨Or.inl ⟨fresh.1, fun same => notDoneO (Or.inr same)⟩, fresh.2.1, fresh.2.2⟩
  · exact mem_fire.mpr (Or.inl ⟨inv.receiver_mem, by simpa [loopFire] using Ne.symm notReceiver⟩)
  · intro o' inStart' notDone'
    have different : o' ≠ o := fun same => notDone' (by simp [same])
    have earlier := inv.unfired_fresh o' inStart' (fun inDone => notDone' (by simp [inDone]))
    refine Finset.disjoint_left.mpr fun x inBody inFire => ?_
    rcases mem_fire.mp inFire with ⟨inStore, _⟩ | made
    · exact Finset.disjoint_left.mp earlier inBody inStore
    · exact Finset.disjoint_left.mp (setup.body_apart o' o different) inBody made
  · rw [← List.concat_eq_append]
    exact inv.nodup.concat notDone
  · intro o' member
    rcases List.mem_append.mp member with inDone | same
    · exact inv.done_sub o' inDone
    · rw [List.mem_singleton.mp same]
      exact inStart

theorem LoopInvariant.outsiderStep {start : Finset O} {others : N → Bool}
    (unheld : others channel = false) (setup : LoopSetup label loc channel receiver body start)
    {done : List O} {store : Finset O}
    (inv : LoopInvariant label loc channel receiver body start done store) {e : Commit O R}
    (outsider : Outsider label loc body others e) :
    LoopInvariant label loc channel receiver body start done (fire store e) := by
  refine ⟨?_, ?_, ?_, inv.nodup, inv.done_sub⟩
  · rw [← inv.elements_eq]
    unfold elements
    rw [restrict_channel_fire_outside unheld outsider.inScope]
  · refine mem_fire.mpr (Or.inl ⟨inv.receiver_mem, fun taken => ?_⟩)
    have := outsider.inScope.taken receiver taken
    rw [setup.receiver_at, unheld] at this
    exact absurd this (by decide)
  · intro o' inStart' notDone'
    refine Finset.disjoint_left.mpr fun x inBody inFire => ?_
    rcases mem_fire.mp inFire with ⟨inStore, _⟩ | made
    · exact Finset.disjoint_left.mp (inv.unfired_fresh o' inStart' notDone') inBody inStore
    · exact Finset.disjoint_left.mp (outsider.allocated o') made inBody

/-- **The invariant holds along every interleaved run.** -/
theorem LoopInvariant.run {start : Finset O} {others : N → Bool} (unheld : others channel = false)
    (setup : LoopSetup label loc channel receiver body start) :
    ∀ {run : List (O ⊕ Commit O R)} {done : List O} {store : Finset O},
      LoopInvariant label loc channel receiver body start done store →
      Interleaved label loc channel body others run →
      Executable label store (run.map (stepCommit R receiver body)) →
      LoopInvariant label loc channel receiver body start (done ++ firedOf run)
        (fireList store (run.map (stepCommit R receiver body))) := by
  intro run
  induction run with
  | nil => intro done store inv _ _; simpa using inv
  | cons s rest ih =>
      intro done store inv interleaved executable
      rw [List.map_cons] at executable
      cases executable with
      | cons enabled after =>
          rw [List.map_cons, fireList_cons]
          cases s with
          | inl o =>
              have next := inv.loopStep setup (interleaved.onChannel o List.mem_cons_self) enabled
              have := ih next interleaved.tail after
              simpa [stepCommit, List.append_assoc] using this
          | inr e =>
              have next := inv.outsiderStep unheld setup
                (interleaved.outsiders e List.mem_cons_self)
              have := ih next interleaved.tail after
              simpa [stepCommit] using this

/-- **Interleaved with outsiders, each element fires at most once**, and what remains on the
channel is exactly the elements not yet fired. -/
theorem interleaved_elements {start : Finset O} {others : N → Bool} (unheld : others channel = false)
    (setup : LoopSetup label loc channel receiver body start) {run : List (O ⊕ Commit O R)}
    (interleaved : Interleaved label loc channel body others run)
    (executable : Executable label start (run.map (stepCommit R receiver body))) :
    (firedOf run).Nodup ∧ (∀ o ∈ firedOf run, o ∈ elements label loc channel receiver start) ∧
      elements label loc channel receiver (fireList start (run.map (stepCommit R receiver body))) =
        elements label loc channel receiver start \ (firedOf run).toFinset := by
  have inv := (LoopInvariant.initial setup).run unheld setup interleaved executable
  simp only [List.nil_append] at inv
  exact ⟨inv.nodup, inv.done_sub, inv.elements_eq⟩

/-- **No outsider can stall the loop**: after any interleaved run, every element not yet fired can
fire. -/
theorem interleaved_unfired_enabled {start : Finset O} {others : N → Bool}
    (unheld : others channel = false) (setup : LoopSetup label loc channel receiver body start)
    {run : List (O ⊕ Commit O R)} (interleaved : Interleaved label loc channel body others run)
    (executable : Executable label start (run.map (stepCommit R receiver body))) {o : O}
    (inStart : o ∈ elements label loc channel receiver start) (notFired : o ∉ firedOf run) :
    Enabled label (fireList start (run.map (stepCommit R receiver body))) (loopFire R receiver body o) := by
  have inv := (LoopInvariant.initial setup).run unheld setup interleaved executable
  simp only [List.nil_append] at inv
  have left : o ∈ elements label loc channel receiver
      (fireList start (run.map (stepCommit R receiver body))) := by
    rw [inv.elements_eq, Finset.mem_sdiff, List.mem_toFinset]
    exact ⟨inStart, notFired⟩
  obtain ⟨present, _, notReceiver⟩ := mem_elements.mp left
  exact loopFire_enabled_iff.mpr ⟨present, inv.receiver_mem, notReceiver,
    inv.unfired_fresh o inStart notFired⟩

/-- **An interleaved run leaves the loop with nothing to fire exactly when it has fired every
element.** With `interleaved_elements` and `interleaved_unfired_enabled`: under a scheduler that
does not starve the loop forever, every element fires exactly once, whatever the outsiders do. -/
theorem interleaved_maximal_iff {start : Finset O} {others : N → Bool}
    (unheld : others channel = false) (setup : LoopSetup label loc channel receiver body start)
    {run : List (O ⊕ Commit O R)} (interleaved : Interleaved label loc channel body others run)
    (executable : Executable label start (run.map (stepCommit R receiver body))) :
    (∀ o ∈ elements label loc channel receiver start,
        ¬ Enabled label (fireList start (run.map (stepCommit R receiver body)))
          (loopFire R receiver body o)) ↔
      ∀ o ∈ elements label loc channel receiver start, o ∈ firedOf run := by
  constructor
  · intro maximal o inStart
    by_contra notFired
    exact maximal o inStart
      (interleaved_unfired_enabled unheld setup interleaved executable inStart notFired)
  · intro covered o inStart enabledEnd
    obtain ⟨_, _, gone⟩ := interleaved_elements unheld setup interleaved executable
    obtain ⟨present, _, notReceiver, _⟩ := loopFire_enabled_iff.mp enabledEnd
    have stillThere : o ∈ elements label loc channel receiver
        (fireList start (run.map (stepCommit R receiver body))) :=
      mem_elements.mpr ⟨present, (mem_elements.mp inStart).2.1, notReceiver⟩
    rw [gone, Finset.mem_sdiff, List.mem_toFinset] at stillThere
    exact stillThere.2 (covered o inStart)

/-- **From an exhausted store every interleaved run is a run of outsiders**: the loop never fires
again, so by `receiver_garbage` the receiver can be collected invisibly. -/
theorem exhausted_runs_are_outside {others : N → Bool} (unheld : others channel = false) :
    ∀ {run : List (O ⊕ Commit O R)} {store : Finset O},
      elements label loc channel receiver store = ∅ →
      Interleaved label loc channel body others run →
      Executable label store (run.map (stepCommit R receiver body)) → firedOf run = [] := by
  intro run
  induction run with
  | nil => intro _ _ _ _; rfl
  | cons s rest ih =>
      intro store exhausted interleaved executable
      rw [List.map_cons] at executable
      cases executable with
      | cons enabled after =>
          cases s with
          | inl o =>
              obtain ⟨present, _, notReceiver, _⟩ := loopFire_enabled_iff.mp enabled
              have : o ∈ elements label loc channel receiver store :=
                mem_elements.mpr ⟨present, interleaved.onChannel o List.mem_cons_self, notReceiver⟩
              rw [exhausted] at this
              exact absurd this (Finset.notMem_empty o)
          | inr e =>
              have outsider := interleaved.outsiders e List.mem_cons_self
              have still : elements label loc channel receiver (fire store e) = ∅ := by
                unfold elements
                rw [restrict_channel_fire_outside unheld outsider.inScope]
                exact exhausted
              simpa using ih still interleaved.tail after

end Loop

/-! ## Controls -/

namespace Controls

open Atom

/-- Occurrences `200` (the receiver), `201`, `202` live at the channel `0`; the body results `211`,
`212` live at name `1`. -/
def loopLoc : ℕ → ℕ
  | 200 => 0 | 201 => 0 | 202 => 0
  | _ => 1

/-- Labels of the loop control. -/
def loopLabel (o : ℕ) : ℕ × Atom := (loopLoc o, out)

/-- The body: element `201` makes `211`, element `202` makes `212`. -/
def loopBody : ℕ → Finset ℕ
  | 201 => {211}
  | 202 => {212}
  | _ => ∅

/-- An outsider who holds the channel's name injects element `202`. -/
def inject : Commit ℕ (ℕ × Atom) := ⟨∅, ∅, {202}, []⟩

/-- **A public channel lets an outsider change the loop.** A process that holds name `0` injects
an element, and the loop then fires on it: the store reaches `212`. A process that does not hold
the name cannot even perform the injection. -/
theorem public_channel_injection :
    Scoped loopLabel Prod.fst (fun n => n == 0) inject ∧
      ¬ Scoped loopLabel Prod.fst (fun n => n == 1) inject ∧
      Executable loopLabel {200, 201}
        [inject, loopFire (ℕ × Atom) 200 loopBody 201, loopFire (ℕ × Atom) 200 loopBody 202] ∧
      212 ∈ fireList {200, 201} [inject, loopFire (ℕ × Atom) 200 loopBody 201, loopFire (ℕ × Atom) 200 loopBody 202] ∧
      fireList {200, 201} [loopFire (ℕ × Atom) 200 loopBody 201] = {200, 211} := by
  refine ⟨⟨by simp [inject], by simp [inject], by decide, by simp [inject]⟩, ?_, ?_, by decide, by decide⟩
  · intro inScope
    have := inScope.made 202 (by simp [inject])
    revert this
    decide
  · refine .cons ⟨by simp [inject], by simp [inject], by simp [inject], by decide, by simp [inject]⟩ ?_
    refine .cons (loopFire_enabled_iff.mpr ⟨by decide, by decide, by decide, by decide⟩) ?_
    exact .cons (loopFire_enabled_iff.mpr ⟨by decide, by decide, by decide, by decide⟩) (.nil _)

theorem loopBody_cases (o : ℕ) :
    (o = 201 ∧ loopBody o = {211}) ∨ (o = 202 ∧ loopBody o = {212}) ∨
      (o ≠ 201 ∧ o ≠ 202 ∧ loopBody o = ∅) := by
  unfold loopBody
  split
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rename_i first second
    exact Or.inr (Or.inr ⟨first, second, rfl⟩)

/-- **The loop setting is satisfiable**: the receiver `200` over the element `201`. -/
theorem loopSetup_instance : LoopSetup loopLabel Prod.fst 0 200 loopBody {200, 201} where
  receiver_mem := by decide
  receiver_at := rfl
  body_fresh o := by
    rcases loopBody_cases o with ⟨_, body⟩ | ⟨_, body⟩ | ⟨_, _, body⟩ <;> rw [body] <;> decide
  body_apart o o' different := by
    rcases loopBody_cases o with ⟨isO, body⟩ | ⟨isO, body⟩ | ⟨_, _, body⟩ <;>
      rcases loopBody_cases o' with ⟨isO', body'⟩ | ⟨isO', body'⟩ | ⟨_, _, body'⟩ <;>
      rw [body, body'] <;> first | decide | (subst isO; subst isO'; exact absurd rfl different)
  body_off_channel o x member := by
    rcases loopBody_cases o with ⟨_, body⟩ | ⟨_, body⟩ | ⟨_, _, body⟩ <;> rw [body] at member
    · rw [Finset.mem_singleton.mp member]; decide
    · rw [Finset.mem_singleton.mp member]; decide
    · simp at member

/-- So the loop over `201` runs. -/
theorem loop_instance :
    Executable loopLabel {200, 201} ([201].map (loopFire (ℕ × Atom) 200 loopBody)) :=
  loop_every_order loopSetup_instance (by simp)
    (fun o member => by
      simp only [List.mem_singleton] at member
      subst member
      decide)

/-- A process at name `1`, which does not hold the channel, makes occurrence `211`: the identity
of the result of element `201`. -/
def squatter : Commit ℕ (ℕ × Atom) := ⟨∅, ∅, {211}, []⟩

/-- **Without the allocator an outsider can stall the loop.** The squatter does not hold the
channel; after it commits, element `201` is still on the channel and can never fire, since its
result's identity is taken. -/
theorem squatter_stalls_loop :
    Scoped loopLabel Prod.fst (fun n => n == 1) squatter ∧
      Enabled loopLabel {200, 201} squatter ∧
      elements loopLabel Prod.fst 0 200 (fire {200, 201} squatter) = {201} ∧
      ¬ Enabled loopLabel (fire {200, 201} squatter) (loopFire (ℕ × Atom) 200 loopBody 201) := by
  refine ⟨⟨by simp [squatter], by simp [squatter], by decide, by simp [squatter]⟩,
    ⟨by decide, by decide, by decide, by decide, by simp [squatter]⟩, by decide, fun enabled => ?_⟩
  have fresh := (loopFire_enabled_iff.mp enabled).2.2.2
  revert fresh
  decide

/-- The squatter is excluded by the allocator: it is not an outsider. -/
theorem squatter_not_outsider :
    ¬ Outsider loopLabel Prod.fst loopBody (fun n => n == 1) squatter := fun outsider => by
  have := outsider.allocated 201
  revert this
  decide

/-- A process at name `1` that makes an identity of its own. -/
def bystander : Commit ℕ (ℕ × Atom) := ⟨∅, ∅, {215}, []⟩

theorem bystander_outsider : Outsider loopLabel Prod.fst loopBody (fun n => n == 1) bystander where
  inScope := ⟨by simp [bystander], by simp [bystander], by decide, by simp [bystander]⟩
  allocated o := by
    rcases loopBody_cases o with ⟨_, body⟩ | ⟨_, body⟩ | ⟨_, _, body⟩ <;> rw [body] <;> decide

/-- The bystander, then the loop on `201`. -/
def mixedRun : List (ℕ ⊕ Commit ℕ (ℕ × Atom)) := [.inr bystander, .inl 201]

/-- **An interleaved run meets the hypotheses**, so the interleaved theorems are not vacuous: the
run executes, and the loop ends having fired `201` once. -/
theorem mixedRun_instance :
    Interleaved loopLabel Prod.fst 0 loopBody (fun n => n == 1) mixedRun ∧
      Executable loopLabel {200, 201} (mixedRun.map (stepCommit (ℕ × Atom) 200 loopBody)) ∧
      firedOf mixedRun = [201] ∧
      elements loopLabel Prod.fst 0 200
        (fireList {200, 201} (mixedRun.map (stepCommit (ℕ × Atom) 200 loopBody))) = ∅ := by
  have interleaved : Interleaved loopLabel Prod.fst 0 loopBody (fun n => n == 1) mixedRun := by
    refine ⟨fun e member => ?_, fun o member => ?_⟩
    · simp only [mixedRun, List.mem_cons, Sum.inr.injEq, reduceCtorEq, List.mem_nil_iff,
        or_false] at member
      subst member
      exact bystander_outsider
    · simp only [mixedRun, List.mem_cons, reduceCtorEq, Sum.inl.injEq, List.mem_nil_iff,
        false_or, or_false] at member
      subst member
      rfl
  have executable : Executable loopLabel {200, 201}
      (mixedRun.map (stepCommit (ℕ × Atom) 200 loopBody)) := by
    refine .cons ⟨by simp [stepCommit, bystander], by simp [stepCommit, bystander],
      by simp [stepCommit, bystander], by decide, by simp [stepCommit, bystander]⟩ ?_
    exact .cons (loopFire_enabled_iff.mpr ⟨by decide, by decide, by decide, by decide⟩) (.nil _)
  refine ⟨interleaved, executable, rfl, ?_⟩
  obtain ⟨_, _, gone⟩ := interleaved_elements (by decide) loopSetup_instance interleaved executable
  rw [gone]
  decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
