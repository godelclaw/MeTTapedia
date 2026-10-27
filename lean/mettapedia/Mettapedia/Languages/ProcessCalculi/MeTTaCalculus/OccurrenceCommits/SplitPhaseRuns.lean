import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ValidationPolicies

/-!
# Runs of a scheduler: atomic firings, split-phase proposals, batches and observations

A scheduler that runs concurrent firings does more than fire commits one at a time. It may
*propose* a commit at one store and *commit* it at a later one, after other commits; it may commit
a *batch* of commits matched at one store; it may *observe* that a firing cannot fire now and
continue otherwise; and a thread may fire inside a private copy of the store. This module gives
such runs a semantics over the commits of `Commits`, so that a trace a scheduler prints can be
checked against it (`TraceChecker`).

## Events and states

A `RunState` holds the live store, every identity ever allocated (`born`), the active proposals
(a transaction number, the mode that will validate it, and its commit) and the private stores of
branch-local threads. The events are:

* `fire c`: an atomic firing; `c` must be enabled at the store.
* `begin t mode c`: transaction `t` proposes `c`, which must be enabled at the store (the matcher
  ran here); its fresh identities are reserved.
* `commit t dropped`: `t` publishes its commit, without the fresh occurrences `dropped`, when its
  mode permits it at the current store (`Permits`). An occurrence may be dropped only when an
  occurrence with its label is present after the commit: this is how a region with set semantics
  ignores an emission it already holds.
* `abort t`: `t` is dropped.
* `batch cs`: commits all enabled at one store, pairwise without a clash, committed in an
  executable order (the wave commit of `Waves`).
* `observe c`: a read-only commit enabled at the store, such as the observation that a firing
  has no row now.
* `branch b c`: an atomic firing in the private store `b` (a copy of the store taken when `b` is
  first used).
* `tau`: a step that touches no store.

Every fresh identity must be unborn: identities are never reused (the runtime specification of
the first report, item 7.1).

## Theorems

* **Atomic runs are executable sequences** (`runValid_fires_iff`): a run made of firings only is
  valid exactly when its commits form an `Executable` sequence.
* **A valid batch is an acyclic wave** (`Valid.batch_acyclic`, `Valid.batch_fireList`): no common
  take, acyclic precedence, and it reaches the wave commit.
* **Serializable runs refine the atomic semantics** (`executable_history_of_serializable`): when
  every proposal is validated in `serializable` mode, the commits of the run, in commit order,
  form an executable sequence from the initial store, and the run ends where that sequence ends.
* **A run whose proposals all begin before any commit is a round** (`round_of_beginsFirst`):
  every split-phase run that begins its proposals at one store and then commits or aborts them is a
  `Round` of `ValidationPolicies` over those proposals. Its outcomes are therefore the snapshot
  outcomes characterized there (`snapshotOutcome_of_beginsFirst`).
* **A history is serializable** when some order of its commits is executable from the initial
  store (`SerializableHistory`). For commits matched at one store and pairwise without a clash this
  is exactly acyclic precedence (`serializableHistory_iff_acyclic`), so it is the cycle test of
  `Waves`, extended to proposals begun at different stores.

## Controls

The positive and negative examples are decided by the verified checker of `TraceChecker`, whose
correctness theorems transfer them to the definitions here: a reader and a taker proposed at one
store and committed taker first form a valid snapshot run whose history is serializable (reader
first) although the reader's kept occurrence is gone when it commits
(`TraceChecker.Controls.taker_first_valid`, `taker_first_serializable`); the same run validated in
`serializable` mode is not valid (`serializable_refuses_stale`); write skew under `snapshot` is a
valid run whose history is not serializable (`write_skew_valid`, `write_skew_not_serializable`);
two atomic takes of one occurrence are not a valid run (`double_take_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v

variable {O : Type u} [DecidableEq O] {R : Type v}

namespace Commit

/-- The commit without some of the occurrences it would make. -/
def dropMade (c : Commit O R) (dropped : Finset O) : Commit O R :=
  { c with made := c.made \ dropped }

@[simp] theorem dropMade_taken (c : Commit O R) (dropped : Finset O) :
    (c.dropMade dropped).taken = c.taken := rfl

@[simp] theorem dropMade_kept (c : Commit O R) (dropped : Finset O) :
    (c.dropMade dropped).kept = c.kept := rfl

@[simp] theorem dropMade_made (c : Commit O R) (dropped : Finset O) :
    (c.dropMade dropped).made = c.made \ dropped := rfl

@[simp] theorem dropMade_queries (c : Commit O R) (dropped : Finset O) :
    (c.dropMade dropped).queries = c.queries := rfl

end Commit

/-- One event of a run. -/
inductive Event (O : Type u) (R : Type v) where
  | fire (c : Commit O R)
  | begin (t : ℕ) (mode : Finset Check) (c : Commit O R)
  | commit (t : ℕ) (dropped : Finset O)
  | abort (t : ℕ)
  | batch (cs : List (Commit O R))
  | observe (c : Commit O R)
  | branch (b : ℕ) (c : Commit O R)
  | tau

/-- The state of a run. -/
structure RunState (O : Type u) (R : Type v) where
  store : Finset O
  born : Finset O
  active : List (ℕ × Finset Check × Commit O R)
  branches : List (ℕ × Finset O)

namespace RunState

/-- The private store of branch `b`: the store itself until `b` is first used. -/
def branchStore (s : RunState O R) (b : ℕ) : Finset O := (s.branches.lookup b).getD s.store

/-- A run starting at a store, with nothing active. -/
def start (store : Finset O) : RunState O R := ⟨store, store, [], []⟩

end RunState

/-- Remove the entries of a key from an association list. -/
def eraseKey {β : Type*} (t : ℕ) (l : List (ℕ × β)) : List (ℕ × β) := l.filter fun x => x.1 != t

/-- When an event may happen. -/
def Valid (label : O → R) (s : RunState O R) : Event O R → Prop
  | .fire c => Enabled label s.store c ∧ Disjoint c.made s.born
  | .begin t _ c => s.active.lookup t = none ∧ Enabled label s.store c ∧ Disjoint c.made s.born
  | .commit t dropped => ∃ mode c, s.active.lookup t = some (mode, c) ∧ dropped ⊆ c.made ∧
      (∀ o ∈ dropped, ∃ o' ∈ fire s.store (c.dropMade dropped), label o' = label o) ∧
      Permits label mode s.store (c.dropMade dropped)
  | .abort t => ∃ entry, s.active.lookup t = some entry
  | .batch cs => (∀ c ∈ cs, Enabled label s.store c) ∧ Disjoint (madeOf cs) s.born ∧
      cs.Pairwise (fun e d => ¬ Clash e d) ∧ Executable label s.store cs
  | .observe c => Enabled label s.store c ∧ c.taken = ∅ ∧ c.made = ∅
  | .branch b c => Enabled label (s.branchStore b) c ∧ Disjoint c.made s.born
  | .tau => True

/-- What an event does. -/
def next (s : RunState O R) : Event O R → RunState O R
  | .fire c => { s with store := fire s.store c, born := s.born ∪ c.made }
  | .begin t mode c => { s with active := (t, mode, c) :: s.active, born := s.born ∪ c.made }
  | .commit t dropped =>
      match s.active.lookup t with
      | some (_, c) => { s with store := fire s.store (c.dropMade dropped),
                                active := eraseKey t s.active }
      | none => s
  | .abort t => { s with active := eraseKey t s.active }
  | .batch cs => { s with store := fireList s.store cs, born := s.born ∪ madeOf cs }
  | .observe _ => s
  | .branch b c => { s with branches := (b, fire (s.branchStore b) c) :: eraseKey b s.branches,
                            born := s.born ∪ c.made }
  | .tau => s

/-- A valid run: each event may happen at the state the earlier ones reach. -/
def RunValid (label : O → R) : RunState O R → List (Event O R) → Prop
  | _, [] => True
  | s, e :: es => Valid label s e ∧ RunValid label (next s e) es

/-- The state a run reaches. -/
def final (s : RunState O R) (es : List (Event O R)) : RunState O R := es.foldl next s

@[simp] theorem final_nil (s : RunState O R) : final s [] = s := rfl

@[simp] theorem final_cons (s : RunState O R) (e : Event O R) (es : List (Event O R)) :
    final s (e :: es) = final (next s e) es := rfl

/-- The commits an event publishes to the shared store. -/
def committedBy (s : RunState O R) : Event O R → List (Commit O R)
  | .fire c => [c]
  | .commit t dropped =>
      match s.active.lookup t with
      | some (_, c) => [c.dropMade dropped]
      | none => []
  | .batch cs => cs
  | .observe c => [c]
  | _ => []

/-- The history of a run: the commits it published, in order. -/
def history : RunState O R → List (Event O R) → List (Commit O R)
  | _, [] => []
  | s, e :: es => committedBy s e ++ history (next s e) es

/-! ## Atomic runs -/

/-- **A run of firings is valid exactly when its commits are an executable sequence** (with fresh
identities never reused). -/
theorem runValid_fires_iff {label : O → R} :
    ∀ (s : RunState O R) (cs : List (Commit O R)),
      RunValid label s (cs.map Event.fire) ↔
        Executable label s.store cs ∧
          ∀ (pre : List (Commit O R)) (c : Commit O R) (post : List (Commit O R)),
            cs = pre ++ c :: post → Disjoint c.made (s.born ∪ madeOf pre) := by
  intro s cs
  induction cs generalizing s with
  | nil => simp [RunValid, Executable.nil]
  | cons c rest ih =>
      simp only [List.map_cons, RunValid, Valid, next]
      rw [ih, executable_cons_iff]
      constructor
      · rintro ⟨⟨enabled, freshC⟩, executable, freshRest⟩
        refine ⟨⟨enabled, executable⟩, ?_⟩
        intro pre d post split
        rcases pre with _ | ⟨p, pre⟩
        · simp only [List.nil_append, List.cons.injEq] at split
          obtain ⟨rfl, -⟩ := split
          simpa [madeOf] using freshC
        · simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨rfl, split⟩ := split
          have := freshRest pre d post split
          simpa [madeOf, Finset.union_assoc] using this
      · rintro ⟨⟨enabled, executable⟩, fresh⟩
        refine ⟨⟨enabled, by simpa [madeOf] using fresh [] c rest rfl⟩, executable, ?_⟩
        intro pre d post split
        have := fresh (c :: pre) d post (by simp [split])
        simpa [madeOf, Finset.union_assoc] using this

/-! ## Batches -/

/-- **A valid batch satisfies the exact batch condition of `Waves`**: its commits are matched at
one store, no two take a common occurrence, and its precedence relation is acyclic. -/
theorem Valid.batch_acyclic {label : O → R} {s : RunState O R} {cs : List (Commit O R)}
    (valid : Valid label s (.batch cs)) :
    (∀ c ∈ cs, Enabled label s.store c) ∧ cs.Pairwise (fun e d => ¬ Clash e d) ∧ Acyclic label cs := by
  obtain ⟨enabled, -, noClash, executable⟩ := valid
  exact ⟨enabled, noClash,
    (exists_executable_perm_iff_acyclic enabled noClash).mp ⟨cs, List.Perm.refl _, executable⟩⟩

/-- A batch reaches the wave commit: the store without everything taken, with everything made. -/
theorem Valid.batch_fireList {label : O → R} {s : RunState O R} {cs : List (Commit O R)}
    (valid : Valid label s (.batch cs)) : fireList s.store cs = fire s.store (effectOf cs) :=
  Executable.fireList_eq valid.1

/-! ## Serializable runs refine the atomic semantics -/

/-- What the refinement argument needs of a state: its active proposals do not keep what they
take and are validated in `serializable` mode. -/
def SerializableActive (s : RunState O R) : Prop :=
  ∀ x ∈ s.active, x.2.1 = Mode.serializable ∧ Disjoint x.2.2.taken x.2.2.kept

theorem mem_of_lookup_eq_some {β : Type*} {l : List (ℕ × β)} {t : ℕ} {b : β}
    (found : l.lookup t = some b) : (t, b) ∈ l := by
  induction l with
  | nil => simp at found
  | cons x rest ih =>
      obtain ⟨k, v⟩ := x
      by_cases same : t = k
      · subst same
        simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at found
        subst found
        exact List.mem_cons_self
      · have : (t == k) = false := by simpa using same
        simp only [List.lookup, this] at found
        exact List.mem_cons_of_mem _ (ih found)

theorem mem_eraseKey {β : Type*} {l : List (ℕ × β)} {t : ℕ} {x : ℕ × β}
    (member : x ∈ eraseKey t l) : x ∈ l :=
  (List.mem_filter.mp member).1

/-- Only begin events need their mode checked. -/
def AllBeginsIn (modes : Finset (Finset Check)) : List (Event O R) → Prop
  | [] => True
  | .begin _ mode _ :: es => mode ∈ modes ∧ AllBeginsIn modes es
  | _ :: es => AllBeginsIn modes es

theorem fire_eq_of_readOnly {store : Finset O} {c : Commit O R} (taken : c.taken = ∅)
    (made : c.made = ∅) : fire store c = store := by
  simp [fire, taken, made]

/-- **Serializable runs refine the atomic semantics.** When every proposal of a run is validated
in `serializable` mode, the commits it publishes, in order, are an executable sequence from its
initial store, and the run ends where that sequence ends. -/
theorem executable_history_of_serializable {label : O → R} :
    ∀ (es : List (Event O R)) (s : RunState O R), SerializableActive s →
      AllBeginsIn {Mode.serializable} es → RunValid label s es →
        Executable label s.store (history s es) ∧
          (final s es).store = fireList s.store (history s es) := by
  intro es
  induction es with
  | nil => intro s _ _ _; exact ⟨Executable.nil _, rfl⟩
  | cons e es ih =>
      intro s active modes run
      obtain ⟨valid, rest⟩ := run
      cases e with
      | fire c =>
          have := ih (next s (.fire c)) active modes rest
          refine ⟨executable_cons_iff.mpr ⟨valid.1, this.1⟩, this.2⟩
      | begin t mode c =>
          have modeEq : mode = Mode.serializable := by simpa [AllBeginsIn] using modes.1
          have active' : SerializableActive (next s (.begin t mode c)) := by
            intro x member
            simp only [next, List.mem_cons] at member
            rcases member with rfl | member
            · exact ⟨modeEq, valid.2.1.apart⟩
            · exact active x member
          have := ih _ active' modes.2 rest
          simpa [history, committedBy, next] using this
      | commit t dropped =>
          obtain ⟨mode, c, found, -, -, permits⟩ := valid
          have entry := active _ (mem_of_lookup_eq_some found)
          simp only at entry
          obtain ⟨modeEq, apart⟩ := entry
          subst modeEq
          have enabled : Enabled label s.store (c.dropMade dropped) :=
            (permits_serializable_iff (by simpa using apart)).mp permits
          have active' : SerializableActive (next s (.commit t dropped)) := by
            intro x member
            simp only [next, found] at member
            exact active x (mem_eraseKey member)
          have := ih _ active' modes rest
          simp only [next, found] at this
          simp only [history, committedBy, found, List.singleton_append, final_cons, next]
          exact ⟨executable_cons_iff.mpr ⟨enabled, this.1⟩, this.2⟩
      | abort t =>
          have active' : SerializableActive (next s (.abort t)) := by
            intro x member
            exact active x (mem_eraseKey member)
          have := ih _ active' modes rest
          simpa [history, committedBy, next] using this
      | batch cs =>
          have := ih (next s (.batch cs)) active modes rest
          simp only [history, committedBy, next, final_cons] at this ⊢
          exact ⟨executable_append_iff.mpr ⟨valid.2.2.2, this.1⟩, by rw [this.2, fireList_append]⟩
      | observe c =>
          have same : next s (.observe c) = s := rfl
          have := ih (next s (.observe c)) active modes rest
          rw [same] at this
          simp only [history, committedBy, List.singleton_append]
          refine ⟨executable_cons_iff.mpr ⟨valid.1, ?_⟩, ?_⟩
          · rw [fire_eq_of_readOnly valid.2.1 valid.2.2]; exact this.1
          · rw [fireList_cons, fire_eq_of_readOnly valid.2.1 valid.2.2]; exact this.2
      | branch b c =>
          have := ih (next s (.branch b c)) active modes rest
          simpa [history, committedBy, next] using this
      | tau =>
          have := ih (next s .tau) active modes rest
          simpa [history, committedBy, next] using this


/-! ## Proposals that all begin at one store form a round -/

/-- An event that commits, aborts or idles. -/
def Resolving : Event O R → Prop
  | .commit _ _ => True
  | .abort _ => True
  | .tau => True
  | _ => False

/-- The proposals of an active list in the order a list of events resolves them: a committed
proposal as it is published, an aborted one as it was proposed. -/
def resolvedProposals : List (ℕ × Finset Check × Commit O R) → List (Event O R) → List (Commit O R)
  | _, [] => []
  | active, .commit t dropped :: es =>
      match active.lookup t with
      | some (_, c) => c.dropMade dropped :: resolvedProposals (eraseKey t active) es
      | none => resolvedProposals active es
  | active, .abort t :: es =>
      match active.lookup t with
      | some (_, c) => c :: resolvedProposals (eraseKey t active) es
      | none => resolvedProposals active es
  | active, _ :: es => resolvedProposals active es

/-- Every active proposal is validated by the mode `mode`. -/
def ActiveIn (mode : Finset Check) (s : RunState O R) : Prop := ∀ x ∈ s.active, x.2.1 = mode

/-- **A resolution of proposals is a round.** If every remaining event commits, aborts or idles and
every active proposal is validated by one mode, the run resolves the proposals as a `Round` of
`ValidationPolicies`: the committed ones are the history, and the round ends at the run's store. -/
theorem round_of_resolving {label : O → R} {mode : Finset Check} :
    ∀ (es : List (Event O R)) (s : RunState O R), (∀ e ∈ es, Resolving e) → ActiveIn mode s →
      RunValid label s es →
      Round label (fun _ => mode) s.store (resolvedProposals s.active es) (history s es)
        (final s es).store := by
  intro es
  induction es with
  | nil => intro s _ _ _; exact .done _
  | cons e es ih =>
      intro s resolving active run
      obtain ⟨valid, rest⟩ := run
      have resolvingRest : ∀ e ∈ es, Resolving e := fun e member =>
        resolving e (List.mem_cons_of_mem _ member)
      cases e with
      | commit t dropped =>
          simp only [Valid] at valid
          obtain ⟨mode', c, found, -, -, permits⟩ := valid
          have modeEq : mode' = mode := active _ (mem_of_lookup_eq_some found)
          subst modeEq
          have active' : ActiveIn mode' (next s (.commit t dropped)) := by
            intro x member
            simp only [next, found] at member
            exact active x (mem_eraseKey member)
          have := ih _ resolvingRest active' rest
          simp only [next, found] at this
          simp only [resolvedProposals, history, committedBy, found, List.singleton_append, final_cons,
            next]
          exact .commit permits this
      | abort t =>
          simp only [Valid] at valid
          obtain ⟨⟨mode', c⟩, found⟩ := valid
          have active' : ActiveIn mode (next s (.abort t)) := by
            intro x member
            exact active x (mem_eraseKey member)
          have := ih _ resolvingRest active' rest
          simp only [next] at this
          simp only [resolvedProposals, history, committedBy, found, List.nil_append, final_cons,
            next]
          exact .drop this
      | tau =>
          have := ih (next s .tau) resolvingRest active rest
          simpa [resolvedProposals, history, committedBy, next] using this
      | fire c => exact absurd (resolving _ List.mem_cons_self) (by simp [Resolving])
      | begin t m c => exact absurd (resolving _ List.mem_cons_self) (by simp [Resolving])
      | batch cs => exact absurd (resolving _ List.mem_cons_self) (by simp [Resolving])
      | observe c => exact absurd (resolving _ List.mem_cons_self) (by simp [Resolving])
      | branch b c => exact absurd (resolving _ List.mem_cons_self) (by simp [Resolving])

/-- A list of begin events. -/
def Begins : List (Event O R) → Prop
  | [] => True
  | .begin _ _ _ :: es => Begins es
  | _ :: _ => False

theorem runValid_append {label : O → R} :
    ∀ (s : RunState O R) (first second : List (Event O R)),
      RunValid label s (first ++ second) ↔
        RunValid label s first ∧ RunValid label (final s first) second := by
  intro s first second
  induction first generalizing s with
  | nil => simp [RunValid]
  | cons e rest ih => simp only [List.cons_append, RunValid, ih, final_cons, and_assoc]

theorem final_append (s : RunState O R) (first second : List (Event O R)) :
    final s (first ++ second) = final (final s first) second :=
  List.foldl_append ..

theorem history_append :
    ∀ (s : RunState O R) (first second : List (Event O R)),
      history s (first ++ second) = history s first ++ history (final s first) second := by
  intro s first second
  induction first generalizing s with
  | nil => rfl
  | cons e rest ih => simp only [List.cons_append, history, ih, final_cons, List.append_assoc]

/-- After a list of begins the store is unchanged, nothing was published, and every new active
proposal was enabled at the store with the mode of its begin. -/
theorem begins_effect {label : O → R} {mode : Finset Check} :
    ∀ (bs : List (Event O R)) (s : RunState O R), Begins bs → AllBeginsIn {mode} bs →
      RunValid label s bs →
      (final s bs).store = s.store ∧ history s bs = [] ∧
        ∀ x ∈ (final s bs).active, x ∈ s.active ∨ (x.2.1 = mode ∧ Enabled label s.store x.2.2) := by
  intro bs
  induction bs with
  | nil => intro s _ _ _; exact ⟨rfl, rfl, fun x member => Or.inl member⟩
  | cons e bs ih =>
      intro s begins modes run
      cases e with
      | begin t m c =>
          obtain ⟨valid, rest⟩ := run
          simp only [Valid] at valid
          have modeEq : m = mode := by simpa [AllBeginsIn] using modes.1
          obtain ⟨storeEq, histEq, actives⟩ := ih _ begins modes.2 rest
          refine ⟨by simpa [next] using storeEq, by simpa [history, committedBy] using histEq, ?_⟩
          intro x member
          rcases actives x member with old | ⟨xMode, enabled⟩
          · simp only [next, List.mem_cons] at old
            rcases old with rfl | old
            · exact Or.inr ⟨modeEq, valid.2.1⟩
            · exact Or.inl old
          · exact Or.inr ⟨xMode, by simpa [next] using enabled⟩
      | fire c => exact absurd begins (by simp [Begins])
      | commit t d => exact absurd begins (by simp [Begins])
      | abort t => exact absurd begins (by simp [Begins])
      | batch cs => exact absurd begins (by simp [Begins])
      | observe c => exact absurd begins (by simp [Begins])
      | branch b c => exact absurd begins (by simp [Begins])
      | tau => exact absurd begins (by simp [Begins])

theorem Enabled.dropMade {label : O → R} {store : Finset O} {c : Commit O R}
    (enabled : Enabled label store c) (dropped : Finset O) : Enabled label store (c.dropMade dropped) where
  taken_subset := enabled.taken_subset
  kept_subset := enabled.kept_subset
  apart := enabled.apart
  fresh := Finset.disjoint_of_subset_left Finset.sdiff_subset enabled.fresh
  queries_hold := enabled.queries_hold

theorem dropMade_empty (c : Commit O R) : c.dropMade ∅ = c := by
  cases c; simp [Commit.dropMade]

/-- Each resolved proposal is an active proposal, possibly without some of its fresh occurrences. -/
theorem mem_resolvedProposals :
    ∀ (es : List (Event O R)) (active : List (ℕ × Finset Check × Commit O R)) (c : Commit O R),
      c ∈ resolvedProposals active es → ∃ x ∈ active, ∃ dropped, c = x.2.2.dropMade dropped := by
  intro es
  induction es with
  | nil => intro active c member; simp [resolvedProposals] at member
  | cons e es ih =>
      intro active c member
      cases e with
      | commit t dropped =>
          simp only [resolvedProposals] at member
          split at member
          · next mode d found =>
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨_, mem_of_lookup_eq_some found, dropped, rfl⟩
            · obtain ⟨x, inX, rest⟩ := ih _ c member
              exact ⟨x, mem_eraseKey inX, rest⟩
          · exact ih _ c member
      | abort t =>
          simp only [resolvedProposals] at member
          split at member
          · next mode d found =>
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨_, mem_of_lookup_eq_some found, ∅, (dropMade_empty _).symm⟩
            · obtain ⟨x, inX, rest⟩ := ih _ c member
              exact ⟨x, mem_eraseKey inX, rest⟩
          · exact ih _ c member
      | fire d => exact ih _ c (by simpa [resolvedProposals] using member)
      | begin t m d => exact ih _ c (by simpa [resolvedProposals] using member)
      | batch cs => exact ih _ c (by simpa [resolvedProposals] using member)
      | observe d => exact ih _ c (by simpa [resolvedProposals] using member)
      | branch b d => exact ih _ c (by simpa [resolvedProposals] using member)
      | tau => exact ih _ c (by simpa [resolvedProposals] using member)

/-- **Proposals begun at one store and then resolved give a snapshot outcome.** A run from a state
with nothing active that first begins proposals in a mode and then only commits, aborts or idles is
a round of that mode over the resolved proposals, every one of which is enabled at the initial
store. In `snapshot` mode its store is therefore a `SnapshotOutcome` of those proposals, and
`snapshotOutcome_iff` characterizes it. -/
theorem round_of_beginsFirst {label : O → R} {mode : Finset Check} {s : RunState O R}
    (idle : s.active = []) {bs rs : List (Event O R)} (begins : Begins bs)
    (modes : AllBeginsIn {mode} bs) (resolving : ∀ e ∈ rs, Resolving e)
    (run : RunValid label s (bs ++ rs)) :
    let W := resolvedProposals (final s bs).active rs
    Round label (fun _ => mode) s.store W (history s (bs ++ rs)) (final s (bs ++ rs)).store ∧
      ∀ c ∈ W, Enabled label s.store c := by
  intro W
  obtain ⟨runB, runR⟩ := (runValid_append s bs rs).mp run
  obtain ⟨storeEq, histEq, actives⟩ := begins_effect bs s begins modes runB
  have activeIn : ActiveIn mode (final s bs) := by
    intro x member
    rcases actives x member with old | ⟨xMode, _⟩
    · rw [idle] at old; simp at old
    · exact xMode
  have round := round_of_resolving rs (final s bs) resolving activeIn runR
  rw [storeEq] at round
  refine ⟨?_, ?_⟩
  · rw [history_append, histEq, List.nil_append, final_append]
    exact round
  · intro c member
    obtain ⟨x, inX, dropped, rfl⟩ := mem_resolvedProposals rs _ c member
    rcases actives x inX with old | ⟨_, enabled⟩
    · rw [idle] at old; simp at old
    · exact enabled.dropMade dropped

theorem snapshotOutcome_of_beginsFirst {label : O → R} {s : RunState O R} (idle : s.active = [])
    {bs rs : List (Event O R)} (begins : Begins bs) (modes : AllBeginsIn {Mode.snapshot} bs)
    (resolving : ∀ e ∈ rs, Resolving e) (run : RunValid label s (bs ++ rs)) :
    SnapshotOutcome label s.store (resolvedProposals (final s bs).active rs)
      (final s (bs ++ rs)).store :=
  ⟨_, _, List.Perm.refl _, (round_of_beginsFirst idle begins modes resolving run).1⟩

/-! ## Serializable histories -/

/-- A history is serializable from a store when some order of its commits is executable there. -/
def SerializableHistory (label : O → R) (store : Finset O) (h : List (Commit O R)) : Prop :=
  ∃ l, l.Perm h ∧ Executable label store l

/-- **For commits matched at one store, a serializable history is an acyclic wave.** -/
theorem serializableHistory_iff_acyclic {label : O → R} {store : Finset O} {W : List (Commit O R)}
    (enabled : ∀ c ∈ W, Enabled label store c) (noClash : W.Pairwise (fun e d => ¬ Clash e d)) :
    SerializableHistory label store W ↔ Acyclic label W :=
  exists_executable_perm_iff_acyclic enabled noClash

/-- A serializable history reaches the store of its executable order: the combined effect of its
commits, when they were all matched at that store. -/
theorem SerializableHistory.fireList_eq {label : O → R} {store : Finset O} {W l : List (Commit O R)}
    (enabled : ∀ c ∈ W, Enabled label store c) (perm : l.Perm W) :
    fireList store l = fire store (effectOf W) := by
  have matched : MatchedAt store W := MatchedAt.of_enabled enabled
  rw [fireList_perm (fun c member => matched c (perm.subset member)) perm,
    fireList_eq_fire_effectOf matched]

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
