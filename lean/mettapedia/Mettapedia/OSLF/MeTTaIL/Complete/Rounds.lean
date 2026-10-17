import Mettapedia.OSLF.MeTTaIL.Complete.Deep

/-!
# Fair rounds over deepening lanes, with a chronological log

A *lane* is a deepening search (`Complete.Deep`) named by a key, with a map from its payloads to
receipts, which may refuse a payload. A round gives every lane one unit of work, in lane order, so
no lane starves another even when its search never ends. Each payload a lane publishes for the
first time is mapped and appended to the log.

- `log_sound`: every logged receipt maps a published payload of some lane;
- `log_complete`: every published payload of every lane is logged when it maps to a receipt;
- `complete_iff`: the rounds are complete exactly when every lane is complete;
- `eventually_complete`: if every lane finishes, the rounds finish.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Rounds

variable {Key Receipt : Type} (family : Key → Deep.Family)
  (lift : (key : Key) → (family key).Payload → Option Receipt)

/-- A lane with its deepening search. -/
abbrev Entry := Σ key : Key, Deep.State (family key)

/-- The lanes with their searches, and the receipt log. -/
structure State where
  entries : List (Entry family)
  log : List Receipt

/-- One unit of work for a lane, and the receipts its newly published payloads give. -/
def advance (entry : Entry family) : Entry family × List Receipt :=
  let next := Deep.tick (family entry.1) entry.2
  (⟨entry.1, next⟩, (next.publication.drop entry.2.publication.length).filterMap (lift entry.1))

/-- One round: every lane gets one unit of work, in lane order. -/
def round (state : State family (Receipt := Receipt)) : State family (Receipt := Receipt) :=
  ⟨state.entries.map fun entry => (advance family lift entry).1,
    state.log ++ state.entries.flatMap fun entry => (advance family lift entry).2⟩

/-- `work` rounds. -/
def rounds : Nat → State family (Receipt := Receipt) → State family (Receipt := Receipt)
  | 0, state => state
  | work + 1, state => rounds work (round family lift state)

/-- The lanes before any work. -/
def begin (keys : List Key) : State family (Receipt := Receipt) :=
  ⟨keys.map fun key => ⟨key, Deep.start (family key)⟩, []⟩

/-- Every lane is drained and certified. -/
def complete (state : State family (Receipt := Receipt)) : Bool :=
  state.entries.all fun entry => entry.2.complete

theorem rounds_add (first second : Nat) (state : State family (Receipt := Receipt)) :
    rounds family lift (first + second) state = rounds family lift second (rounds family lift first state) := by
  induction first generalizing state with
  | zero => simp [rounds]
  | succ first ih => simpa only [Nat.succ_add, rounds] using ih (round family lift state)

theorem rounds_succ (work : Nat) (state : State family (Receipt := Receipt)) :
    rounds family lift (work + 1) state = round family lift (rounds family lift work state) := by
  rw [rounds_add]
  rfl

/-- After `work` rounds every lane's search is its deepening run of `work` units. -/
theorem rounds_entries (keys : List Key) (work : Nat) :
    (rounds family lift work (begin family keys)).entries =
      keys.map fun key => ⟨key, Deep.run (family key) work (Deep.start (family key))⟩ := by
  induction work with
  | zero => rfl
  | succ work ih =>
    rw [rounds_succ]
    change (rounds family lift work (begin family keys)).entries.map
      (fun entry => (advance family lift entry).1) = _
    rw [ih, List.map_map]
    apply List.map_congr_left
    intro key _
    simp only [Function.comp_apply, advance, Deep.run_succ]

theorem rounds_log_prefix (work : Nat) (state : State family (Receipt := Receipt)) :
    state.log <+: (rounds family lift work state).log := by
  induction work generalizing state with
  | zero => exact List.prefix_refl _
  | succ work ih => exact (List.prefix_append _ _).trans (ih (round family lift state))

/-- A lane's publication after some work. -/
abbrev published (key : Key) (work : Nat) : List (family key).Payload :=
  (Deep.run (family key) work (Deep.start (family key))).publication

theorem published_succ (key : Key) (work : Nat) :
    published family key (work + 1) = published family key work ++
      (published family key (work + 1)).drop (published family key work).length := by
  obtain ⟨tail, grown⟩ := Deep.tick_publication_prefix (family key)
    (Deep.run (family key) work (Deep.start (family key)))
  simp only [published, Deep.run_succ]
  rw [← grown, List.drop_left]

theorem rounds_log_succ (keys : List Key) (work : Nat) :
    (rounds family lift (work + 1) (begin family keys)).log =
      (rounds family lift work (begin family keys)).log ++
        keys.flatMap fun key =>
          ((published family key (work + 1)).drop (published family key work).length).filterMap (lift key) := by
  rw [rounds_succ]
  change (rounds family lift work (begin family keys)).log ++
    (rounds family lift work (begin family keys)).entries.flatMap (fun entry => (advance family lift entry).2) = _
  rw [rounds_entries, List.flatMap_map]
  simp only [advance, published, Deep.run_succ]

/-- **Every logged receipt maps a published payload of some lane.** -/
theorem log_sound (keys : List Key) (work : Nat) :
    ∀ receipt ∈ (rounds family lift work (begin family keys)).log,
      ∃ key ∈ keys, ∃ payload ∈ published family key work, lift key payload = some receipt := by
  induction work with
  | zero => intro receipt member; cases member
  | succ work ih =>
    intro receipt member
    rw [rounds_log_succ] at member
    rcases List.mem_append.mp member with earlier | later
    · obtain ⟨key, present, payload, found, lifted⟩ := ih receipt earlier
      refine ⟨key, present, payload, ?_, lifted⟩
      rw [published_succ]
      exact List.mem_append_left _ found
    · obtain ⟨key, present, lifted⟩ := List.mem_flatMap.mp later
      obtain ⟨payload, fresh, given⟩ := List.mem_filterMap.mp lifted
      exact ⟨key, present, payload, List.mem_of_mem_drop fresh, given⟩

/-- **Every published payload of every lane is logged** when it maps to a receipt. -/
theorem log_complete (keys : List Key) (work : Nat) :
    ∀ key ∈ keys, ∀ payload ∈ published family key work, ∀ receipt, lift key payload = some receipt →
      receipt ∈ (rounds family lift work (begin family keys)).log := by
  induction work with
  | zero =>
    intro key _ payload found
    simp [published, Deep.run, Deep.start, Deep.levelStart, Deep.State.publication,
      StructuralDescent.Scheduled.start, Deep.fresh] at found
  | succ work ih =>
    intro key present payload found receipt lifted
    rw [rounds_log_succ]
    rw [published_succ] at found
    rcases List.mem_append.mp found with earlier | fresh
    · exact List.mem_append_left _ (ih key present payload earlier receipt lifted)
    · exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨key, present, List.mem_filterMap.mpr ⟨payload, fresh, lifted⟩⟩)

theorem complete_iff (keys : List Key) (work : Nat) :
    complete family (rounds family lift work (begin family keys)) = true ↔
      ∀ key ∈ keys, (Deep.run (family key) work (Deep.start (family key))).complete = true := by
  unfold complete
  rw [rounds_entries, List.all_map, List.all_eq_true]
  rfl

theorem complete_mono (keys : List Key) {work : Nat}
    (done : complete family (rounds family lift work (begin family keys)) = true)
    {later : Nat} (after : work ≤ later) :
    complete family (rounds family lift later (begin family keys)) = true := by
  rw [complete_iff] at done ⊢
  exact fun key present => Deep.complete_mono _ (done key present) after

/-- **If every lane finishes, the rounds finish.** -/
theorem eventually_complete (keys : List Key)
    (finishes : ∀ key ∈ keys, ∃ work, (Deep.run (family key) work (Deep.start (family key))).complete = true) :
    ∃ work, complete family (rounds family lift work (begin family keys)) = true := by
  suffices every : ∀ listed : List Key, (∀ key ∈ listed, ∃ work,
      (Deep.run (family key) work (Deep.start (family key))).complete = true) →
      ∃ work, ∀ key ∈ listed, (Deep.run (family key) work (Deep.start (family key))).complete = true by
    obtain ⟨work, done⟩ := every keys finishes
    exact ⟨work, (complete_iff family lift keys work).mpr done⟩
  intro listed
  induction listed with
  | nil => intro _; exact ⟨0, fun _ absent => by cases absent⟩
  | cons key rest ih =>
    intro finishing
    obtain ⟨first, done⟩ := finishing key List.mem_cons_self
    obtain ⟨later, restDone⟩ := ih (fun other member => finishing other (List.mem_cons_of_mem _ member))
    refine ⟨max first later, ?_⟩
    intro other member
    rcases List.mem_cons.mp member with rfl | inRest
    · exact Deep.complete_mono _ done (Nat.le_max_left _ _)
    · exact Deep.complete_mono _ (restDone other inRest) (Nat.le_max_right _ _)

end Mettapedia.OSLF.MeTTaIL.Complete.Rounds
