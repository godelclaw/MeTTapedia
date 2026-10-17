import Mettapedia.OSLF.MeTTaIL.Complete.Exhaustion

/-!
# Iterative deepening over a family of scheduled goals

A *family* is a scheduled goal at every depth, `goal d`, together with what its results record
(`Payload`, without proofs or depth) and which payloads are valid. Results do not store their
depth, so every valid payload is a result at every depth; it is a bounded result at the depths
covering its derivation's nesting (`required`).

The search runs the scheduled machine at depth `0, 1, 2, …`: a level runs until it drains, then,
unless it is certified, the next level starts. Its publication is the payloads already published
followed by the new payloads of the current level, so it grows by prefix as work is added.

A drained level is **certified** when no branch was cut by depth (`Exhaustion`), or when the family
has a bound on the nesting of all its derivations and the depth reaches it.

- `sound`: every published payload is valid;
- `complete_in_limit`: every valid payload is published after finitely much work;
- `exact_of_complete`: a drained, certified search has published every valid payload;
- `eventually_complete`: with a bound, the search is certified after finitely much work.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Deep

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralPremise
open StructuralDescent
open StructuralDescent.Scheduled (Goal Result Obligation)

/-- A scheduled goal at every depth, with the payload its results record. -/
structure Family where
  environment : Environment
  goal : Nat → Goal
  Payload : Type
  [decEq : DecidableEq Payload]
  read : {depth : Nat} → Result environment (goal depth) → Payload
  Valid : Payload → Prop
  read_valid : ∀ {depth : Nat} (result : Result environment (goal depth)), Valid (read result)
  build : (payload : Payload) → Valid payload → (depth : Nat) → Result environment (goal depth)
  read_build : ∀ (payload : Payload) (valid : Valid payload) (depth : Nat), read (build payload valid depth) = payload
  required : Payload → Nat
  build_ordered : ∀ (payload : Payload) (valid : Valid payload) (depth : Nat),
    required payload ≤ depth → (build payload valid depth).ordered = true
  bound : Option Nat
  bound_sound : ∀ limit, bound = some limit → ∀ payload, Valid payload → required payload ≤ limit

attribute [instance] Family.decEq

variable (family : Family)

/-- A deepening search: the depth, the scheduled search at that depth, and what was published
before it. -/
structure State where
  depth : Nat
  level : StructuralDescent.Scheduled.State family.environment (family.goal depth)
  published : List family.Payload

/-- The payloads of a list that are not yet published, in order. -/
def fresh (published answers : List family.Payload) : List family.Payload :=
  answers.filter fun payload => !published.contains payload

theorem fresh_append (published first second : List family.Payload) :
    fresh family published (first ++ second) = fresh family published first ++ fresh family published second := by
  simp [fresh, List.filter_append]

theorem mem_fresh {published answers : List family.Payload} {payload : family.Payload} :
    payload ∈ fresh family published answers ↔ payload ∈ answers ∧ payload ∉ published := by
  simp [fresh, List.mem_filter]

/-- Published payloads, then the new payloads of the current level. -/
def State.publication {family : Family} (state : State family) : List family.Payload :=
  state.published ++ fresh family state.published (state.level.answers.map family.read)

theorem mem_publication_of_mem_answers {state : State family} {payload : family.Payload}
    (member : payload ∈ state.level.answers.map family.read) : payload ∈ state.publication := by
  by_cases published : payload ∈ state.published
  · exact List.mem_append_left _ published
  · exact List.mem_append_right _ ((mem_fresh family).mpr ⟨member, published⟩)

/-- Whether an obligation is a depth cut. -/
def isCut : Obligation → Bool
  | .depthExhausted _ => true
  | _ => false

/-- A drained level is certified when no branch was cut, or the depth reaches the family's bound. -/
def certified (state : State family) : Bool :=
  !(state.level.unresolved.any isCut) ||
    match family.bound with
    | some limit => decide (limit ≤ state.depth)
    | none => false

/-- A level starts with an empty scheduled search and the publication so far. -/
def levelStart (depth : Nat) (published : List family.Payload) : State family :=
  ⟨depth, StructuralDescent.Scheduled.start family.environment (family.goal depth), published⟩

/-- The search before any work. -/
def start : State family := levelStart family 0 []

/-- Whether a state moves to the next level: its level drained and it is not certified. -/
def deepens (state : State family) : Bool :=
  state.level.agenda.isEmpty && !certified family state

/-- One unit of work: a scheduled tick, or the start of the next level. -/
def tick (state : State family) : State family :=
  if deepens family state then levelStart family (state.depth + 1) state.publication
  else { state with level := StructuralDescent.Scheduled.tick family.environment (family.goal state.depth) state.level }

/-- `work` units of work. -/
def run : Nat → State family → State family
  | 0, state => state
  | work + 1, state => run work (tick family state)

/-- The search is complete: drained and certified. -/
def State.complete {family : Family} (state : State family) : Bool :=
  state.level.agenda.isEmpty && certified family state

theorem run_add (first second : Nat) (state : State family) :
    run family (first + second) state = run family second (run family first state) := by
  induction first generalizing state with
  | zero => simp [run]
  | succ first ih => simpa only [Nat.succ_add, run] using ih (tick family state)

theorem run_succ (work : Nat) (state : State family) :
    run family (work + 1) state = tick family (run family work state) := by
  rw [run_add]
  rfl

/-! ## Publication grows by prefix -/

theorem tick_publication_prefix (state : State family) :
    state.publication <+: (tick family state).publication := by
  unfold tick
  split
  · refine ⟨[], ?_⟩
    simp [levelStart, State.publication, StructuralDescent.Scheduled.start, fresh]
  · obtain ⟨tail, grown⟩ := GeneralPremise.Scheduler.tick_answers_prefix
      (StructuralDescent.Scheduled.expand family.environment (family.goal state.depth)) state.level
    refine ⟨fresh family state.published (tail.map family.read), ?_⟩
    simp only [State.publication]
    change _ = state.published ++ fresh family state.published
      ((GeneralPremise.Scheduler.tick (StructuralDescent.Scheduled.expand family.environment
        (family.goal state.depth)) state.level).answers.map family.read)
    rw [grown, List.map_append, fresh_append, List.append_assoc]

theorem run_publication_prefix (work : Nat) (state : State family) :
    state.publication <+: (run family work state).publication := by
  induction work generalizing state with
  | zero => exact List.prefix_refl _
  | succ work ih => exact (tick_publication_prefix family state).trans (ih (tick family state))

/-! ## Soundness -/

/-- What every reached state satisfies: its level is a run of the scheduled search from its
start, and its published payloads are valid. -/
structure Good (state : State family) : Prop where
  level : ∃ work, state.level = StructuralDescent.Scheduled.run family.environment (family.goal state.depth)
    work (StructuralDescent.Scheduled.start family.environment (family.goal state.depth))
  published : ∀ payload ∈ state.published, family.Valid payload

theorem publication_valid {state : State family} (good : Good family state) :
    ∀ payload ∈ state.publication, family.Valid payload := by
  intro payload member
  rcases List.mem_append.mp member with published | current
  · exact good.published payload published
  · obtain ⟨answers, _⟩ := (mem_fresh family).mp current
    obtain ⟨result, _, rfl⟩ := List.mem_map.mp answers
    exact family.read_valid result

theorem levelStart_good (depth : Nat) {published : List family.Payload}
    (valid : ∀ payload ∈ published, family.Valid payload) : Good family (levelStart family depth published) :=
  ⟨⟨0, rfl⟩, valid⟩

theorem start_good : Good family (start family) := levelStart_good family 0 (by simp)

theorem tick_good {state : State family} (good : Good family state) : Good family (tick family state) := by
  unfold tick
  split
  · exact levelStart_good family _ (publication_valid family good)
  · obtain ⟨work, level⟩ := good.level
    refine ⟨⟨work + 1, ?_⟩, good.published⟩
    change StructuralDescent.Scheduled.tick _ _ state.level = _
    rw [level]
    unfold StructuralDescent.Scheduled.tick StructuralDescent.Scheduled.run
    rw [GeneralPremise.Scheduler.run_add]
    rfl

theorem run_good (work : Nat) {state : State family} (good : Good family state) :
    Good family (run family work state) := by
  induction work generalizing state with
  | zero => exact good
  | succ work ih => exact ih (tick_good family good)

/-- **Sound.** Every published payload is valid. -/
theorem sound (work : Nat) : ∀ payload ∈ (run family work (start family)).publication, family.Valid payload :=
  publication_valid family (run_good family work (start_good family))

/-! ## Levels drain -/

/-- A drained scheduled run is the finished one. -/
theorem drained_eq_finish (environment : Environment) (goal : Goal) (work : Nat)
    (drained : (StructuralDescent.Scheduled.run environment goal work
      (StructuralDescent.Scheduled.start environment goal)).agenda = []) :
    StructuralDescent.Scheduled.run environment goal work (StructuralDescent.Scheduled.start environment goal) =
      StructuralDescent.Scheduled.finish environment goal := by
  have finished : (StructuralDescent.Scheduled.run environment goal
      (StructuralDescent.Scheduled.treeStart environment goal).cost
      (StructuralDescent.Scheduled.start environment goal)).agenda = [] :=
    StructuralDescent.Scheduled.finish_settled environment goal
  have idle : ∀ (extra : Nat) (state : StructuralDescent.Scheduled.State environment goal), state.agenda = [] →
      StructuralDescent.Scheduled.run environment goal extra state = state := by
    intro extra
    induction extra with
    | zero => intro _ _; rfl
    | succ extra ih =>
      intro state empty
      change GeneralPremise.Scheduler.run _ extra (GeneralPremise.Scheduler.tick _ state) = state
      rw [GeneralPremise.Scheduler.tick_idle _ state empty]
      exact ih state empty
  unfold StructuralDescent.Scheduled.finish
  by_cases order : work ≤ (StructuralDescent.Scheduled.treeStart environment goal).cost
  · obtain ⟨extra, total⟩ := Nat.exists_eq_add_of_le order
    rw [total, StructuralDescent.Scheduled.run_add, idle extra _ drained]
  · obtain ⟨extra, total⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le order)
    rw [total, StructuralDescent.Scheduled.run_add] at drained ⊢
    rw [idle extra _ finished]

theorem run_levelStart (depth : Nat) (published : List family.Payload) :
    ∀ work, (∀ earlier < work, (StructuralDescent.Scheduled.run family.environment (family.goal depth) earlier
      (StructuralDescent.Scheduled.start family.environment (family.goal depth))).agenda ≠ []) →
    run family work (levelStart family depth published) =
      ⟨depth, StructuralDescent.Scheduled.run family.environment (family.goal depth) work
        (StructuralDescent.Scheduled.start family.environment (family.goal depth)), published⟩ := by
  intro work
  induction work with
  | zero => intro _; rfl
  | succ work ih =>
    intro pending
    rw [run_succ, ih (fun earlier bounded => pending earlier (Nat.lt_succ_of_lt bounded))]
    have busy := pending work (Nat.lt_succ_self work)
    have keep : deepens family ⟨depth, StructuralDescent.Scheduled.run family.environment (family.goal depth) work
        (StructuralDescent.Scheduled.start family.environment (family.goal depth)), published⟩ = false := by
      simp only [deepens, Bool.and_eq_false_iff]
      left
      simpa [List.isEmpty_iff] using busy
    unfold tick
    rw [if_neg (by simp [keep])]
    change (⟨depth, StructuralDescent.Scheduled.tick _ _ _, published⟩ : State family) = _
    congr 1
    unfold StructuralDescent.Scheduled.tick StructuralDescent.Scheduled.run
    rw [GeneralPremise.Scheduler.run_add]
    rfl

/-- The drained state of a level. -/
abbrev drainedAt (depth : Nat) (published : List family.Payload) : State family :=
  ⟨depth, StructuralDescent.Scheduled.finish family.environment (family.goal depth), published⟩

/-- Every level drains, at the finished scheduled search of its depth. -/
theorem level_drains (depth : Nat) (published : List family.Payload) :
    ∃ work, run family work (levelStart family depth published) = drainedAt family depth published := by
  let isDrained := fun work => (StructuralDescent.Scheduled.run family.environment (family.goal depth) work
    (StructuralDescent.Scheduled.start family.environment (family.goal depth))).agenda.isEmpty = true
  have settled : (StructuralDescent.Scheduled.run family.environment (family.goal depth)
      (StructuralDescent.Scheduled.treeStart family.environment (family.goal depth)).cost
      (StructuralDescent.Scheduled.start family.environment (family.goal depth))).agenda = [] :=
    StructuralDescent.Scheduled.finish_settled family.environment (family.goal depth)
  have exists_drained : ∃ work, isDrained work := ⟨_, by simpa [isDrained, List.isEmpty_iff] using settled⟩
  classical
  let first := Nat.find exists_drained
  have drained : isDrained first := Nat.find_spec exists_drained
  have pending : ∀ earlier < first, (StructuralDescent.Scheduled.run family.environment (family.goal depth) earlier
      (StructuralDescent.Scheduled.start family.environment (family.goal depth))).agenda ≠ [] := by
    intro earlier bounded empty
    exact Nat.find_min exists_drained bounded (by simpa [isDrained, List.isEmpty_iff] using empty)
  refine ⟨first, ?_⟩
  rw [run_levelStart family depth published first pending,
    drained_eq_finish _ _ first (by simpa [isDrained, List.isEmpty_iff] using drained)]

theorem drainedAt_empty (depth : Nat) (published : List family.Payload) :
    (drainedAt family depth published).level.agenda = [] :=
  StructuralDescent.Scheduled.finish_settled family.environment (family.goal depth)

/-- An uncertified drained level starts the next level with its whole publication. -/
theorem tick_deepens (depth : Nat) (published : List family.Payload)
    (uncertified : certified family (drainedAt family depth published) = false) :
    tick family (drainedAt family depth published) =
      levelStart family (depth + 1) (drainedAt family depth published).publication := by
  unfold tick
  rw [if_pos (by simp [deepens, StructuralDescent.Scheduled.finish_settled, uncertified])]

/-! ## Certified levels are exact -/

/-- The finished search at a covering depth holds the payload. -/
theorem mem_finish_of_required {payload : family.Payload} (valid : family.Valid payload) {depth : Nat}
    (enough : family.required payload ≤ depth) :
    payload ∈ (StructuralDescent.Scheduled.finish family.environment (family.goal depth)).answers.map family.read :=
  List.mem_map.mpr ⟨family.build payload valid depth,
    StructuralDescent.Scheduled.finish_contains _ _ _ (family.build_ordered payload valid depth enough),
    family.read_build payload valid depth⟩

/-- **A certified drained level is exact.** -/
theorem mem_finish_of_certified {payload : family.Payload} (valid : family.Valid payload)
    {depth : Nat} {published : List family.Payload}
    (checked : certified family (drainedAt family depth published) = true) :
    payload ∈ (StructuralDescent.Scheduled.finish family.environment (family.goal depth)).answers.map family.read := by
  unfold certified at checked
  rcases Bool.or_eq_true_iff.mp checked with uncut | bounded
  · apply List.mem_map.mpr
    refine ⟨family.build payload valid depth, ?_, family.read_build payload valid depth⟩
    apply Exhaustion.finish_contains_of_unexhausted
    intro index cut
    have : (StructuralDescent.Scheduled.finish family.environment (family.goal depth)).unresolved.any isCut = true :=
      List.any_eq_true.mpr ⟨_, cut, rfl⟩
    simp_all
  · revert bounded
    cases bounding : family.bound with
    | none => intro impossible; cases impossible
    | some limit =>
      intro bounded
      exact mem_finish_of_required family valid
        ((family.bound_sound limit bounding payload valid).trans (by simpa using bounded))

/-! ## Completeness in the limit -/

/-- Every valid payload is published, or a further level is reached. -/
theorem found_or_level {payload : family.Payload} (valid : family.Valid payload) :
    ∀ depth, (∃ work, payload ∈ (run family work (start family)).publication) ∨
      ∃ work published, run family work (start family) = levelStart family depth published := by
  intro depth
  induction depth with
  | zero => exact .inr ⟨0, [], rfl⟩
  | succ depth ih =>
    rcases ih with found | ⟨work, published, reached⟩
    · exact .inl found
    · obtain ⟨drain, drained⟩ := level_drains family depth published
      cases checked : certified family (drainedAt family depth published) with
      | true =>
        refine .inl ⟨work + drain, ?_⟩
        rw [run_add, reached, drained]
        exact mem_publication_of_mem_answers family (mem_finish_of_certified family valid checked)
      | false =>
        refine .inr ⟨work + drain + 1, (drainedAt family depth published).publication, ?_⟩
        rw [run_succ, run_add, reached, drained, tick_deepens family depth published checked]

/-- **Complete in the limit.** Every valid payload is published after finitely much work. -/
theorem complete_in_limit {payload : family.Payload} (valid : family.Valid payload) :
    ∃ work, payload ∈ (run family work (start family)).publication := by
  rcases found_or_level family valid (family.required payload) with found | ⟨work, published, reached⟩
  · exact found
  · obtain ⟨drain, drained⟩ := level_drains family (family.required payload) published
    refine ⟨work + drain, ?_⟩
    rw [run_add, reached, drained]
    exact mem_publication_of_mem_answers family (mem_finish_of_required family valid (Nat.le_refl _))

/-! ## Complete searches are exact and stable -/

/-- **A complete search is exact.** -/
theorem exact_of_complete (work : Nat) (done : (run family work (start family)).complete = true)
    {payload : family.Payload} (valid : family.Valid payload) :
    payload ∈ (run family work (start family)).publication := by
  let state := run family work (start family)
  have good : Good family state := run_good family work (start_good family)
  simp only [State.complete, Bool.and_eq_true, List.isEmpty_iff] at done
  obtain ⟨levelWork, level⟩ := good.level
  have finished : state.level = StructuralDescent.Scheduled.finish family.environment (family.goal state.depth) := by
    rw [level]
    apply drained_eq_finish
    rw [← level]
    exact done.1
  have shape : state = drainedAt family state.depth state.published := by
    cases equation : state with
    | mk depth current published =>
      rw [equation] at finished
      simp only at finished
      subst finished
      rfl
  have checked : certified family (drainedAt family state.depth state.published) = true := by
    rw [← shape]
    exact done.2
  apply mem_publication_of_mem_answers family
  change payload ∈ state.level.answers.map family.read
  rw [finished]
  exact mem_finish_of_certified family valid checked

theorem tick_complete {state : State family} (done : state.complete = true) : tick family state = state := by
  simp only [State.complete, Bool.and_eq_true] at done
  unfold tick
  rw [if_neg (by simp [deepens, done.2])]
  have idle : state.level.agenda = [] := by simpa [List.isEmpty_iff] using done.1
  change (⟨state.depth, StructuralDescent.Scheduled.tick _ _ state.level, state.published⟩ : State family) = state
  unfold StructuralDescent.Scheduled.tick
  rw [GeneralPremise.Scheduler.tick_idle _ _ idle]

theorem run_complete {state : State family} (done : state.complete = true) :
    ∀ work, run family work state = state := by
  intro work
  induction work with
  | zero => rfl
  | succ work ih => rw [run_succ, ih, tick_complete family done]

theorem complete_mono {work : Nat} (done : (run family work (start family)).complete = true)
    {later : Nat} (after : work ≤ later) : (run family later (start family)).complete = true := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le after
  rw [run_add, run_complete family done extra]
  exact done

/-- **Bounded families finish.** -/
theorem eventually_complete {limit : Nat} (bounded : family.bound = some limit) :
    ∃ work, (run family work (start family)).complete = true := by
  have reach : ∀ depth ≤ limit, (∃ work, (run family work (start family)).complete = true) ∨
      ∃ work published, run family work (start family) = levelStart family depth published := by
    intro depth
    induction depth with
    | zero => intro _; exact .inr ⟨0, [], rfl⟩
    | succ depth ih =>
      intro below
      rcases ih (Nat.le_of_succ_le below) with done | ⟨work, published, reached⟩
      · exact .inl done
      · obtain ⟨drain, drained⟩ := level_drains family depth published
        cases checked : certified family (drainedAt family depth published) with
        | true =>
          refine .inl ⟨work + drain, ?_⟩
          rw [run_add, reached, drained]
          simp [State.complete, StructuralDescent.Scheduled.finish_settled, checked]
        | false =>
          refine .inr ⟨work + drain + 1, (drainedAt family depth published).publication, ?_⟩
          rw [run_succ, run_add, reached, drained, tick_deepens family depth published checked]
  rcases reach limit (Nat.le_refl _) with done | ⟨work, published, reached⟩
  · exact done
  · obtain ⟨drain, drained⟩ := level_drains family limit published
    refine ⟨work + drain, ?_⟩
    rw [run_add, reached, drained]
    simp [State.complete, StructuralDescent.Scheduled.finish_settled, certified, bounded]

end Mettapedia.OSLF.MeTTaIL.Complete.Deep
