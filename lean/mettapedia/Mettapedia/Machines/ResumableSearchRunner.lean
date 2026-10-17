import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain

/-!
# Whole runs over a resumable search

A *search* at a state can be run with an amount of work, resumed with more, and read: its
publication is a list of receipts and its status says whether it is complete, blocked or still
pending. A search is *lawful* when resuming adds work without restarting, its publication only
grows by prefix, and every published receipt is valid at the state.

A *machine* keeps the search of its current state. A tick resumes it; when the publication
releases a receipt, the first released receipt is committed and a new search begins at its
target; otherwise the status decides whether the machine keeps running or stops. Every theorem
holds for every number of ticks; none assumes that a run terminates.

Instances: the PeTTa program driver (`GeneralLiveRunnerExecution.Spec.search`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ResumableSearchRunner

/-- Why a search's publication stops. -/
inductive Status where
  | complete
  | blocked
  | pending
  deriving DecidableEq

/-- A resumable search over states `σ`, with retained runs `Run` and receipts `Receipt`. -/
structure Search (σ Run Receipt : Type) where
  run : σ → Nat → Run
  resume : Run → Nat → Run
  publication : Run → List Receipt
  status : Run → Status
  target : Receipt → σ
  Valid : σ → Receipt → Prop

variable {σ Run Receipt : Type}

/-- Resuming adds work, publication grows by prefix, and published receipts are valid. -/
structure Search.Lawful (S : Search σ Run Receipt) : Prop where
  resume_run : ∀ state first extra, S.resume (S.run state first) extra = S.run state (first + extra)
  publication_prefix : ∀ state first extra,
    S.publication (S.run state first) <+: S.publication (S.run state (first + extra))
  sound : ∀ state work receipt, receipt ∈ S.publication (S.run state work) → S.Valid state receipt

/-- What a machine is doing. -/
inductive Phase where
  | running
  | done
  | blocked
  deriving DecidableEq

/-- The phase a run without released receipts stops in. -/
def phaseOf : Status → Phase
  | .complete => .done
  | .blocked => .blocked
  | .pending => .running

/-- A live machine: its phase, current state, the retained search there, and its history,
newest first. -/
structure Machine (σ Run Receipt : Type) where
  phase : Phase
  state : σ
  program : Run
  states : List σ
  receipts : List Receipt

namespace Machine

variable (S : Search σ Run Receipt)

/-- A machine at the source, before any work. -/
def begin (source : σ) : Machine σ Run Receipt :=
  ⟨.running, source, S.run source 0, [source], []⟩

/-- One tick: more work for the retained search, then the publication decides. -/
def tick (machine : Machine σ Run Receipt) (quantum : Nat) : Machine σ Run Receipt :=
  match machine.phase with
  | .running =>
      match S.publication (S.resume machine.program quantum) with
      | receipt :: _ =>
          ⟨.running, S.target receipt, S.run (S.target receipt) 0, S.target receipt :: machine.states,
            receipt :: machine.receipts⟩
      | [] =>
          { machine with phase := phaseOf (S.status (S.resume machine.program quantum)),
                         program := S.resume machine.program quantum }
  | .done => machine
  | .blocked => machine

/-- A page of ticks. -/
def advance : Nat → Nat → Machine σ Run Receipt → Machine σ Run Receipt
  | 0, _, machine => machine
  | ticks + 1, quantum, machine => advance ticks quantum (tick S machine quantum)

theorem advance_zero (quantum : Nat) (machine : Machine σ Run Receipt) :
    advance S 0 quantum machine = machine := rfl

theorem advance_add (first extra quantum : Nat) (machine : Machine σ Run Receipt) :
    advance S (first + extra) quantum machine = advance S extra quantum (advance S first quantum machine) := by
  induction first generalizing machine with
  | zero => simp [advance]
  | succ first ih =>
    rw [Nat.succ_add]
    exact ih _

theorem tick_done {machine : Machine σ Run Receipt} (phase : machine.phase = .done) (quantum : Nat) :
    tick S machine quantum = machine := by
  simp [tick, phase]

theorem tick_blocked {machine : Machine σ Run Receipt} (phase : machine.phase = .blocked) (quantum : Nat) :
    tick S machine quantum = machine := by
  simp [tick, phase]

end Machine

/-! ## Reached machines -/

variable (S : Search σ Run Receipt)

/-- A chronological history, newest first: it starts at one state and every committed receipt
is valid at the state before it. -/
inductive History : List σ → List Receipt → Prop
  | start (source : σ) : History [source] []
  | commit {state : σ} {states : List σ} {receipts : List Receipt} {receipt : Receipt} :
      History (state :: states) receipts → S.Valid state receipt →
      History (S.target receipt :: state :: states) (receipt :: receipts)

/-- What every machine reached from `begin` satisfies. -/
structure Reached (machine : Machine σ Run Receipt) : Prop where
  budget : ∃ work, machine.program = S.run machine.state work
  history : History S machine.states machine.receipts
  current : machine.states.head? = some machine.state
  stopped : machine.phase ≠ .running →
    S.publication machine.program = [] ∧ phaseOf (S.status machine.program) = machine.phase

variable {S}

theorem begin_reached (source : σ) : Reached S (Machine.begin S source) where
  budget := ⟨0, rfl⟩
  history := .start source
  current := rfl
  stopped := fun running => absurd rfl running

theorem tick_reached (lawful : S.Lawful) {machine : Machine σ Run Receipt} (reached : Reached S machine)
    (quantum : Nat) : Reached S (Machine.tick S machine quantum) := by
  obtain ⟨⟨work, exact⟩, history, current, stopped⟩ := reached
  unfold Machine.tick
  cases phase : machine.phase with
  | done | blocked => exact ⟨⟨work, exact⟩, history, current, stopped⟩
  | running =>
    simp only
    cases published : S.publication (S.resume machine.program quantum) with
    | cons receipt rest =>
      obtain ⟨state, states, listed⟩ : ∃ state states, machine.states = state :: states := by
        cases equation : machine.states with
        | nil => simp [equation] at current
        | cons state states => exact ⟨state, states, rfl⟩
      rw [listed] at history current
      have same : state = machine.state := by simpa using current
      have member : receipt ∈ S.publication (S.run machine.state (work + quantum)) := by
        rw [← lawful.resume_run, ← exact, published]
        exact List.mem_cons_self
      show Reached S ⟨.running, S.target receipt, S.run (S.target receipt) 0, S.target receipt :: machine.states,
        receipt :: machine.receipts⟩
      refine ⟨⟨0, rfl⟩, ?_, rfl, fun running => absurd rfl running⟩
      rw [listed]
      exact .commit history (same ▸ lawful.sound _ _ _ member)
    | nil =>
      refine ⟨⟨work + quantum, by rw [exact, lawful.resume_run]⟩, history, current, ?_⟩
      intro _
      exact ⟨published, rfl⟩

theorem advance_reached (lawful : S.Lawful) (ticks quantum : Nat) {machine : Machine σ Run Receipt}
    (reached : Reached S machine) : Reached S (Machine.advance S ticks quantum machine) := by
  induction ticks generalizing machine with
  | zero => exact reached
  | succ ticks ih => exact ih (tick_reached lawful reached quantum)

/-- **Every finite prefix** of a run from a source is a reached machine. -/
theorem run_reached (lawful : S.Lawful) (source : σ) (ticks quantum : Nat) :
    Reached S (Machine.advance S ticks quantum (Machine.begin S source)) :=
  advance_reached lawful ticks quantum (begin_reached source)

/-- The history only grows. -/
theorem tick_history_suffix (machine : Machine σ Run Receipt) (quantum : Nat) :
    machine.states <:+ (Machine.tick S machine quantum).states ∧
      machine.receipts <:+ (Machine.tick S machine quantum).receipts := by
  unfold Machine.tick
  cases machine.phase with
  | done | blocked => exact ⟨List.suffix_refl _, List.suffix_refl _⟩
  | running =>
    simp only
    split
    · exact ⟨List.suffix_cons _ _, List.suffix_cons _ _⟩
    · exact ⟨List.suffix_refl _, List.suffix_refl _⟩

theorem advance_history_suffix (ticks quantum : Nat) (machine : Machine σ Run Receipt) :
    machine.states <:+ (Machine.advance S ticks quantum machine).states ∧
      machine.receipts <:+ (Machine.advance S ticks quantum machine).receipts := by
  induction ticks generalizing machine with
  | zero => exact ⟨List.suffix_refl _, List.suffix_refl _⟩
  | succ ticks ih =>
    have first := tick_history_suffix (S := S) machine quantum
    have later := ih (Machine.tick S machine quantum)
    exact ⟨first.1.trans later.1, first.2.trans later.2⟩

/-- A history is a chain of any relation that valid receipts imply, read newest first. -/
theorem History.isChain {Step : σ → σ → Prop}
    (sound : ∀ {state : σ} {receipt : Receipt}, S.Valid state receipt → Step state (S.target receipt))
    {states : List σ} {receipts : List Receipt} (history : History S states receipts) :
    states.IsChain (fun newer older => Step older newer) := by
  induction history with
  | start source => exact List.isChain_singleton _
  | commit _ valid ih => exact List.IsChain.cons_cons (sound valid) ih

/-- **The run is a chain.** In chronological order, the states of every reached machine start
at the source and each one steps to the next. -/
theorem run_chain (lawful : S.Lawful) {Step : σ → σ → Prop}
    (sound : ∀ {state : σ} {receipt : Receipt}, S.Valid state receipt → Step state (S.target receipt))
    (source : σ) (ticks quantum : Nat) :
    let machine := Machine.advance S ticks quantum (Machine.begin S source)
    machine.states.reverse.head? = some source ∧ machine.states.reverse.IsChain Step := by
  intro machine
  have reached := run_reached lawful source ticks quantum
  obtain ⟨front, joined⟩ := (advance_history_suffix (S := S) ticks quantum (Machine.begin S source)).1
  refine ⟨?_, ?_⟩
  · change (Machine.advance S ticks quantum (Machine.begin S source)).states.reverse.head? = some source
    rw [← joined]
    simp [Machine.begin]
  · exact List.isChain_reverse.mpr (History.isChain sound reached.history)

/-- **A normal ending is exact**, given that a complete, empty search excludes every step. -/
theorem done_no_step {Step : σ → σ → Prop}
    (exact : ∀ state work, S.status (S.run state work) = .complete → S.publication (S.run state work) = [] →
      ∀ target, ¬ Step state target)
    {machine : Machine σ Run Receipt} (reached : Reached S machine) (done : machine.phase = .done) :
    ∀ target, ¬ Step machine.state target := by
  obtain ⟨work, program⟩ := reached.budget
  obtain ⟨published, phase⟩ := reached.stopped (by rw [done]; decide)
  rw [done] at phase
  have complete : S.status machine.program = .complete := by
    cases status : S.status machine.program <;> simp_all [phaseOf]
  rw [program] at published complete
  exact exact _ _ complete published

/-! ## The committed receipt is stable -/

theorem first_receipt_stable (lawful : S.Lawful) (state : σ) (work quantum extra : Nat)
    {receipt : Receipt} {rest : List Receipt}
    (released : S.publication (S.resume (S.run state work) quantum) = receipt :: rest) :
    ∃ more, S.publication (S.resume (S.run state work) (quantum + extra)) = receipt :: more := by
  rw [lawful.resume_run] at released ⊢
  have grown := lawful.publication_prefix state (work + quantum) extra
  rw [released, Nat.add_assoc] at grown
  obtain ⟨tail, joined⟩ := grown
  exact ⟨rest ++ tail, by rw [← joined]; rfl⟩

/-- A tick that commits a receipt commits the same one under any larger quantum. -/
theorem tick_commit_stable (lawful : S.Lawful) {machine : Machine σ Run Receipt} (reached : Reached S machine)
    (running : machine.phase = .running) (quantum extra : Nat) {receipt : Receipt} {rest : List Receipt}
    (released : S.publication (S.resume machine.program quantum) = receipt :: rest) :
    Machine.tick S machine (quantum + extra) = Machine.tick S machine quantum := by
  obtain ⟨work, program⟩ := reached.budget
  rw [program] at released
  obtain ⟨more, later⟩ := first_receipt_stable lawful machine.state work quantum extra released
  rw [← program] at later released
  simp only [Machine.tick, running, later, released]

/-! ## Commits along a run -/

/-- One tick does nothing to the history, or commits one receipt valid at the state. -/
theorem tick_commit_or_keep (lawful : S.Lawful) {machine : Machine σ Run Receipt} (reached : Reached S machine)
    (quantum : Nat) :
    ((Machine.tick S machine quantum).state = machine.state ∧
      (Machine.tick S machine quantum).states = machine.states ∧
      (Machine.tick S machine quantum).receipts = machine.receipts) ∨
    ∃ receipt : Receipt, S.Valid machine.state receipt ∧
      Machine.tick S machine quantum = ⟨.running, S.target receipt, S.run (S.target receipt) 0,
        S.target receipt :: machine.states, receipt :: machine.receipts⟩ := by
  obtain ⟨work, program⟩ := reached.budget
  unfold Machine.tick
  cases machine.phase with
  | done | blocked => exact .inl ⟨rfl, rfl, rfl⟩
  | running =>
    simp only
    cases published : S.publication (S.resume machine.program quantum) with
    | cons receipt rest =>
      have member : receipt ∈ S.publication (S.run machine.state (work + quantum)) := by
        rw [← lawful.resume_run, ← program, published]
        exact List.mem_cons_self
      exact .inr ⟨receipt, lawful.sound _ _ _ member, rfl⟩
    | nil => exact .inl ⟨rfl, rfl, rfl⟩

/-- **The first commit of a page.** -/
theorem exists_first_commit (lawful : S.Lawful) (quantum : Nat) :
    ∀ (ticks : Nat) (machine : Machine σ Run Receipt), Reached S machine →
    machine.receipts.length < (Machine.advance S ticks quantum machine).receipts.length →
    ∃ before ≤ ticks, ∃ receipt : Receipt, S.Valid machine.state receipt ∧
      (Machine.advance S before quantum machine).state = machine.state ∧
      (Machine.advance S before quantum machine).states = machine.states ∧
      (Machine.advance S before quantum machine).receipts = machine.receipts ∧
      Reached S (Machine.advance S before quantum machine) ∧
      Machine.tick S (Machine.advance S before quantum machine) quantum =
        ⟨.running, S.target receipt, S.run (S.target receipt) 0, S.target receipt :: machine.states,
          receipt :: machine.receipts⟩ := by
  intro ticks
  induction ticks with
  | zero => intro machine _ grown; simp [Machine.advance] at grown
  | succ ticks ih =>
    intro machine reached grown
    rcases tick_commit_or_keep lawful reached quantum with ⟨sameState, sameStates, sameReceipts⟩ |
        ⟨receipt, valid, committed⟩
    · have later : (Machine.tick S machine quantum).receipts.length <
          (Machine.advance S ticks quantum (Machine.tick S machine quantum)).receipts.length := by
        rw [sameReceipts]
        simpa [Machine.advance] using grown
      obtain ⟨before, bounded, receipt, valid, state, states, receipts, nextReached, ticked⟩ :=
        ih (Machine.tick S machine quantum) (tick_reached lawful reached quantum) later
      rw [sameState] at valid state
      rw [sameStates] at states ticked
      rw [sameReceipts] at receipts ticked
      exact ⟨before + 1, by omega, receipt, valid, state, states, receipts, nextReached, ticked⟩
    · exact ⟨0, by omega, receipt, valid, rfl, rfl, rfl, reached, committed⟩

/-- Without a commit, a page leaves the state as it was. -/
theorem advance_keep_of_no_commit (lawful : S.Lawful) (quantum : Nat) :
    ∀ (ticks : Nat) {machine : Machine σ Run Receipt}, Reached S machine →
    (Machine.advance S ticks quantum machine).receipts.length ≤ machine.receipts.length →
    (Machine.advance S ticks quantum machine).state = machine.state := by
  intro ticks
  induction ticks with
  | zero => intro _ _ _; rfl
  | succ ticks ih =>
    intro machine reached short
    rcases tick_commit_or_keep lawful reached quantum with ⟨same, _, sameReceipts⟩ | ⟨receipt, _, committed⟩
    · have rest := ih (tick_reached lawful reached quantum)
        (by rw [sameReceipts]; simpa [Machine.advance] using short)
      simpa [Machine.advance, same] using rest
    · exfalso
      have suffix := (advance_history_suffix (S := S) ticks quantum (Machine.tick S machine quantum)).2
      have longer := suffix.length_le
      rw [committed] at longer
      simp only [Machine.advance, committed, List.length_cons] at short longer
      omega

/-- A stopped machine is fixed by every page. -/
theorem advance_stopped {machine : Machine σ Run Receipt} (stopped : machine.phase ≠ .running) (quantum : Nat) :
    ∀ ticks, Machine.advance S ticks quantum machine = machine := by
  intro ticks
  induction ticks with
  | zero => rfl
  | succ ticks ih =>
    have fixed : Machine.tick S machine quantum = machine := by
      cases phase : machine.phase with
      | running => exact absurd phase stopped
      | done => exact Machine.tick_done S phase quantum
      | blocked => exact Machine.tick_blocked S phase quantum
    simp only [Machine.advance, fixed, ih]

/-- **Runs follow any relation that valid receipts imply.** -/
theorem advance_reaches (lawful : S.Lawful) {Reduces : σ → σ → Prop}
    (sound : ∀ {state : σ} {receipt : Receipt}, S.Valid state receipt → Reduces state (S.target receipt))
    (quantum : Nat) : ∀ (ticks : Nat) {machine : Machine σ Run Receipt}, Reached S machine →
    Relation.ReflTransGen Reduces machine.state (Machine.advance S ticks quantum machine).state := by
  intro ticks
  induction ticks with
  | zero => intro _ _; exact .refl
  | succ ticks ih =>
    intro machine reached
    have rest := ih (tick_reached lawful reached quantum)
    rcases tick_commit_or_keep lawful reached quantum with ⟨same, _, _⟩ | ⟨receipt, valid, committed⟩
    · rw [same] at rest
      exact rest
    · change Relation.ReflTransGen Reduces machine.state
        (Machine.advance S ticks quantum (Machine.tick S machine quantum)).state
      rw [committed] at rest ⊢
      exact Relation.ReflTransGen.head (sound valid) rest

/-- **Runs keep any property that valid receipts' targets have.** -/
theorem advance_preserves (lawful : S.Lawful) {Good : σ → Prop}
    (preserved : ∀ {state : σ} {receipt : Receipt}, S.Valid state receipt → Good (S.target receipt))
    (quantum : Nat) : ∀ (ticks : Nat) {machine : Machine σ Run Receipt}, Reached S machine →
    Good machine.state → Good (Machine.advance S ticks quantum machine).state := by
  intro ticks
  induction ticks with
  | zero => intro _ _ good; exact good
  | succ ticks ih =>
    intro machine reached good
    apply ih (tick_reached lawful reached quantum)
    rcases tick_commit_or_keep lawful reached quantum with ⟨same, _, _⟩ | ⟨receipt, valid, committed⟩
    · rw [same]; exact good
    · rw [committed]; exact preserved valid

/-! ## Progress -/

/-- Under work that settles the state, a running machine commits a receipt or stops. -/
theorem tick_decides {Settles : σ → Prop} {cost : σ → Nat}
    (settles : ∀ state work, Settles state → cost state ≤ work → S.status (S.run state work) ≠ .pending)
    (lawful : S.Lawful) {machine : Machine σ Run Receipt} (settling : Settles machine.state)
    (running : machine.phase = .running)
    (quantum : Nat) {work : Nat} (program : machine.program = S.run machine.state work)
    (enough : cost machine.state ≤ work + quantum) :
    (Machine.tick S machine quantum).receipts.length = machine.receipts.length + 1 ∨
      (Machine.tick S machine quantum).phase ≠ .running := by
  have stopped : S.status (S.resume machine.program quantum) ≠ .pending := by
    rw [program, lawful.resume_run]
    exact settles _ _ settling enough
  unfold Machine.tick
  simp only [running]
  split
  · exact .inl rfl
  · refine .inr ?_
    cases status : S.status (S.resume machine.program quantum) with
    | complete | blocked => simp [phaseOf]
    | pending => exact absurd status stopped

/-- **Every search settles in finitely many ticks.** With a positive quantum, a running reached
machine commits a receipt or stops within `cost state + 1` ticks. -/
theorem progress {Settles : σ → Prop} {cost : σ → Nat}
    (settles : ∀ state work, Settles state → cost state ≤ work → S.status (S.run state work) ≠ .pending)
    (lawful : S.Lawful) {machine : Machine σ Run Receipt} (reached : Reached S machine)
    (settling : Settles machine.state) (running : machine.phase = .running) {quantum : Nat}
    (positive : 0 < quantum) :
    ∃ ticks ≤ cost machine.state + 1,
      machine.receipts.length < (Machine.advance S ticks quantum machine).receipts.length ∨
        (Machine.advance S ticks quantum machine).phase ≠ .running := by
  obtain ⟨work, program⟩ := reached.budget
  suffices waiting : ∀ ticks, ∀ machine : Machine σ Run Receipt, Reached S machine →
      Settles machine.state → machine.phase = .running → ∀ work, machine.program = S.run machine.state work →
      cost machine.state ≤ work + ticks * quantum →
      ∃ used ≤ ticks + 1, machine.receipts.length < (Machine.advance S used quantum machine).receipts.length ∨
        (Machine.advance S used quantum machine).phase ≠ .running by
    exact waiting (cost machine.state) machine reached settling running work program
      (by have := Nat.le_mul_of_pos_right (cost machine.state) positive; omega)
  intro ticks
  induction ticks with
  | zero =>
    intro machine _ settling running work program enough
    refine ⟨1, by omega, ?_⟩
    rcases tick_decides settles lawful settling running quantum program (by omega) with committed | stopped
    · exact .inl (by simp only [Machine.advance]; omega)
    · exact .inr stopped
  | succ ticks ih =>
    intro machine reached settling running work program enough
    by_cases released : S.publication (S.resume machine.program quantum) = []
    · cases status : S.status (S.resume machine.program quantum) with
      | complete | blocked =>
        refine ⟨1, by omega, .inr ?_⟩
        simp [Machine.advance, Machine.tick, running, released, status, phaseOf]
      | pending =>
        have next : Machine.tick S machine quantum =
            { machine with program := S.resume machine.program quantum } := by
          simp [Machine.tick, running, released, status, phaseOf]
        have nextReached := tick_reached lawful reached quantum
        rw [next] at nextReached
        obtain ⟨used, bounded, result⟩ := ih { machine with program := S.resume machine.program quantum }
          nextReached settling running (work + quantum) (by rw [program, lawful.resume_run])
          (by simp only; rw [Nat.add_mul] at enough; omega)
        refine ⟨used + 1, by omega, ?_⟩
        simp only [Machine.advance, next]
        exact result
    · obtain ⟨receipt, rest, cons⟩ := List.exists_cons_of_ne_nil released
      refine ⟨1, by omega, .inl ?_⟩
      simp [Machine.advance, Machine.tick, running, cons]

/-- **Stop or commit.** Under a positive quantum, a running reached machine either stops at its
own state after some page, or after some page has committed one receipt valid at that state. -/
theorem stop_or_commit {Settles : σ → Prop} {cost : σ → Nat}
    (settles : ∀ state work, Settles state → cost state ≤ work → S.status (S.run state work) ≠ .pending)
    (lawful : S.Lawful) {machine : Machine σ Run Receipt} (reached : Reached S machine)
    (settling : Settles machine.state) (running : machine.phase = .running) {quantum : Nat}
    (positive : 0 < quantum) :
    (∃ ticks, (Machine.advance S ticks quantum machine).phase ≠ .running ∧
      (Machine.advance S ticks quantum machine).state = machine.state) ∨
    ∃ ticks, ∃ receipt : Receipt, S.Valid machine.state receipt ∧
      Machine.advance S ticks quantum machine = ⟨.running, S.target receipt, S.run (S.target receipt) 0,
        S.target receipt :: machine.states, receipt :: machine.receipts⟩ := by
  obtain ⟨ticks, _, result⟩ := progress settles lawful reached settling running positive
  by_cases grown : machine.receipts.length < (Machine.advance S ticks quantum machine).receipts.length
  · obtain ⟨before, _, receipt, valid, _, _, _, _, ticked⟩ :=
      exists_first_commit lawful quantum ticks machine reached grown
    refine .inr ⟨before + 1, receipt, valid, ?_⟩
    rw [Machine.advance_add, show Machine.advance S 1 quantum (Machine.advance S before quantum machine) =
      Machine.tick S (Machine.advance S before quantum machine) quantum from rfl, ticked]
  · rcases result with longer | stopped
    · exact absurd longer grown
    · exact .inl ⟨ticks, stopped, advance_keep_of_no_commit lawful quantum ticks reached (by omega)⟩

/-- **A state with a step commits**, when work that settles it publishes a receipt. -/
theorem tick_commits_of_published {machine : Machine σ Run Receipt} (reached : Reached S machine)
    (running : machine.phase = .running) (quantum : Nat) {work : Nat}
    (program : machine.program = S.run machine.state work)
    (published : S.publication (S.resume machine.program quantum) ≠ []) :
    ∃ receipt rest, S.publication (S.resume machine.program quantum) = receipt :: rest ∧
      Machine.tick S machine quantum = ⟨.running, S.target receipt, S.run (S.target receipt) 0,
        S.target receipt :: machine.states, receipt :: machine.receipts⟩ := by
  have _ := reached
  have _ := program
  obtain ⟨receipt, rest, cons⟩ := List.exists_cons_of_ne_nil published
  exact ⟨receipt, rest, cons, by simp only [Machine.tick, running, cons]⟩

end Mettapedia.Machines.ResumableSearchRunner
