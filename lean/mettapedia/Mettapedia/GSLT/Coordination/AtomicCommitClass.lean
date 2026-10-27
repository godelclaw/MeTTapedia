import Mettapedia.GSLT.Coordination.CrashConsensusImpossibility

/-!
# Every atomic commit protocol blocks: a theorem over the class of protocols

`AtomicCommitBlocking` showed two-phase commit's blocking on two hand-built runs. This module proves
it for every protocol, in the asynchronous model of `CrashConsensusImpossibility`: `n ≥ 2`
deterministic processes, messages delayed without bound, one process may crash.

Each process starts with a **vote** (its input: `true` for yes) and may output a **decision**
(`true` for commit, `false` for abort).

* **Abort validity** (`AbortValidity`): if some process votes no, no process ever decides commit.
* **Commit validity** (`CommitValidity`): if every process votes yes and no process crashes, no
  process ever decides abort.
* **Non-blocking** (`NonBlocking`): in every run in which one process has crashed at the start,
  every other process decides.

## The theorem

* **No protocol has all three** (`atomic_commit_blocks`): every protocol with both validities has a
  run in which one process crashes at the start and some correct process never decides. Agreement
  is not even needed: the validities alone force every correct process to wait for every vote.

The argument: let process `0` vote no and crash at the start. Some other process `1` must decide,
and by abort validity it decides abort, after finitely many steps of the others. Those steps run
alike when `0` votes yes instead, since `0` took no step and its vote travelled nowhere
(`CrashConsensusImpossibility.agree_run`). Extend them by a fair run in which `0` is merely slow
(`roundRun`): all voted yes, nobody crashed, and `1` has decided abort, against commit validity.

So a protocol must give up one of the three: it waits for a crashed participant (two-phase commit
blocks), or it aborts transactions that every participant accepted (a timeout that guesses), or
it replaces each participant by a group that does not crash as a whole (a replicated owner,
`OwnerFailover`, and deterministic ordering, `DeterministicOrdering`).

## Positive control

`Controls.coordinator` is a protocol in the class: process `1` sends its vote to process `0`,
which decides the conjunction of the two votes and sends the decision back. It has both validities
(`Controls.coordinator_abortValidity`, `Controls.coordinator_commitValidity`), so the theorem
applies to it: it blocks (`Controls.coordinator_blocks`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.AtomicCommitClass

open Mettapedia.GSLT.Coordination.CrashConsensusImpossibility

universe u v

variable {n : ℕ} {S : Type u} {M : Type v} [DecidableEq M]

/-! ## Fair runs from any configuration -/

section RoundRobin

variable (P : Protocol n S M)

/-- The configurations of the round-robin run: in block `k` the process whose turn it is receives
every envelope waiting for it and takes a step. Nobody crashes. -/
noncomputable def roundConfig (positive : 0 < n) (C : Config n S M) : ℕ → Config n S M
  | 0 => C
  | k + 1 => run P (roundConfig positive C k) (stageEvents (roundConfig positive C k) (turn positive k))

/-- The round-robin run from `C`. -/
noncomputable def roundRun (positive : 0 < n) (C : Config n S M) : BlockRun n S M where
  start := C
  blocks k := stageEvents (roundConfig P positive C k) (turn positive k)

theorem roundRun_config (positive : 0 < n) (C : Config n S M) (k : ℕ) :
    configAt P (roundRun P positive C) k = roundConfig P positive C k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show run P (configAt P (roundRun P positive C) k) ((roundRun P positive C).blocks k) = _
      rw [ih]
      rfl

theorem roundRun_valid (positive : 0 < n) (C : Config n S M) : Valid P (roundRun P positive C) := by
  intro k
  rw [roundRun_config]
  exact runs_stageEvents _ _

/-- **The round-robin run is fair.** -/
theorem roundRun_fair (positive : 0 < n) (C : Config n S M) : Fair P (roundRun P positive C) := by
  refine ⟨fun q k => ?_, fun k env member => ?_⟩
  · obtain ⟨j, le, isTurn⟩ := next_turn positive k q
    have turnIs : turn positive j = q := Fin.ext isTurn
    refine ⟨j, le, .null q, ?_, rfl⟩
    simp only [roundRun, turnIs]
    simp [stageEvents]
  · obtain ⟨j, le, isTurn⟩ := next_turn positive k env.dest
    have turnIs : turn positive j = env.dest := Fin.ext isTurn
    by_cases present : env ∈ (configAt P (roundRun P positive C) j).buffer
    · refine ⟨j, le, ?_⟩
      simp only [roundRun, turnIs]
      rw [roundRun_config] at present
      exact deliver_mem_stageEvents present
    · obtain ⟨i, low, _, delivered⟩ := delivered_between member j le present
      exact ⟨i, low, delivered⟩

/-- A finite schedule followed by a run. -/
def prefixed (C : Config n S M) (σ : List (Event n M)) (r : BlockRun n S M) : BlockRun n S M where
  start := C
  blocks k := if k = 0 then σ else r.blocks (k - 1)

theorem prefixed_config (C : Config n S M) (σ : List (Event n M)) (r : BlockRun n S M)
    (starts : r.start = run P C σ) : ∀ k, configAt P (prefixed C σ r) (k + 1) = configAt P r k := by
  intro k
  induction k with
  | zero => show run P C σ = r.start; rw [starts]
  | succ k ih =>
      show run P (configAt P (prefixed C σ r) (k + 1)) ((prefixed C σ r).blocks (k + 1)) = _
      rw [ih]
      rfl

/-- **A fair run after a finite schedule is fair**, when the schedule starts with nothing in
transit. -/
theorem prefixed_fair (C : Config n S M) (empty : C.buffer = ∅) (σ : List (Event n M))
    (r : BlockRun n S M) (starts : r.start = run P C σ) (fair : Fair P r) :
    Fair P (prefixed C σ r) := by
  refine ⟨fun q k => ?_, fun k env member => ?_⟩
  · obtain ⟨j, le, e, inBlock, isQ⟩ := fair.1 q k
    exact ⟨j + 1, by omega, e, by simpa [prefixed] using inBlock, isQ⟩
  · cases k with
    | zero => simp [prefixed, configAt, empty] at member
    | succ k =>
        rw [prefixed_config P C σ r starts] at member
        obtain ⟨j, le, delivered⟩ := fair.2 k env member
        exact ⟨j + 1, by omega, by simpa [prefixed] using delivered⟩

theorem prefixed_valid (C : Config n S M) (σ : List (Event n M)) (runsσ : Runs P C σ)
    (r : BlockRun n S M) (starts : r.start = run P C σ) (valid : Valid P r) :
    Valid P (prefixed C σ r) := by
  intro k
  cases k with
  | zero => exact runsσ
  | succ k =>
      rw [prefixed_config P C σ r starts]
      simpa [prefixed] using valid k

end RoundRobin

/-! ## The requirements -/

variable (P : Protocol n S M)

/-- **Abort validity**: if some process votes no, no process ever decides commit. -/
def AbortValidity : Prop :=
  ∀ inputs : Fin n → Bool, (∃ p, inputs p = false) → ∀ σ, Runs P (initial P inputs) σ →
    ∀ q, P.output ((run P (initial P inputs) σ).state q) ≠ some true

/-- **Commit validity**: if every process votes yes and nobody crashes, no process ever decides
abort. -/
def CommitValidity : Prop :=
  ∀ r : BlockRun n S M, r.start = initial P (fun _ => true) → Valid P r → Fair P r →
    ∀ k q, P.output ((configAt P r k).state q) ≠ some false

/-- **Non-blocking**: in every run in which one process has crashed at the start, every other
process decides. -/
def NonBlocking : Prop :=
  ∀ (inputs : Fin n → Bool) (p : Fin n) (r : BlockRun n S M), r.start = initial P inputs →
    Valid P r → FairExcept P p r → ∀ q, q ≠ p → ∃ k value, P.output ((configAt P r k).state q) = some value

/-- **No atomic commit protocol is non-blocking**: abort validity, commit validity and
non-blocking termination cannot hold together, for any protocol with at least two processes. -/
theorem not_nonBlocking (two : 2 ≤ n) (abortValid : AbortValidity P) (commitValid : CommitValidity P) :
    ¬ NonBlocking P := by
  intro nonBlocking
  have positive : 0 < n := by omega
  set crashed : Fin n := ⟨0, positive⟩
  set other : Fin n := ⟨1, by omega⟩
  have apart : other ≠ crashed := fun h => by simp [crashed, other, Fin.ext_iff] at h
  set noVote : Fin n → Bool := fun i => decide (i ≠ crashed)
  -- the crashed process voted no: the other decides, and decides abort
  set r := crashRun (P := P) positive crashed (initial P noVote)
  obtain ⟨k, value, decided⟩ := nonBlocking noVote crashed r rfl (crashRun_valid positive crashed _)
    (crashRun_fair positive crashed _) other apart
  set σ := prefixBlocks r k
  have runsσ : Runs P (initial P noVote) σ := runs_prefix (crashRun_valid positive crashed _) k
  have atK : configAt P r k = run P (initial P noVote) σ := configAt_prefix (P := P) r k
  have isAbort : value = false := by
    have := abortValid noVote ⟨crashed, by simp [noVote]⟩ σ runsσ other
    rw [← atK, decided] at this
    cases value
    · rfl
    · exact absurd rfl this
  subst isAbort
  -- the same steps run alike when the crashed process voted yes
  have avoids : Avoids crashed σ := avoids_prefix (crashRun_fair (P := P) positive crashed _).2.2 k
  have agree : AgreeExcept crashed (initial P noVote) (initial P (fun _ => true)) :=
    ⟨rfl, rfl, fun q apart' => by simp [initial, noVote, apart']⟩
  obtain ⟨runsYes, agreeAfter⟩ := agree_run σ _ _ agree avoids runsσ
  have sameOther : (run P (initial P (fun _ => true)) σ).state other =
      (run P (initial P noVote) σ).state other := (agreeAfter.state other apart).symm
  -- extend by a fair run: everyone voted yes, nobody crashed, and `other` decided abort
  set rest := roundRun P positive (run P (initial P (fun _ => true)) σ)
  have fairWhole := prefixed_fair P (initial P (fun _ => true)) rfl σ rest rfl
    (roundRun_fair P positive _)
  have validWhole := prefixed_valid P (initial P (fun _ => true)) σ runsYes rest rfl
    (roundRun_valid P positive _)
  have := commitValid (prefixed (initial P (fun _ => true)) σ rest) rfl validWhole fairWhole 1 other
  apply this
  rw [show (1 : ℕ) = 0 + 1 from rfl, prefixed_config P _ σ rest rfl]
  show P.output ((configAt P rest 0).state other) = some false
  show P.output ((run P (initial P (fun _ => true)) σ).state other) = some false
  rw [sameOther, ← atK]
  exact decided

/-- **Every atomic commit protocol blocks**: with both validities, some run in which one process
crashes at the start leaves a correct process undecided forever. -/
theorem atomic_commit_blocks (two : 2 ≤ n) (abortValid : AbortValidity P)
    (commitValid : CommitValidity P) :
    ∃ (inputs : Fin n → Bool) (p : Fin n) (r : BlockRun n S M), r.start = initial P inputs ∧
      Valid P r ∧ FairExcept P p r ∧ ∃ q, q ≠ p ∧ ∀ k, P.output ((configAt P r k).state q) = none := by
  have := not_nonBlocking P two abortValid commitValid
  unfold NonBlocking at this
  push Not at this
  obtain ⟨inputs, p, r, start, valid, fair, q, apart, never⟩ := this
  refine ⟨inputs, p, r, start, valid, fair, q, apart, fun k => ?_⟩
  cases h : P.output ((configAt P r k).state q) with
  | none => rfl
  | some value => exact absurd h (never k value)

/-! ## Positive control: a coordinator protocol -/

namespace Controls

/-- The messages: a vote, or a decision. -/
inductive CMsg where
  | vote (v : Bool)
  | decision (d : Bool)
  deriving DecidableEq

/-- A process's state: its vote and its decision. -/
abbrev CState := Bool × Option Bool

/-- Process `1` sends its vote to process `0` on every step on nothing; process `0` decides the
conjunction of both votes when the vote arrives and sends the decision; process `1` adopts the
decision when it arrives. -/
def coordStep (p : Fin 2) (s : CState) (m : Option CMsg) : CState × List (Fin 2 × CMsg) :=
  if p = 0 then
    match m with
    | some (.vote v) => if s.2 = none then ((s.1, some (s.1 && v)), [(1, .decision (s.1 && v))]) else (s, [])
    | _ => (s, [])
  else
    match m with
    | none => (s, [(0, .vote s.1)])
    | some (.decision d) => if s.2 = none then ((s.1, some d), []) else (s, [])
    | some (.vote _) => (s, [])

theorem coordStep_stable (p : Fin 2) (s : CState) (m : Option CMsg) (value : Bool)
    (decided : s.2 = some value) : (coordStep p s m).1.2 = some value := by
  unfold coordStep
  split_ifs <;> (try split) <;> simp_all

/-- The coordinator protocol. -/
def coordinator : Protocol 2 CState CMsg where
  init _ v := (v, none)
  step := coordStep
  output s := s.2
  output_stable p s m value decided := coordStep_stable p s m value decided

theorem mem_stamp_content {sender : Fin 2} {seq : ℕ} :
    ∀ {i : ℕ} {sent : List (Fin 2 × CMsg)} {env : Envelope 2 CMsg},
      env ∈ stamp sender seq i sent → (env.dest, env.content) ∈ sent := by
  intro i sent
  induction sent generalizing i with
  | nil => intro env member; simp [stamp] at member
  | cons head rest ih =>
      intro env member
      obtain ⟨dest, content⟩ := head
      simp only [stamp, List.mem_cons] at member
      rcases member with rfl | member
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih member)

/-- What every reachable configuration from given votes satisfies: votes kept, every decision the
conjunction of the votes, and every message in transit a true vote of process `1` or that
decision. -/
structure Good (inputs : Fin 2 → Bool) (C : Config 2 CState CMsg) : Prop where
  votes : ∀ q, (C.state q).1 = inputs q
  decisions : ∀ q d, (C.state q).2 = some d → d = (inputs 0 && inputs 1)
  messages : ∀ env ∈ C.buffer, env.content = .vote (inputs 1) ∨ env.content = .decision (inputs 0 && inputs 1)

theorem good_initial (inputs : Fin 2 → Bool) : Good inputs (initial coordinator inputs) where
  votes _ := rfl
  decisions _ _ h := by simp [initial, coordinator] at h
  messages _ h := by simp [initial] at h

/-- One step keeps a process's part of the invariant. -/
theorem coordStep_good (inputs : Fin 2 → Bool) (p : Fin 2) (s : CState) (m : Option CMsg)
    (vote : s.1 = inputs p) (decision : ∀ d, s.2 = some d → d = (inputs 0 && inputs 1))
    (message : ∀ x, m = some x → x = .vote (inputs 1) ∨ x = .decision (inputs 0 && inputs 1)) :
    (coordStep p s m).1.1 = inputs p ∧
      (∀ d, (coordStep p s m).1.2 = some d → d = (inputs 0 && inputs 1)) ∧
      ∀ x ∈ (coordStep p s m).2, x.2 = .vote (inputs 1) ∨ x.2 = .decision (inputs 0 && inputs 1) := by
  obtain ⟨own, decided⟩ := s
  simp only at vote decision
  subst vote
  fin_cases p
  · -- the coordinator
    rcases m with _ | (v | d)
    · simp [coordStep]; simpa using decision
    · rcases message _ rfl with h | h
      · injection h with h
        subst h
        by_cases none' : decided = none
        · subst none'; simp [coordStep]
        · simp [coordStep, none']; simpa using decision
      · cases h
    · simp [coordStep]; simpa using decision
  · -- the participant
    rcases m with _ | (v | d)
    · simp [coordStep]; simpa using decision
    · simp [coordStep]; simpa using decision
    · rcases message _ rfl with h | h
      · cases h
      · injection h with h
        subst h
        by_cases none' : decided = none
        · subst none'; simp [coordStep]
        · simp [coordStep, none']; simpa using decision

theorem good_apply {inputs : Fin 2 → Bool} {C : Config 2 CState CMsg} (good : Good inputs C)
    {e : Event 2 CMsg} (applicable : Applicable C e) : Good inputs (apply coordinator C e) := by
  have received : ∀ m, e.received = some m →
      m = .vote (inputs 1) ∨ m = .decision (inputs 0 && inputs 1) := by
    intro m h
    cases e with
    | null _ => simp [Event.received] at h
    | deliver env =>
        simp only [Event.received, Option.some.injEq] at h
        subst h
        exact good.messages env applicable
  obtain ⟨stateVote, stateDecision, sentOk⟩ := coordStep_good inputs e.proc (C.state e.proc) e.received
    (good.votes e.proc) (good.decisions e.proc) received
  refine ⟨fun q => ?_, fun q d h => ?_, fun env member => ?_⟩
  · simp only [apply_state, Function.update_apply]
    split_ifs with same
    · subst same; exact stateVote
    · exact good.votes q
  · simp only [apply_state, Function.update_apply] at h
    split_ifs at h with same
    · exact stateDecision d h
    · exact good.decisions q d h
  · rw [apply_buffer] at member
    rcases Finset.mem_union.mp member with old | new
    · have inBuffer : env ∈ C.buffer := by
        cases e with
        | deliver d => exact Finset.mem_of_mem_erase old
        | null _ => exact old
      exact good.messages env inBuffer
    · exact sentOk _ (mem_stamp_content (List.mem_toFinset.mp new))

theorem good_run {inputs : Fin 2 → Bool} :
    ∀ (σ : List (Event 2 CMsg)) (C : Config 2 CState CMsg), Good inputs C → Runs coordinator C σ →
      Good inputs (run coordinator C σ) := by
  intro σ
  induction σ with
  | nil => exact fun _ good _ => good
  | cons e rest ih => exact fun C good runs => ih _ (good_apply good runs.1) runs.2

/-- **The coordinator protocol has abort validity.** -/
theorem coordinator_abortValidity : AbortValidity coordinator := by
  intro inputs someNo σ runs q decided
  have := (good_run σ _ (good_initial inputs) runs).decisions q true decided
  obtain ⟨p, isNo⟩ := someNo
  have both : inputs 0 = true ∧ inputs 1 = true := by
    simp only [eq_comm (a := true), Bool.and_eq_true] at this; exact this
  rcases (by omega : p.val = 0 ∨ p.val = 1) with h | h
  · rw [show p = 0 from Fin.ext h] at isNo; rw [isNo] at both; exact absurd both.1 (by decide)
  · rw [show p = 1 from Fin.ext h] at isNo; rw [isNo] at both; exact absurd both.2 (by decide)

/-- **The coordinator protocol has commit validity.** -/
theorem coordinator_commitValidity : CommitValidity coordinator := by
  intro r start valid _ k q decided
  have runs := runs_prefix valid k
  rw [start] at runs
  have atK := configAt_prefix (P := coordinator) r k
  rw [start] at atK
  rw [atK] at decided
  have := (good_run _ _ (good_initial (fun _ => true)) runs).decisions q false decided
  simp at this

/-- **So the coordinator protocol blocks**: some run with one crash leaves a correct process
undecided forever. -/
theorem coordinator_blocks :
    ∃ (inputs : Fin 2 → Bool) (p : Fin 2) (r : BlockRun 2 CState CMsg),
      r.start = initial coordinator inputs ∧ Valid coordinator r ∧ FairExcept coordinator p r ∧
        ∃ q, q ≠ p ∧ ∀ k, coordinator.output ((configAt coordinator r k).state q) = none :=
  atomic_commit_blocks coordinator le_rfl coordinator_abortValidity coordinator_commitValidity

/-! ### Non-blocking, with and without -/

open CrashConsensusImpossibility.Controls in
/-- **Non-blocking, positive**: when every process outputs its own input at once, whoever crashes,
every other process has decided. (Validity fails for it, as `not_nonBlocking` requires.) -/
theorem ownInput_nonBlocking : NonBlocking (frozenProtocol fun _ input => some input) := by
  intro inputs p r start _ _ q _
  exact ⟨0, inputs q, by rw [configAt, start]; rfl⟩

/-- Process `1` steps on nothing in every block; process `0` has crashed. -/
def onlyOneSteps (start : Config 2 (Option Bool) Unit) : BlockRun 2 (Option Bool) Unit :=
  ⟨start, fun _ => [.null 1]⟩

open CrashConsensusImpossibility.Controls in
/-- **Non-blocking, negative**: when nobody ever outputs, process `1` stays undecided in the run in
which process `0` has crashed and process `1` steps forever. -/
theorem neverDecides_blocks : ¬ NonBlocking (frozenProtocol fun _ _ => none) := by
  intro nonBlocking
  have valid : Valid (frozenProtocol fun _ _ => none)
      (onlyOneSteps (initial (frozenProtocol fun _ _ => none) fun _ => false)) :=
    fun _ => ⟨trivial, trivial⟩
  have fairExcept : FairExcept (frozenProtocol fun _ _ => none) 0
      (onlyOneSteps (initial (frozenProtocol fun _ _ => none) fun _ => false)) := by
    refine ⟨fun q apart k => ⟨k, le_rfl, .null 1, by simp [onlyOneSteps], ?_⟩,
      fun k env member _ => ?_, fun k e member => ?_⟩
    · fin_cases q
      · exact absurd rfl apart
      · rfl
    · have := (frozenProtocol_configAt _ _ k).2 member
      simp [onlyOneSteps, initial] at this
    · simp only [onlyOneSteps, List.mem_singleton] at member
      subst member
      decide
  obtain ⟨k, value, h⟩ := nonBlocking (fun _ => false) 0 _ rfl valid fairExcept 1 (by decide)
  rw [(frozenProtocol_configAt _ _ k).1] at h
  simp [onlyOneSteps, initial, frozenProtocol] at h

end Controls

end Mettapedia.GSLT.Coordination.AtomicCommitClass
