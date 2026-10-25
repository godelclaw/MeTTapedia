import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# The turn loop of a tool-using coding agent

A turn alternates model replies and tool executions. Two independently built
coding agents end a turn on the same condition: the latest reply calls no tool,
and no user input is waiting. Neither caps the number of steps. Input that
arrives while a turn runs is kept, and reaches the model by one of two
policies:

* **boundary** — a reply already requested is still applied, and the input is
  folded in before the next request;
* **preempt** — the reply in flight is discarded unapplied, and the next
  request already contains the input.

The model and the tools are arbitrary functions, so nothing here depends on a
provider. A turn has three operations: `arrive` (an input arrives), `ask` (the
pending inputs are folded into the conversation and a reply is requested), and
`commit` (the reply in flight is applied: its tool calls run and their results
are recorded, or, for a reply without calls, the turn may end).

Proved:

* a commit ends the turn exactly when the reply calls no tool and nothing is
  pending (`commit_done_iff`);
* under either policy, every input that arrives before the turn ends is in the
  final conversation (`arrived_mem_log_of_done`);
* tool results are recorded in call order (`commit_results_in_call_order`);
* under `preempt`, no tool of a discarded reply ever runs
  (`preempt_discards_inflight`); under `boundary`, no requested reply is
  discarded (`boundary_keeps_inflight`).

Termination is not a theorem: it depends on the model eventually replying
without tools. Every operation is total.
-/

set_option autoImplicit false

namespace Mettapedia.CogArch.Agent.CodingAgent.TurnLoop

universe u v w

/-- One conversation event, oldest first in a log. -/
inductive Event (Input : Type u) (Call : Type v) (Result : Type w) where
  | input (x : Input)
  | reply (calls : List Call)
  | result (c : Call) (r : Result)

/-- How input that arrives during a requested reply reaches the model. -/
inductive Policy where
  | boundary
  | preempt
  deriving DecidableEq

variable {Input : Type u} {Call : Type v} {Result : Type w}

/-- The state of one turn. `inflight` is the reply requested and not yet
applied; `pending` are inputs that arrived and are not yet in the log. -/
structure State (Input : Type u) (Call : Type v) (Result : Type w) where
  log : List (Event Input Call Result)
  pending : List Input
  inflight : Option (List Call)
  done : Bool

/-- A fresh turn over an existing conversation. -/
def start (log : List (Event Input Call Result)) : State Input Call Result :=
  ⟨log, [], none, false⟩

/-- An input arrives. After the turn has ended it belongs to the next turn and
is not recorded here. Under `preempt`, a reply in flight is discarded. -/
def arrive (policy : Policy) (x : Input) (s : State Input Call Result) :
    State Input Call Result :=
  if s.done then s
  else
    { s with
      pending := s.pending ++ [x]
      inflight := if policy = Policy.preempt then none else s.inflight }

/-- Fold the pending inputs into the log and request a reply from `model`,
which sees exactly the folded log. Without effect if a reply is already in
flight or the turn is over. -/
def ask (model : List (Event Input Call Result) → List Call)
    (s : State Input Call Result) : State Input Call Result :=
  if s.done then s
  else
    match s.inflight with
    | some _ => s
    | none =>
      let log := s.log ++ s.pending.map Event.input
      ⟨log, [], some (model log), false⟩

/-- Apply the reply in flight: record it, run its tool calls with `tool` and
record their results in call order. A reply without calls ends the turn unless
input is pending. Without effect if nothing is in flight. -/
def commit (tool : Call → Result) (s : State Input Call Result) :
    State Input Call Result :=
  match s.inflight with
  | none => s
  | some calls =>
    { s with
      log := s.log ++ Event.reply calls :: calls.map (fun c => Event.result c (tool c))
      inflight := none
      done := calls.isEmpty && s.pending.isEmpty }

/-- One operation of a run. -/
inductive Op (Input : Type u) where
  | arrive (x : Input)
  | ask
  | commit

/-- Apply one operation. -/
def apply (policy : Policy) (model : List (Event Input Call Result) → List Call)
    (tool : Call → Result) : Op Input → State Input Call Result → State Input Call Result
  | Op.arrive x => arrive policy x
  | Op.ask => ask model
  | Op.commit => commit tool

/-- Apply a run of operations, first to last. -/
def run (policy : Policy) (model : List (Event Input Call Result) → List Call)
    (tool : Call → Result) (ops : List (Op Input)) (s : State Input Call Result) :
    State Input Call Result :=
  ops.foldl (fun state op => apply policy model tool op state) s

/-- The inputs a run delivers to the turn: arrivals before the turn ends. -/
def arrived (policy : Policy) (model : List (Event Input Call Result) → List Call)
    (tool : Call → Result) : List (Op Input) → State Input Call Result → List Input
  | [], _ => []
  | op :: ops, s =>
    let here := match op with
      | Op.arrive x => if s.done then [] else [x]
      | _ => []
    here ++ arrived policy model tool ops (apply policy model tool op s)

/-! ## Stopping -/

/-- A commit ends the turn exactly when the reply in flight calls no tool and
no input is pending. -/
theorem commit_done_iff (tool : Call → Result) (s : State Input Call Result)
    (calls : List Call) (h : s.inflight = some calls) :
    (commit tool s).done = true ↔ calls = [] ∧ s.pending = [] := by
  simp [commit, h, List.isEmpty_iff]

/-- Only a commit ends a turn: arrivals and requests never set `done`. -/
theorem arrive_done (policy : Policy) (x : Input) (s : State Input Call Result) :
    (arrive policy x s).done = s.done := by
  unfold arrive; split <;> simp

theorem ask_done (model : List (Event Input Call Result) → List Call)
    (s : State Input Call Result) : (ask model s).done = s.done := by
  unfold ask
  split
  · rfl
  · split <;> simp_all

/-! ## Results are recorded in call order -/

/-- The tool results a commit records name exactly the calls of the reply, in
order, each with the tool's result. -/
theorem commit_results_in_call_order (tool : Call → Result)
    (s : State Input Call Result) (calls : List Call) (h : s.inflight = some calls) :
    (commit tool s).log =
      s.log ++ Event.reply calls :: calls.map (fun c => Event.result c (tool c)) := by
  simp [commit, h]

/-! ## No input is lost -/

/-- The bookkeeping invariant: every delivered input is pending or in the log,
and a finished turn has nothing pending. -/
def Holds (s : State Input Call Result) (xs : List Input) : Prop :=
  (∀ x ∈ xs, x ∈ s.pending ∨ Event.input x ∈ s.log) ∧ (s.done = true → s.pending = [])

/-- Log entries are never removed. -/
theorem log_prefix_apply (policy : Policy) (model : List (Event Input Call Result) → List Call)
    (tool : Call → Result) (op : Op Input) (s : State Input Call Result) :
    ∃ suffix, (apply policy model tool op s).log = s.log ++ suffix := by
  cases op with
  | arrive x =>
    refine ⟨[], ?_⟩
    cases hd : s.done <;> simp [apply, arrive, hd]
  | ask =>
    cases hd : s.done
    · cases hi : s.inflight with
      | none => exact ⟨s.pending.map Event.input, by simp [apply, ask, hd, hi]⟩
      | some c => exact ⟨[], by simp [apply, ask, hd, hi]⟩
    · exact ⟨[], by simp [apply, ask, hd]⟩
  | commit =>
    cases hi : s.inflight with
    | none => exact ⟨[], by simp [apply, commit, hi]⟩
    | some calls =>
      exact ⟨Event.reply calls :: calls.map (fun c => Event.result c (tool c)),
        by simp [apply, commit, hi]⟩

theorem holds_apply (policy : Policy) (model : List (Event Input Call Result) → List Call)
    (tool : Call → Result) (op : Op Input) (s : State Input Call Result) (xs : List Input)
    (h : Holds s xs) :
    Holds (apply policy model tool op s)
      (xs ++ match op with
        | Op.arrive x => if s.done then [] else [x]
        | _ => []) := by
  obtain ⟨hmem, hdone⟩ := h
  cases op with
  | arrive x =>
    cases hd : s.done
    · simp only [apply, arrive, hd, if_false, Bool.false_eq_true]
      refine ⟨?_, by simp⟩
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · rcases hmem y hy with h | h
        · exact Or.inl (List.mem_append_left _ h)
        · exact Or.inr h
      · simp at hy; subst hy; exact Or.inl (by simp)
    · simp only [apply, arrive, hd, if_true, List.append_nil]
      exact ⟨hmem, hdone⟩
  | ask =>
    simp only [apply, List.append_nil]
    cases hd : s.done
    · cases hi : s.inflight with
      | none =>
        simp only [ask, hd, hi, if_false, Bool.false_eq_true]
        refine ⟨?_, by simp⟩
        intro y hy
        right
        rcases hmem y hy with h | h
        · exact List.mem_append_right _ (List.mem_map.mpr ⟨y, h, rfl⟩)
        · exact List.mem_append_left _ h
      | some c =>
        simp only [ask, hd, hi, if_false, Bool.false_eq_true]
        exact ⟨hmem, hdone⟩
    · simp only [ask, hd, if_true]
      exact ⟨hmem, hdone⟩
  | commit =>
    simp only [apply, List.append_nil]
    cases hi : s.inflight with
    | none =>
      simp only [commit, hi]
      exact ⟨hmem, hdone⟩
    | some calls =>
      simp only [commit, hi]
      refine ⟨?_, ?_⟩
      · intro y hy
        rcases hmem y hy with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_append_left _ h)
      · intro hd
        simp only [Bool.and_eq_true, List.isEmpty_iff] at hd
        exact hd.2

theorem holds_run (policy : Policy) (model : List (Event Input Call Result) → List Call)
    (tool : Call → Result) :
    ∀ (ops : List (Op Input)) (s : State Input Call Result) (xs : List Input),
      Holds s xs → Holds (run policy model tool ops s) (xs ++ arrived policy model tool ops s)
  | [], s, xs, h => by simpa [run, arrived] using h
  | op :: ops, s, xs, h => by
    have h1 := holds_apply policy model tool op s xs h
    have h2 := holds_run policy model tool ops _ _ h1
    simpa [run, arrived, List.foldl, List.append_assoc] using h2

/-- **No input is lost.** Under either policy, if the turn has ended, every
input that arrived before it ended is in the final conversation. -/
theorem arrived_mem_log_of_done (policy : Policy)
    (model : List (Event Input Call Result) → List Call) (tool : Call → Result)
    (ops : List (Op Input)) (log : List (Event Input Call Result))
    (hdone : (run policy model tool ops (start log)).done = true) :
    ∀ x ∈ arrived policy model tool ops (start log),
      Event.input x ∈ (run policy model tool ops (start log)).log := by
  have hstart : Holds (start log : State Input Call Result) [] := by
    refine ⟨by simp, ?_⟩
    intro h; simp [start] at h
  obtain ⟨hmem, hpend⟩ := holds_run policy model tool ops (start log) [] hstart
  intro x hx
  rcases hmem x (by simpa using hx) with h | h
  · rw [hpend hdone] at h; simp at h
  · exact h

/-! ## The two policies -/

/-- Under `preempt`, an input arriving during a requested reply discards that
reply: a following commit runs none of its tools and records nothing. -/
theorem preempt_discards_inflight (tool : Call → Result) (x : Input)
    (s : State Input Call Result) (hnotdone : s.done = false) :
    (arrive Policy.preempt x s).inflight = none ∧
      commit tool (arrive Policy.preempt x s) = arrive Policy.preempt x s := by
  simp [arrive, hnotdone, commit]

/-- Under `boundary`, an arriving input never discards the requested reply. -/
theorem boundary_keeps_inflight (x : Input) (s : State Input Call Result) :
    (arrive Policy.boundary x s).inflight = s.inflight := by
  unfold arrive; split <;> simp

end Mettapedia.CogArch.Agent.CodingAgent.TurnLoop
