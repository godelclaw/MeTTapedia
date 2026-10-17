import Mathlib.Logic.Function.Iterate

/-!
# Checkpoints for a specified deterministic strategy

Replay keeps its computed internal state and compares only a declared finite
view. The exact endpoint, successful tick count, refusal work, concatenation
and trace-materialization laws are independent of a particular programming
language, proof calculus or encoding of partial recursive functions.
-/

namespace Mettapedia.Machines.ExecutionHints


universe u v

/-- A visible checkpoint after the stated number of steps of the strategy
fixed by the request. It carries no replacement for private machine state. -/
structure Checkpoint (View : Type v) where
  steps : Nat
  expected : View
  deriving DecidableEq, Repr

variable {State : Type u} {View : Type v} [DecidableEq View]

def fuel : List (Checkpoint View) → Nat
  | [] => 0
  | point :: rest => point.steps + fuel rest

/-- Replay gaps from the actual computed residual, comparing only the named
view. Even a noninjective view cannot replace private theory or owner state.
The first component counts calls of `tick`, including the refused gap.
Equality, copying and reading hints have separate costs. -/
def replay (tick : State → State) (view : State → View) (source : State) :
    List (Checkpoint View) → Nat × Option State
  | [] => (0, some source)
  | point :: rest =>
      let next := tick^[point.steps] source
      if view next = point.expected then
        let later := replay tick view next rest
        (point.steps + later.1, later.2)
      else (point.steps, none)

omit [DecidableEq View] in
 theorem fuel_append (first second : List (Checkpoint View)) :
    fuel (first ++ second) = fuel first + fuel second := by
  induction first with
  | nil => simp [fuel]
  | cons point rest ih => simp [fuel, ih, Nat.add_assoc]

/-- A successful prefix is retained exactly when the remaining recipe is
checked. The accounting includes work performed before a later refusal. -/
theorem replay_append (tick : State → State) (view : State → View)
    (source : State) (first second : List (Checkpoint View)) :
    replay tick view source (first ++ second) =
      let checkedPrefix := replay tick view source first
      match checkedPrefix.2 with
      | none => (checkedPrefix.1, none)
      | some middle =>
          let suffix := replay tick view middle second
          (checkedPrefix.1 + suffix.1, suffix.2) := by
  induction first generalizing source with
  | nil => simp [replay]
  | cons point rest ih =>
      by_cases same : view (tick^[point.steps] source) = point.expected
      · simp only [List.cons_append, replay, if_pos same, ih]
        cases (replay tick view (tick^[point.steps] source) rest).2 <;>
          simp [Nat.add_assoc]
      · simp [replay, same]

theorem replay_calls_le (tick : State → State) (view : State → View)
    (points : List (Checkpoint View)) (source : State) :
    (replay tick view source points).1 ≤ fuel points := by
  induction points generalizing source with
  | nil => exact Nat.le_refl _
  | cons point rest ih =>
      by_cases same : view (tick^[point.steps] source) = point.expected
      · simpa [replay, same, fuel] using
          Nat.add_le_add_left (ih (tick^[point.steps] source)) point.steps
      · simp [replay, same, fuel]

/-- Successful replay has the exact internal endpoint, not merely an equal
visible observation, and makes exactly the supplied total number of tick calls. -/
theorem replay_result (tick : State → State) (view : State → View)
    (points : List (Checkpoint View)) (source target : State)
    (accepted : (replay tick view source points).2 = some target) :
    target = tick^[fuel points] source ∧
      (replay tick view source points).1 = fuel points := by
  induction points generalizing source target with
  | nil =>
      simp only [replay, Option.some.injEq] at accepted
      subst target
      exact ⟨rfl, rfl⟩
  | cons point rest ih =>
      by_cases same : view (tick^[point.steps] source) = point.expected
      · have later : (replay tick view (tick^[point.steps] source) rest).2 = some target := by
          simpa only [replay, if_pos same] using accepted
        obtain ⟨endpoint, calls⟩ := ih (tick^[point.steps] source) target later
        constructor
        · rw [endpoint, fuel, Nat.add_comm point.steps, Function.iterate_add_apply]
        · simp [replay, same, fuel, calls]
      · simp [replay, same] at accepted

/-- Materialize the requested visible residuals. Replay recomputes them from
its own state; correctness does not rely on trusting this producer. -/
def record (tick : State → State) (view : State → View) (source : State) :
    List Nat → List (Checkpoint View)
  | [] => []
  | steps :: rest =>
      let next := tick^[steps] source
      ⟨steps, view next⟩ :: record tick view next rest

omit [DecidableEq View] in
 theorem record_length (tick : State → State) (view : State → View)
    (gaps : List Nat) (source : State) :
    (record tick view source gaps).length = gaps.length := by
  induction gaps generalizing source with
  | nil => rfl
  | cons steps rest ih => simpa [record] using ih (tick^[steps] source)

omit [DecidableEq View] in
 theorem record_fuel (tick : State → State) (view : State → View)
    (gaps : List Nat) (source : State) :
    fuel (record tick view source gaps) = gaps.sum := by
  induction gaps generalizing source with
  | nil => rfl
  | cons steps rest ih => simp [record, fuel, ih]

theorem replay_record (tick : State → State) (view : State → View)
    (gaps : List Nat) (source : State) :
    replay tick view source (record tick view source gaps) =
      (gaps.sum, some (tick^[gaps.sum] source)) := by
  induction gaps generalizing source with
  | nil => rfl
  | cons steps rest ih =>
      simp only [record, replay]
      simp only [ite_true]
      rw [ih]
      simp only [List.sum_cons, Prod.mk.injEq, true_and, Option.some.injEq]
      rw [← Function.iterate_add_apply, Nat.add_comm rest.sum steps]

def check (tick : State → State) (view : State → View) (claim : State × View)
    (points : List (Checkpoint View)) : Bool :=
  decide (((replay tick view claim.1 points).2.map view) = some claim.2)

theorem check_sound (tick : State → State) (view : State → View)
    (claim : State × View) (points : List (Checkpoint View))
    (accepted : check tick view claim points = true) :
    view (tick^[fuel points] claim.1) = claim.2 := by
  have observed := of_decide_eq_true accepted
  obtain ⟨target, replayed, observed⟩ := Option.map_eq_some_iff.mp observed
  rw [(replay_result tick view points claim.1 target replayed).1] at observed
  exact observed

theorem check_record (tick : State → State) (view : State → View)
    (claim : State × View) (gaps : List Nat) :
    check tick view claim (record tick view claim.1 gaps) =
      decide (view (tick^[gaps.sum] claim.1) = claim.2) := by
  simp [check, replay_record]

/-- Completeness is for the fixed strategy at the supplied total budget and
view; it does not decide unrelated model truth or arbitrary normalization. -/
theorem exists_check_iff (tick : State → State) (view : State → View)
    (source : State) (target : View) (budget : Nat) :
    (∃ points, fuel points = budget ∧ check tick view (source, target) points = true) ↔
      view (tick^[budget] source) = target := by
  constructor
  · rintro ⟨points, total, accepted⟩
    simpa only [total] using check_sound tick view (source, target) points accepted
  · intro reached
    refine ⟨record tick view source [budget], ?_, ?_⟩
    · simp [record_fuel]
    · change check tick view (source, target) (record tick view (source, target).1 [budget]) = true
      rw [check_record]
      simp [reached]

/-- One visible checkpoint per strategy tick is the expanded trace. -/
def fullTrace (tick : State → State) (view : State → View) (source : State) (budget : Nat) :
    List (Checkpoint View) := record tick view source (List.replicate budget 1)

omit [DecidableEq View] in
 theorem fullTrace_length (tick : State → State) (view : State → View)
    (source : State) (budget : Nat) :
    (fullTrace tick view source budget).length = budget := by
  simp [fullTrace, record_length]

omit [DecidableEq View] in
 theorem fullTrace_fuel (tick : State → State) (view : State → View)
    (source : State) (budget : Nat) :
    fuel (fullTrace tick view source budget) = budget := by
  simp [fullTrace, record_fuel]

omit [DecidableEq View] in
 theorem fullTrace_unit (tick : State → State) (view : State → View)
    (source : State) (budget : Nat) :
    ∀ point ∈ fullTrace tick view source budget, point.steps = 1 := by
  induction budget generalizing source with
  | zero => simp [fullTrace, record]
  | succ budget ih =>
      simp only [fullTrace, List.replicate_succ, record, Function.iterate_one, List.mem_cons]
      intro point member
      rcases member with rfl | member
      · rfl
      · exact ih (tick source) point member

theorem check_fullTrace (tick : State → State) (view : State → View)
    (claim : State × View) (budget : Nat) :
    check tick view claim (fullTrace tick view claim.1 budget) =
      decide (view (tick^[budget] claim.1) = claim.2) := by
  simp [fullTrace, check_record]

namespace Controls

theorem wrong_checkpoint_refused :
    check Nat.succ id (0, 2) [⟨1, 99⟩, ⟨1, 2⟩] = false := by decide

theorem correct_coarse_checkpoint : check Nat.succ id (0, 2) [⟨2, 2⟩] = true := by decide

theorem split_checkpoint_calls : replay Nat.succ id 0 [⟨2, 2⟩, ⟨3, 5⟩] = (5, some 5) := by decide

theorem refused_checkpoint_calls : replay Nat.succ id 0 [⟨2, 99⟩, ⟨3, 5⟩] = (2, none) := by decide

/-- The certificate sees only the counter; its replay cannot replace the
private flag, even though that flag is absent from every checkpoint. -/
theorem hidden_state_preserved :
    replay (fun state : Nat × Bool => (state.1 + 1, state.2)) Prod.fst (0, true)
      [⟨2, 2⟩] = (2, some (2, true)) := by decide

end Controls

end Mettapedia.Machines.ExecutionHints
