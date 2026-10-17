import Mettapedia.GSLT.LanguageDef.RegexRelationEnumeration

/-!
# Retained occurrence frontiers

The cursor stores deferred search work, not a precomputed answer list. A
transition either preserves its exact ordered residual or returns its first
occurrence with the remaining suffix. Work interruption preserves the same
residual observation. Finite exhaustion is earned from a decreasing frontier
weight rather than asserted by an arbitrary caller budget.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexRelationCursor

open RegexRelationEnumeration
open RegexObservationTrace (ObservedAction)

universe u v

structure Work (State : Type u) (Key : Type v) where
  state : State
  seen : List Key
  depth : Nat
  choices : List Bool
  points : List Key

def decorate {State : Type u} {Key : Type v} (choices : List Bool) (points : List Key)
    (occurrence : Occurrence State Key) : Occurrence State Key :=
  ⟨occurrence.value, choices ++ occurrence.choices, points ++ occurrence.points⟩

theorem decorate_prepend {State : Type u} {Key : Type v} (choices bits : List Bool)
    (points : List Key) (point : Key) (occurrence : Occurrence State Key) :
    decorate choices points (prepend bits point occurrence) =
      decorate (choices ++ bits) (points ++ [point]) occurrence := by
  cases occurrence
  simp [decorate, prepend, List.append_assoc]

def child {State : Type u} {Key : Type v} (key : State → Key)
    (work : Work State Key) (depth : Nat) (target : State) (bits : List Bool) : Work State Key :=
  ⟨target, key work.state :: work.seen, depth, work.choices ++ bits, work.points ++ [key work.state]⟩

def denoteWork {State : Type u} {Key : Type v} [DecidableEq Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (work : Work State Key) : List (Occurrence State Key) :=
  (enumerate step key eligible work.depth work.seen work.state).map (decorate work.choices work.points)

def denote {State : Type u} {Key : Type v} [DecidableEq Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (pending : List (Work State Key)) : List (Occurrence State Key) :=
  pending.flatMap (denoteWork step key eligible)

inductive Result (State : Type u) (Key : Type v) where
  | closed
  | pending (frontier : List (Work State Key))
  | yielded (occurrence : Occurrence State Key) (frontier : List (Work State Key))

def advance {State : Type u} {Key : Type v} [DecidableEq Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool) :
    List (Work State Key) → Result State Key
  | [] => .closed
  | work :: rest =>
      match work.depth with
      | 0 => .pending rest
      | depth + 1 =>
          if key work.state ∈ work.seen then .pending rest else
            match step work.state with
            | .dead => .pending rest
            | .accept =>
                if eligible work.state then
                  .yielded ⟨work.state, work.choices, work.points ++ [key work.state]⟩ rest
                else .pending rest
            | .next target bits => .pending (child key work depth target bits :: rest)
            | .branch left right =>
                .pending (child key work depth left [false] :: child key work depth right [true] :: rest)

def Equation {State : Type u} {Key : Type v} [DecidableEq Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (before : List (Work State Key)) : Result State Key → Prop
  | .closed => denote step key eligible before = []
  | .pending after => denote step key eligible before = denote step key eligible after
  | .yielded occurrence after => denote step key eligible before = occurrence :: denote step key eligible after

theorem child_denote {State : Type u} {Key : Type v} [DecidableEq Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (work : Work State Key) (depth : Nat) (target : State) (bits : List Bool) :
    denoteWork step key eligible (child key work depth target bits) =
      ((enumerate step key eligible depth (key work.state :: work.seen) target).map
        (prepend bits (key work.state))).map (decorate work.choices work.points) := by
  simp only [denoteWork, child, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro occurrence present
  exact (decorate_prepend work.choices bits work.points (key work.state) occurrence).symm

theorem advance_equation {State : Type u} {Key : Type v} [DecidableEq Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (pending : List (Work State Key)) : Equation step key eligible pending (advance step key eligible pending) := by
  cases pending with
  | nil => rfl
  | cons work rest =>
      cases depth : work.depth with
      | zero => simp [advance, depth, Equation, denote, denoteWork, enumerate]
      | succ depth =>
          by_cases visited : key work.state ∈ work.seen
          · simp [advance, depth, visited, Equation, denote, denoteWork, enumerate]
          · cases operation : step work.state with
            | dead => simp [advance, depth, visited, operation, Equation, denote, denoteWork, enumerate]
            | accept =>
                cases allowed : eligible work.state <;>
                  simp [advance, depth, visited, operation, allowed, Equation, denote, denoteWork, enumerate,
                    decorate]
            | next target bits =>
                simp only [advance, depth, visited, ↓reduceIte, operation, Equation,
                  denote, List.flatMap_cons]
                rw [child_denote]
                simp [denoteWork, enumerate, depth, visited, operation]
            | branch left right =>
                simp only [advance, depth, visited, ↓reduceIte, operation, Equation,
                  denote, List.flatMap_cons]
                rw [child_denote, child_denote]
                simp [denoteWork, enumerate, depth, visited, operation, List.map_append, List.append_assoc]

def drive {State : Type u} {Key : Type v} [DecidableEq Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool) :
    Nat → List (Work State Key) → Result State Key
  | 0, pending => .pending pending
  | budget + 1, pending =>
      match advance step key eligible pending with
      | .closed => .closed
      | .yielded occurrence following => .yielded occurrence following
      | .pending following => drive step key eligible budget following

theorem drive_equation {State : Type u} {Key : Type v} [DecidableEq Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (budget : Nat) (pending : List (Work State Key)) :
    Equation step key eligible pending (drive step key eligible budget pending) := by
  induction budget generalizing pending with
  | zero => rfl
  | succ budget ih =>
      have transition := advance_equation step key eligible pending
      unfold drive
      cases advanced : advance step key eligible pending with
      | closed => simpa [advanced] using transition
      | yielded occurrence following => simpa [advanced] using transition
      | pending following =>
          have preserved : denote step key eligible pending = denote step key eligible following := by
            simpa [advanced, Equation] using transition
          have further := ih following
          cases returned : drive step key eligible budget following <;>
            simp_all only [Equation]

def weight {State : Type u} {Key : Type v} (pending : List (Work State Key)) : Nat :=
  (pending.map fun work => 3 ^ work.depth).sum

theorem pending_decreases {State : Type u} {Key : Type v} [DecidableEq Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (before after : List (Work State Key))
    (advanced : advance step key eligible before = .pending after) : weight after < weight before := by
  cases before with
  | nil => cases advanced
  | cons work rest =>
      have positive : 0 < 3 ^ work.depth := Nat.pow_pos (by decide)
      cases depthEq : work.depth with
      | zero =>
          simp [advance, depthEq] at advanced
          subst after
          simp [weight, depthEq]
      | succ depth =>
          have smallerPositive : 0 < 3 ^ depth := Nat.pow_pos (by decide)
          by_cases visited : key work.state ∈ work.seen
          · simp [advance, depthEq, visited] at advanced
            subst after
            simp only [weight, List.map_cons, List.sum_cons]
            omega
          · cases operation : step work.state with
            | dead =>
                simp [advance, depthEq, visited, operation] at advanced
                subst after
                simp only [weight, List.map_cons, List.sum_cons]
                omega
            | accept =>
                cases allowed : eligible work.state <;>
                  simp [advance, depthEq, visited, operation, allowed] at advanced
                subst after
                simp only [weight, List.map_cons, List.sum_cons]
                omega
            | next target bits =>
                simp [advance, depthEq, visited, operation] at advanced
                subst after
                simp only [weight, List.map_cons, List.sum_cons, child, depthEq, Nat.pow_succ]
                omega
            | branch left right =>
                simp [advance, depthEq, visited, operation] at advanced
                subst after
                simp only [weight, List.map_cons, List.sum_cons, child, depthEq, Nat.pow_succ]
                omega

def pending? {State : Type u} {Key : Type v} : Result State Key → Bool
  | .pending _ => true
  | _ => false

theorem earned_budget_finishes_or_yields {State : Type u} {Key : Type v} [DecidableEq Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (budget : Nat) (pending : List (Work State Key)) (enough : weight pending < budget) :
    pending? (drive step key eligible budget pending) = false := by
  induction budget generalizing pending with
  | zero => omega
  | succ budget ih =>
      unfold drive
      cases advanced : advance step key eligible pending with
      | closed | yielded occurrence following => rfl
      | pending following =>
          have decreases := pending_decreases step key eligible pending following advanced
          exact ih following (by omega)

theorem exhausted_iff_empty_residual {State : Type u} {Key : Type v} [DecidableEq Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (pending : List (Work State Key)) :
    drive step key eligible (weight pending + 1) pending = .closed ↔ denote step key eligible pending = [] := by
  have exactResidual := drive_equation step key eligible (weight pending + 1) pending
  have complete := earned_budget_finishes_or_yields step key eligible (weight pending + 1) pending (by omega)
  cases returned : drive step key eligible (weight pending + 1) pending with
  | closed => simpa [returned, Equation] using exactResidual
  | pending following => simp [returned, pending?] at complete
  | yielded occurrence following =>
      have equation : denote step key eligible pending = occurrence :: denote step key eligible following := by
        simpa [returned, Equation] using exactResidual
      simp [equation]

def initial {State : Type u} {Key : Type v} [Fintype Key] (first : State) : List (Work State Key) :=
  [⟨first, [], Fintype.card Key, [], []⟩]

theorem initial_residual {State : Type u} {Key : Type v} [DecidableEq Key] [Fintype Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool) (first : State) :
    denote step key eligible (initial (Key := Key) first) = all step key eligible first := by
  have identity : (decorate [] [] : Occurrence State Key → Occurrence State Key) = id := by
    funext occurrence
    cases occurrence
    rfl
  simp [denote, denoteWork, initial, all, identity]

theorem exhausted_iff_no_simple_accepting_trace {State : Type u} {Key : Type v}
    [DecidableEq Key] [Fintype Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool) (first : State) :
    drive step key eligible (weight (initial (Key := Key) first) + 1) (initial (Key := Key) first) = .closed ↔
      ¬ ∃ bits points last, Trace step key eligible first bits points last ∧ points.Nodup := by
  rw [exhausted_iff_empty_residual, initial_residual]
  constructor
  · intro empty ⟨bits, points, last, trace, simple⟩
    have member := (all_exact step key eligible first (⟨last,bits,points⟩ : Occurrence State Key)).mpr ⟨trace,simple⟩
    rw [empty] at member
    cases member
  · intro absent
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro occurrence member
    obtain ⟨trace, simple⟩ := (all_exact step key eligible first occurrence).mp member
    exact absent ⟨occurrence.choices, occurrence.points, occurrence.value, trace, simple⟩

def initialMany {State : Type u} {Key : Type v} [Fintype Key]
    (starts : List State) : List (Work State Key) := starts.flatMap (initial (Key := Key))

theorem multiple_starts_retain_order_and_overlaps {State : Type u} {Key : Type v}
    [DecidableEq Key] [Fintype Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (starts : List State) :
    denote step key eligible (initialMany (Key := Key) starts) = starts.flatMap (all step key eligible) := by
  simp only [initialMany, denote, List.flatMap_assoc]
  apply congrArg (List.flatMap · starts)
  funext first
  exact initial_residual step key eligible first

inductive PauseReason where
  | budget | cancellation
  deriving DecidableEq, Repr

inductive Delivery (State : Type u) (Key : Type v) where
  | closed
  | paused (reason : PauseReason) (frontier : List (Work State Key))
  | yielded (occurrence : Occurrence State Key) (frontier : List (Work State Key))

def drivePolicy {State : Type u} {Key : Type v} [DecidableEq Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (cancelled : Nat → Bool) : Nat → List (Work State Key) → Delivery State Key
  | budget, pending =>
      if cancelled budget then .paused .cancellation pending else
        match budget with
        | 0 => .paused .budget pending
        | budget + 1 =>
            match advance step key eligible pending with
            | .closed => .closed
            | .yielded occurrence after => .yielded occurrence after
            | .pending after => drivePolicy step key eligible cancelled budget after

def DeliveryEquation {State : Type u} {Key : Type v} [DecidableEq Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (before : List (Work State Key)) : Delivery State Key → Prop
  | .closed => denote step key eligible before = []
  | .paused _ after => denote step key eligible before = denote step key eligible after
  | .yielded occurrence after => denote step key eligible before = occurrence :: denote step key eligible after

theorem policy_residual_exact {State : Type u} {Key : Type v} [DecidableEq Key]
    (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (cancelled : Nat → Bool) (budget : Nat) (pending : List (Work State Key)) :
    DeliveryEquation step key eligible pending (drivePolicy step key eligible cancelled budget pending) := by
  induction budget generalizing pending with
  | zero => cases stopped : cancelled 0 <;> simp [drivePolicy, stopped, DeliveryEquation]
  | succ budget ih =>
      have transition := advance_equation step key eligible pending
      unfold drivePolicy
      split
      · rfl
      · cases advanced : advance step key eligible pending with
        | closed => simpa [advanced, Equation, DeliveryEquation] using transition
        | yielded occurrence following => simpa [advanced, Equation, DeliveryEquation] using transition
        | pending following =>
            have preserved : denote step key eligible pending = denote step key eligible following := by
              simpa [advanced, Equation] using transition
            have further := ih following
            cases returned : drivePolicy step key eligible cancelled budget following <;>
              simp_all only [DeliveryEquation]

theorem pause_does_not_consume_an_unreturned_occurrence {State : Type u} {Key : Type v}
    [DecidableEq Key] (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (cancelled : Nat → Bool) (budget : Nat) (before after : List (Work State Key)) (reason : PauseReason)
    (paused : drivePolicy step key eligible cancelled budget before = .paused reason after) :
    denote step key eligible before = denote step key eligible after := by
  have exactResidual := policy_residual_exact step key eligible cancelled budget before
  simpa [paused, DeliveryEquation] using exactResidual

theorem published_prefix_extends_by_exactly_one_occurrence {State : Type u} {Key : Type v}
    [DecidableEq Key] (step : State → ObservedAction State) (key : State → Key) (eligible : State → Bool)
    (cancelled : Nat → Bool) (budget : Nat) (before after : List (Work State Key))
    (published : List (Occurrence State Key)) (occurrence : Occurrence State Key)
    (returned : drivePolicy step key eligible cancelled budget before = .yielded occurrence after) :
    published ++ denote step key eligible before = (published ++ [occurrence]) ++ denote step key eligible after := by
  have exactResidual := policy_residual_exact step key eligible cancelled budget before
  have partition : denote step key eligible before = occurrence :: denote step key eligible after := by
    simpa [returned, DeliveryEquation] using exactResidual
  simp [partition, List.append_assoc]

namespace Controls

private def branching (state : Fin 2) : ObservedAction (Fin 2) :=
  if state = 0 then .branch 1 1 else .accept

theorem budget_zero_retains_the_entire_frontier :
    ∀ pending : List (Work (Fin 2) (Fin 2)),
      drivePolicy branching id (fun _ => true) (fun _ => false) 0 pending = .paused .budget pending := by
  intro pending
  rfl

theorem cancellation_before_next_retains_its_occurrence :
    ∀ pending : List (Work (Fin 2) (Fin 2)),
      drivePolicy branching id (fun _ => true) (fun _ => true) 20 pending = .paused .cancellation pending := by
  intro pending
  rfl

theorem positive_overlapping_starts_are_not_nonoverlapping_iteration :
    (denote (fun _ : Fin 1 => .accept) id (fun _ => true)
      (initialMany (Key := Fin 1) [0,0])).map Occurrence.value = [0,0] := by decide

theorem resume_delivers_both_equal_answers_without_replay :
    (match drive branching id (fun _ => true) 20 (initial (Key := Fin 2) 0) with
    | .yielded first after =>
        match drive branching id (fun _ => true) 20 after with
        | .yielded second rest => ([first.value, second.value], (denote branching id (fun _ => true) rest).length)
        | _ => ([], 99)
    | _ => ([], 99)) = ([1,1],0) := by decide

theorem zero_budget_is_not_a_closed_empty_search :
    drive branching id (fun _ => true) 0 (initial (Key := Fin 2) 0) ≠ .closed := by
  intro impossible
  cases impossible

end Controls

end Mettapedia.GSLT.LanguageDef.RegexRelationCursor
