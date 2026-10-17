import Mettapedia.GSLT.Distinction.OrderedAdministrationControls
import Mettapedia.GSLT.Distinction.FrontierObservation
import Mettapedia.GSLT.Contracts.AuthorityControls

/-!
# Joins of the contract layer with ordered administration

Three joins with the ordered-machine theory of `Mettapedia.GSLT.Distinction`.

## Progress is a separate obligation over the same machines

A block simulation (`BlockSimulation`) is a safety contract.  It admits an
implementation that stutters forever: `stutterImpl` stands for an answer while
its administrative state loops, a block simulation relates it to a
specification that answers in one step (`stutter_block`), and it has an
infinite run whose states after the first are never stable
(`stutter_never_stable`).  No rank exists for it (`stutter_not_ranked`).

The rank of `OrderedSystem.AdministrationRanked` is exactly the missing
progress certificate: under it, on every infinite run a stable state recurs
within `rank` steps of any point (`ranked_stable_within_rank`).  So progress
needs no new structure on the machines; it is a property of their infinite
runs, certified separately from the simulation.

## Selecting a successful outcome

`firstAnswer` selects the first halted state.  With a separate success
observer whose successes are halted, pruning every occurrence after the first
success keeps the first success at every fuel (`firstSuccess_prune`).  On the
existing controls, pruning after the first success keeps the value
(`prune_after_success_keeps_value`), while pruning after the first terminal,
which is a fault, loses it (`prune_after_fault_loses_value`).

## Authority is a committed readout of settlement

Authority held by a machine state is a readout that administrative steps must
preserve (`OrderedSystem.AdministrationPreserves`) and that erased dead ends
must account for (`OrderedSystem.ErasurePreserves`).  The frame-preserving
update order alone permits discarding any authority (`FrameUpdate.to_zero`):
authority is affine.  An administrative dead end that holds the consume right
can therefore be dropped by settling without breaking any frame
(`erased_owner_discard_is_update`), and only the erasure licence rejects it
(`erased_owner_not_licensed`).  Obligations that must be discharged, such as
owned continuations or durable intents, need that additional law.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.Joins

open Mettapedia.GSLT.Distinction
open Mettapedia.GSLT.Distinction.OrderedSystem

universe u v

/-! ## Progress -/

section Progress

variable {T : Type u} {system : OrderedSystem T}

/-- An infinite run of an ordered system. -/
def InfiniteRun (system : OrderedSystem T) (run : ℕ → T) : Prop :=
  ∀ n, run (n + 1) ∈ system.step (run n)

/-- **Ranked administration gives progress through administration**: on every
infinite run a stable state occurs within `rank` steps of any point. -/
theorem ranked_stable_within_rank {stable : T → Bool} {rank : T → ℕ}
    (ranked : system.AdministrationRanked stable rank) {run : ℕ → T}
    (infinite : InfiniteRun system run) (n : ℕ) :
    ∃ m, n ≤ m ∧ m ≤ n + rank (run n) ∧ stable (run m) = true := by
  induction h : rank (run n) using Nat.strong_induction_on generalizing n with
  | _ bound ih =>
    cases isStable : stable (run n)
    · have decrease := ranked (run n) isStable (run (n + 1)) (infinite n)
      rw [h] at decrease
      obtain ⟨m, later, within, stableM⟩ := ih _ decrease (n + 1) rfl
      exact ⟨m, by omega, by omega, stableM⟩
    · exact ⟨n, le_rfl, by omega, isStable⟩

/-- Stable states recur infinitely often on every infinite run. -/
theorem ranked_stable_recurs {stable : T → Bool} {rank : T → ℕ}
    (ranked : system.AdministrationRanked stable rank) {run : ℕ → T}
    (infinite : InfiniteRun system run) (n : ℕ) : ∃ m, n ≤ m ∧ stable (run m) = true :=
  let ⟨m, later, _, stableM⟩ := ranked_stable_within_rank ranked infinite n
  ⟨m, later, stableM⟩

end Progress

/-! ## A safety simulation that never serves -/

/-- Specification states: a root that answers in one step. -/
inductive AnswerState where
  | root
  | answer
  deriving DecidableEq, Repr

def answerSpec : OrderedSystem AnswerState where
  step
    | .root => [.answer]
    | .answer => []
  halted
    | .root => false
    | .answer => true

/-- Implementation states: the root enters an administrative loop. -/
inductive StutterState where
  | root
  | spinning
  | answer
  deriving DecidableEq, Repr

def stutterImpl : OrderedSystem StutterState where
  step
    | .root => [.spinning]
    | .spinning => [.spinning]
    | .answer => []
  halted
    | .answer => true
    | _ => false

def stutterStable : StutterState → Bool
  | .spinning => false
  | _ => true

/-- The looping state claims to stand for the answer. -/
def stutterBlock : List AnswerState → StutterState → Prop
  | occurrences, .root => occurrences = [.root]
  | occurrences, .spinning => occurrences = [.answer]
  | occurrences, .answer => occurrences = [.answer]

/-- **The safety contract holds.** -/
theorem stutter_block : BlockSimulation answerSpec stutterImpl stutterStable stutterBlock where
  stable_single := by
    intro occurrences target blocked isStable
    cases target with
    | root => exact ⟨.root, blocked, rfl⟩
    | spinning => cases isStable
    | answer => exact ⟨.answer, blocked, rfl⟩
  stable_step := by
    intro state target blocked isStable
    cases target with
    | root =>
      obtain rfl : state = .root := List.singleton_inj.mp blocked
      exact ⟨[[.answer]], .cons rfl .nil, rfl⟩
    | spinning => cases isStable
    | answer =>
      obtain rfl : state = .answer := List.singleton_inj.mp blocked
      exact ⟨[], .nil, rfl⟩
  administrative_split := by
    intro occurrences target blocked administrative
    cases target with
    | root => cases administrative
    | spinning => exact ⟨[[.answer]], .cons rfl .nil, blocked.symm⟩
    | answer => cases administrative

/-- The run that enters the loop and stays there. -/
def stutterRun : ℕ → StutterState
  | 0 => .root
  | _ + 1 => .spinning

theorem stutterRun_infinite : InfiniteRun stutterImpl stutterRun := by
  intro n
  cases n <;> simp [stutterRun, stutterImpl]

/-- **Progress fails**: after the first step no state of the run is stable, so
the answer is never served. -/
theorem stutter_never_stable (m : ℕ) (later : 1 ≤ m) : stutterStable (stutterRun m) = false := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rfl

/-- No rank certifies this administration. -/
theorem stutter_not_ranked (rank : StutterState → ℕ) :
    ¬ stutterImpl.AdministrationRanked stutterStable rank :=
  not_ranked_of_loop (system := stutterImpl) (state := .spinning) rfl (by simp [stutterImpl]) rank

/-! ## Selecting a successful outcome -/

section Success

variable {State : Type u} {system : OrderedSystem State}

/-- The first successful state in occurrence order. -/
def firstSuccess (success : State → Bool) (states : List State) : Option State :=
  states.find? success

/-- **Pruning after the first success keeps it**, at every fuel, when
successful states are halted and halted states are inert. -/
theorem firstSuccess_prune (inert : system.HaltedInert) {success : State → Bool}
    (successHalts : ∀ state, success state = true → system.halted state = true)
    (fuel : ℕ) (before after : List State) {answer : State} (succeeds : success answer = true) :
    firstSuccess success (system.runFrontier fuel (before ++ answer :: after)) =
      firstSuccess success (system.runFrontier fuel (before ++ [answer])) := by
  have split : before ++ answer :: after = (before ++ [answer]) ++ after := by simp
  have present : answer ∈ system.runFrontier fuel (before ++ [answer]) := by
    rw [system.runFrontier_append inert, runFrontier_single_halted fuel (successHalts _ succeeds)]
    simp
  rw [split, system.runFrontier_append inert]
  simp only [firstSuccess, List.find?_append]
  cases found : (system.runFrontier fuel (before ++ [answer])).find? success with
  | none => exact absurd succeeds (by simpa using List.find?_eq_none.mp found answer present)
  | some _ => rfl

end Success

open FrontierObservationControls in
/-- **Pruning after the first success keeps the value**: dropping what follows
the first successful occurrence never changes the selected value. -/
theorem prune_after_success_keeps_value (fuel : ℕ) :
    firstSuccess successful (FrontierObservationControls.system.runFrontier fuel [.fault, .seven, .towardEight]) =
      firstSuccess successful (FrontierObservationControls.system.runFrontier fuel [.fault, .seven]) :=
  firstSuccess_prune inert (fun state succeeds => by cases state <;> simp_all [successful, FrontierObservationControls.system])
    fuel [.fault] [.towardEight] (answer := .seven) rfl

open FrontierObservationControls in
/-- **Pruning after the first terminal loses the value**: the first terminal is
a fault, and keeping only it leaves no success. -/
theorem prune_after_fault_loses_value :
    FrontierObservationControls.system.firstAnswer [.fault, .seven, .towardEight] = some .fault ∧
      firstSuccess successful [.fault, .seven, .towardEight] = some .seven ∧
      firstSuccess successful [.fault] = none := by
  decide


/-! ## Authority as a committed readout -/

/-- A root that steps into an administrative dead end holding the consume
right. -/
inductive OwnerState where
  | root
  | owner
  deriving DecidableEq, Repr

def ownerSystem : OrderedSystem OwnerState where
  step
    | .root => [.owner]
    | .owner => []
  halted _ := false

def ownerStable : OwnerState → Bool
  | .root => true
  | .owner => false

/-- The authority each state holds. -/
def held : OwnerState → Access
  | .root => .none
  | .owner => .consume

/-- Settling drops the owner. -/
theorem owner_erased : ownerSystem.settle ownerStable 1 .owner = [] := rfl

/-- **The frame order permits the discard.** -/
theorem erased_owner_discard_is_update : FrameUpdate (held .owner) 0 :=
  FrameUpdate.to_zero _

/-- **The erasure licence rejects it**: nothing retains the consume right. -/
theorem erased_owner_not_licensed :
    ¬ ownerSystem.ErasurePreserves ownerStable held (fun _ => (0 : Access)) := by
  intro licensed
  have kept := licensed .owner rfl rfl
  cases kept

/-- A dead end holding nothing may be erased. -/
theorem empty_dead_end_licensed :
    ownerSystem.ErasurePreserves ownerStable (fun _ => (0 : Access)) (fun _ => (0 : Access)) :=
  fun _ _ _ => rfl

/-! ## Separate commitment observers share the existing erasure boundary -/

/-- The first observer sees no retained permission; the second sees one
outstanding duty at the administrative owner. -/
def dutyObservers (state : OwnerState) (duty : Bool) : Nat :=
  match state, duty with
  | .owner, true => 1
  | _, _ => 0

/-- Selecting only the empty component would permit erasure. The complete
observer family refuses it unless the outstanding duty is retained outside
the rejected leaf. This is an erasure control, not a compensating service. -/
theorem duty_family_requires_retention :
    ownerSystem.ErasurePreserves ownerStable
      (fun state => dutyObservers state false) (fun _ => 0) ∧
    ¬ ownerSystem.ErasurePreserves ownerStable dutyObservers (fun _ _ => 0) ∧
    ownerSystem.ErasurePreserves ownerStable dutyObservers
      (fun _ duty => if duty then 1 else 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro state _ _
    cases state <;> rfl
  · intro licensed
    have missing := congrFun (licensed .owner rfl rfl) true
    cases missing
  · intro state administrative _
    cases state with
    | root => cases administrative
    | owner => funext duty; cases duty <;> rfl

/-! ## Axiom audit -/

#print axioms ranked_stable_within_rank
#print axioms stutter_block
#print axioms stutter_never_stable
#print axioms stutter_not_ranked
#print axioms firstSuccess_prune
#print axioms prune_after_success_keeps_value
#print axioms prune_after_fault_loses_value
#print axioms erased_owner_not_licensed
#print axioms OrderedSystem.administrationPreserves_family_iff
#print axioms OrderedSystem.erasurePreserves_family_iff
#print axioms duty_family_requires_retention

end Mettapedia.GSLT.Contracts.Joins
