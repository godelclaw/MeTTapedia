import Mettapedia.Cybernetics.HierarchicalComplexity.Basic

/-!
# Binary composition, commutation, and hierarchical order

Binary schedules form a chain exactly when their composites agree at the
initial state. Separated updates commute; interaction alone does not entail
order sensitivity. The rank laws require the declared child homogeneity.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.HierarchicalComplexity.Composition

open Mettapedia.Cybernetics.HierarchicalComplexity

universe u v w x y

variable {Left : Type v} {Right : Type w} {Outcome : Type x}

/-- Two named transformations and the state from which their schedules are
compared. -/
structure BinaryProcess (State : Type u) where
  initial : State
  left : State → State
  right : State → State

namespace BinaryProcess

variable {State : Type u} (process : BinaryProcess State)

def leftThenRight : State :=
  process.right (process.left process.initial)

def rightThenLeft : State :=
  process.left (process.right process.initial)

/-- The two schedules are distinguished by which named transformation occurs
first. -/
def scheduleSemantics : ScheduleSemantics (Fin 2) State :=
  fun schedule =>
    if schedule 0 = 0 then process.leftThenRight
    else process.rightThenLeft

@[simp] theorem scheduleSemantics_refl : process.scheduleSemantics (Equiv.refl (Fin 2)) =
      process.leftThenRight := by
  simp [scheduleSemantics]

@[simp] theorem scheduleSemantics_swap : process.scheduleSemantics (Equiv.swap (0 : Fin 2) 1) =
      process.rightThenLeft := by
  simp [scheduleSemantics]

/-- Binary schedule invariance is exactly local commutation at the declared
initial state. -/
theorem isChain_iff : IsChain process.scheduleSemantics ↔
      process.leftThenRight = process.rightThenLeft := by
  constructor
  · intro chain
    simpa using chain (Equiv.refl (Fin 2)) (Equiv.swap 0 1)
  · intro commute first second
    simp only [scheduleSemantics, ← commute, ite_self]

/-- Binary order sensitivity is exactly failure of local commutation. -/
theorem isCoordination_iff : IsCoordination process.scheduleSemantics ↔
      process.leftThenRight ≠ process.rightThenLeft := by
  rw [isCoordination_iff_not_isChain, isChain_iff]

/-- A globally commuting pair is a chain from every initial state. -/
theorem isChain_of_commute (initial : State) {left right : State → State}
    (commute : Function.Commute left right) :
    IsChain (BinaryProcess.scheduleSemantics
      ⟨initial, left, right⟩) := (isChain_iff _).mpr (commute initial).symm

/-! ## Certified separation -/

/-- Component-local transformations on a product state. -/
def separated (initial : Left × Right) (updateLeft : Left → Left)
    (updateRight : Right → Right) : BinaryProcess (Left × Right) where
  initial := initial
  left state := (updateLeft state.1, state.2)
  right state := (state.1, updateRight state.2)

/-- Separated transformations commute as functions, independently of their
particular component behavior. -/
theorem separated_commute (updateLeft : Left → Left) (updateRight : Right → Right) :
    Function.Commute
      (fun state : Left × Right => (updateLeft state.1, state.2))
      (fun state : Left × Right => (state.1, updateRight state.2)) := by
  intro state
  rfl

/-- Certified component separation therefore gives a chain. -/
theorem separated_isChain (initial : Left × Right) (updateLeft : Left → Left)
    (updateRight : Right → Right) :
    IsChain (separated initial updateLeft updateRight).scheduleSemantics :=
  isChain_of_commute initial (separated_commute updateLeft updateRight)

/-! ## The induced hierarchical action -/

/-- Two child actions with a schedule-invariant process form a chain action. -/
def chainAction (process : BinaryProcess Outcome) (invariant : IsChain process.scheduleSemantics)
    (child : Fin 2 → Action.{0, x} Outcome) :
    Action.{0, x} Outcome :=
  .compound (Fin 2) LimitCanary.binary_hasAtLeastTwo child
    (.chain process.scheduleSemantics invariant)

/-- Two child actions with an order-sensitive process form a coordination
action. -/
def coordinationAction (process : BinaryProcess Outcome)
    (sensitive : IsCoordination process.scheduleSemantics)
    (child : Fin 2 → Action.{0, x} Outcome) :
    Action.{0, x} Outcome :=
  .compound (Fin 2) LimitCanary.binary_hasAtLeastTwo child
    (.coordination process.scheduleSemantics sensitive)

/-- A homogeneous chain preserves the common hierarchical rank. -/
theorem rank_chainAction_of_equalRank (process : BinaryProcess Outcome)
    (invariant : IsChain process.scheduleSemantics)
    (child : Fin 2 → Action.{0, x} Outcome)
    (equalRank : ∀ occurrence,
      Action.rank (child occurrence) = Action.rank (child 0)) :
    Action.rank (chainAction process invariant child) =
      Action.rank (child 0) := by
  rw [chainAction, Action.rank_chain]
  exact Action.childSup_eq_of_equalRank child (0 : Fin 2) equalRank

/-- A homogeneous coordination raises the common hierarchical rank by one. -/
theorem rank_coordinationAction_of_equalRank (process : BinaryProcess Outcome)
    (sensitive : IsCoordination process.scheduleSemantics)
    (child : Fin 2 → Action.{0, x} Outcome)
    (equalRank : ∀ occurrence,
      Action.rank (child occurrence) = Action.rank (child 0)) :
    Action.rank (coordinationAction process sensitive child) =
      Order.succ (Action.rank (child 0)) := by
  rw [coordinationAction, Action.rank_coordination]
  congr 1
  exact Action.childSup_eq_of_equalRank child (0 : Fin 2) equalRank

end BinaryProcess

/-! ## An interacting, noncommuting control -/

namespace InteractionCanary

/-- Increment and doubling share one state and do not commute from `1`. -/
def process : BinaryProcess Nat where
  initial := 1
  left number := number + 1
  right number := 2 * number

@[simp] theorem leftThenRight : process.leftThenRight = 4 := rfl

@[simp] theorem rightThenLeft : process.rightThenLeft = 3 := rfl

theorem process_isCoordination :
    IsCoordination process.scheduleSemantics := (BinaryProcess.isCoordination_iff _).mpr (by decide)

/-- The same two simple children remain at order zero under separated
composition. -/
def separatedAction : Action.{0, 0} (Nat × Nat) :=
  BinaryProcess.chainAction
    (BinaryProcess.separated (1, 1) (fun n => n + 1) (fun n => 2 * n))
    (BinaryProcess.separated_isChain
      (1, 1) (fun n => n + 1) (fun n => 2 * n))
    (fun _ => .simple)

theorem rank_separatedAction : Action.rank separatedAction = 0 :=
  BinaryProcess.rank_chainAction_of_equalRank _ _ _ (fun _ => rfl)

/-- Sharing state makes the noncommuting version a genuine order-one
coordination. -/
def interactingAction : Action.{0, 0} Nat :=
  BinaryProcess.coordinationAction process process_isCoordination
    (fun _ => .simple)

theorem rank_interactingAction : Action.rank interactingAction = 1 := by
  have rankSuccessor := BinaryProcess.rank_coordinationAction_of_equalRank
    process process_isCoordination (fun _ => .simple) (fun _ => rfl)
  simpa only [interactingAction, Action.rank_simple,
    Order.succ_eq_add_one, zero_add] using rankSuccessor

end InteractionCanary

end Mettapedia.Cybernetics.HierarchicalComplexity.Composition
