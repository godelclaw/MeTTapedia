import Mettapedia.GSLT.Distinction.OrderedSimulation

/-!
# What an observation of a frontier may forget

An observer reads a frontier; a retention operation changes it.  Reading less
hides information that the frontier still holds, while dropping occurrences
destroys it.  This module separates the two for ordered frontiers whose halted
states are inert.

* **Dropping a suffix commutes with execution** (`runFrontier_take_drop`).  The
  future of a prefix is the prefix of the future, so a suffix can be discarded
  without changing what the prefix will do.
* **First answers survive pruning after an answer** (`firstAnswer_prune`).  Every
  occurrence after a halted one can be dropped, at every fuel, without changing
  the first answer in occurrence order.  That is the optimization a
  first-answer observation licenses.
* **Pruning is irreversible** (`Controls.same_first_answer`,
  `Controls.different_futures`).  Two frontiers with the same first answer at
  every fuel run to different frontiers: the coarser observation hides futures
  that only the retained frontier still holds.
* **Finality needs a settled prefix** (`firstAnswer_final`,
  `Controls.first_answer_revised`).  Under synchronous frontier scheduling the
  first answer in occurrence order can change with more fuel: a later
  occurrence answers first, an earlier one answers later.  It is final once every
  earlier occurrence has halted.  So a first-answer observation names its
  schedule: position order and completion order coincide only when the prefix
  is settled, as in depth-first exploration.

`firstAnswer` observes the first halted state. Applying it to successful-value
selection requires a halting predicate that characterizes those values, or a
separate success observer. The controls distinguish a halted fault from a later
successful value. These laws describe independent frontier states; they do not
license discarding shared-world effects or retained resource authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction

universe u

namespace OrderedSystem

variable {State : Type u} (system : OrderedSystem State)

/-- Halted states are inert: they have no successors. -/
def HaltedInert : Prop :=
  ∀ state, system.halted state = true → system.step state = []

/-- The first halted state in occurrence order. A successful-value observer
requires a corresponding terminal classification. -/
def firstAnswer (states : List State) : Option State :=
  states.find? system.halted

variable {system}

/-- **Dropping a suffix commutes with execution**: the frontier splits at any
position into the futures of its two parts. -/
theorem runFrontier_take_drop (inert : system.HaltedInert) (fuel count : ℕ)
    (states : List State) :
    system.runFrontier fuel states =
      system.runFrontier fuel (states.take count) ++ system.runFrontier fuel (states.drop count) := by
  conv_lhs => rw [← List.take_append_drop count states]
  exact system.runFrontier_append inert fuel _ _

/-- A halted occurrence stays in place. -/
theorem runFrontier_single_halted (fuel : ℕ) {state : State}
    (halted : system.halted state = true) : system.runFrontier fuel [state] = [state] :=
  system.runFrontier_halted fuel [state] (by simp [halted])

/-- **First answers survive pruning after an answer.** Dropping every
occurrence after a halted one leaves the first answer unchanged at every fuel. -/
theorem firstAnswer_prune (inert : system.HaltedInert) (fuel : ℕ)
    (before after : List State) {answer : State} (halted : system.halted answer = true) :
    system.firstAnswer (system.runFrontier fuel (before ++ answer :: after)) =
      system.firstAnswer (system.runFrontier fuel (before ++ [answer])) := by
  have split : before ++ answer :: after = (before ++ [answer]) ++ after := by simp
  have present : answer ∈ system.runFrontier fuel (before ++ [answer]) := by
    rw [system.runFrontier_append inert, runFrontier_single_halted fuel halted]
    simp
  rw [split, system.runFrontier_append inert]
  simp only [firstAnswer, List.find?_append]
  cases found : (system.runFrontier fuel (before ++ [answer])).find? system.halted with
  | none => exact absurd halted (List.find?_eq_none.mp found answer present)
  | some _ => rfl

/-- **A first answer behind a settled prefix is final**: once every earlier
occurrence has halted, more fuel never changes it. -/
theorem firstAnswer_final (inert : system.HaltedInert) (fuel : ℕ)
    {before : List State} (settled : before.all system.halted = true)
    {answer : State} (halted : system.halted answer = true) (after : List State) :
    system.firstAnswer (system.runFrontier fuel (before ++ answer :: after)) =
      system.firstAnswer (before ++ [answer]) := by
  rw [firstAnswer_prune inert fuel before after halted,
    system.runFrontier_halted fuel (before ++ [answer]) (by simp [settled, halted])]

end OrderedSystem

namespace FrontierObservationControls

open OrderedSystem

/-- Answers, and two occurrences that will answer differently. -/
inductive Item where
  | seven | eight | nine | towardEight | towardNine | slow | slower | fault
  deriving DecidableEq, Repr

def system : OrderedSystem Item where
  step
    | .towardEight => [.eight]
    | .towardNine => [.nine]
    | .slow => [.slower]
    | .slower => [.seven]
    | _ => []
  halted
    | .seven | .eight | .nine | .fault => true
    | _ => false

theorem inert : system.HaltedInert := by
  intro state halted
  cases state <;> simp_all [system]

/-- **Equal first answers at every fuel.** -/
theorem same_first_answer (fuel : ℕ) :
    system.firstAnswer (system.runFrontier fuel [.seven, .towardEight]) =
      system.firstAnswer (system.runFrontier fuel [.seven, .towardNine]) := by
  rw [show [Item.seven, .towardEight] = [] ++ Item.seven :: [.towardEight] from rfl,
    show [Item.seven, .towardNine] = [] ++ Item.seven :: [.towardNine] from rfl,
    firstAnswer_prune inert fuel [] [.towardEight] (answer := .seven) rfl,
    firstAnswer_prune inert fuel [] [.towardNine] (answer := .seven) rfl]

/-- **Different resumable futures.** The retained frontiers diverge after one
step, although no first-answer observation tells them apart. -/
theorem different_futures :
    system.runFrontier 1 [.seven, .towardEight] ≠ system.runFrontier 1 [.seven, .towardNine] := by
  decide

/-- **The first answer in occurrence order is revised under frontier
scheduling**: a later occurrence answers first, then the earlier one answers. -/
theorem first_answer_revised :
    system.firstAnswer (system.runFrontier 1 [.slow, .towardEight]) = some .eight ∧
      system.firstAnswer (system.runFrontier 2 [.slow, .towardEight]) = some .seven := by
  decide

/-- Successful values can have a different observation from terminal states. -/
def successful : Item → Bool
  | .seven | .eight | .nine => true
  | _ => false

/-- Selecting the first terminal and keeping only its prefix can lose a later
successful value. Halting alone therefore does not justify value selection. -/
theorem first_terminal_can_precede_success :
    system.firstAnswer [.fault, .seven] = some .fault ∧
      ([Item.fault, .seven].find? successful) = some .seven ∧
      (([Item.fault, .seven].take 1).find? successful) = none := by
  decide

end FrontierObservationControls

end Mettapedia.GSLT.Distinction
