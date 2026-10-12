import Mettapedia.GSLT.Causality.ContextualRealization
import Mettapedia.GSLT.Causality.ScriptedExecution

/-!
# Representation change retaining component interventions

A state equivalence transports the evaluator by conjugation and transports
every stored table entry. Input symbols and table/evaluator activity remain
unchanged. The independently defined backup algorithm commutes with this
recoding, including mismatch and table-exhaustion branches.

Evaluator-replacement commands are conjugated as well. Their finite sequences
commute with execution and cover every target component context. The general
contextual-realization bridge therefore transports modal formulas and full
counterfactual comparison. This is an actual constructed instance of the
context square, rather than an assertion that state correspondence alone
supplies it.

The negative control shows that forgetting the player and evaluator does not
admit even a functional interpretation of one declared component intervention.
The positive control changes Boolean machine states to `Fin 2` and retains the
intervention that separates direct execution from a recorded backup.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ScriptedExecutionRecoding

open Mettapedia.GSLT
open Mettapedia.GSLT.ScriptedBackup
open Mettapedia.GSLT.Causality.ScriptedExecution
open Mettapedia.GSLT.Causality.Abstraction
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence

variable {State Target Input : Type} [DecidableEq Input]

def recodeEvaluator (coding : State ≃ Target) (evaluator : State → Input → State) :
    Target → Input → Target :=
  fun state input => coding (evaluator (coding.symm state) input)

def recodePlayer (coding : State ≃ Target) (player : Player State Input) : Player Target Input :=
  ⟨coding player.current, player.remaining.map (fun row => (row.1, coding row.2)), player.live⟩

def recodeMachine (coding : State ≃ Target) (machine : Machine State Input) :
    Machine Target Input :=
  ⟨recodeEvaluator coding machine.evaluator, recodePlayer coding machine.player⟩

def recodeCommand (coding : State ≃ Target) : Command State Input → Command Target Input
  | .feed input => .feed input
  | .replaceEvaluator evaluator => .replaceEvaluator (recodeEvaluator coding evaluator)

omit [DecidableEq Input] in
theorem recodeEvaluator_inverse (coding : State ≃ Target) (evaluator : State → Input → State) :
    recodeEvaluator coding.symm (recodeEvaluator coding evaluator) = evaluator := by
  funext state input
  simp [recodeEvaluator]

omit [DecidableEq Input] in
theorem recodePlayer_inverse (coding : State ≃ Target) (player : Player State Input) :
    recodePlayer coding.symm (recodePlayer coding player) = player := by
  cases player with
  | mk current remaining live =>
      simp [recodePlayer, List.map_map, Function.comp_def]

omit [DecidableEq Input] in
theorem recodeMachine_inverse (coding : State ≃ Target) (machine : Machine State Input) :
    recodeMachine coding.symm (recodeMachine coding machine) = machine := by
  cases machine with
  | mk evaluator player =>
      simp only [recodeMachine, recodeEvaluator_inverse, recodePlayer_inverse]

omit [DecidableEq Input] in
theorem recodeCommand_inverse (coding : State ≃ Target) (command : Command State Input) :
    recodeCommand coding.symm (recodeCommand coding command) = command := by
  cases command <;> simp [recodeCommand, recodeEvaluator_inverse]

omit [DecidableEq Input] in
theorem recodeCommands_inverse (coding : State ≃ Target) (commands : List (Command State Input)) :
    (commands.map (recodeCommand coding)).map (recodeCommand coding.symm) = commands := by
  induction commands with
  | nil => rfl
  | cons command commands ih => simp only [List.map_cons, recodeCommand_inverse, ih]

omit [DecidableEq Input] in
theorem recodeMachine_comp {Further : Type} (first : State ≃ Target) (second : Target ≃ Further)
    (machine : Machine State Input) :
    recodeMachine second (recodeMachine first machine) =
      recodeMachine (first.trans second) machine := by
  cases machine with
  | mk evaluator player =>
      cases player with
      | mk current remaining live =>
          simp [recodeMachine, recodePlayer, Equiv.trans,
            List.map_map, Function.comp_def]
          rfl

omit [DecidableEq Input] in
theorem recodeCommand_comp {Further : Type} (first : State ≃ Target) (second : Target ≃ Further)
    (command : Command State Input) :
    recodeCommand second (recodeCommand first command) =
      recodeCommand (first.trans second) command := by
  cases command <;> rfl

omit [DecidableEq Input] in
/-- Table-entry occurrences are transported without deduplication. -/
theorem recodePlayer_table_length (coding : State ≃ Target) (player : Player State Input) :
    (recodePlayer coding player).remaining.length = player.remaining.length :=
  List.length_map _

/-- The actual context composition executes the inner commands first;
translation retains that ordering rather than re-scheduling replacements. -/
theorem context_comp_commutes (coding : State ≃ Target)
    (outer inner : List (Command State Input)) :
    ((rules (State := State) (Input := Input)).compose outer inner).map (recodeCommand coding) =
      (rules (State := Target) (Input := Input)).compose
        (outer.map (recodeCommand coding)) (inner.map (recodeCommand coding)) :=
  List.map_append

/-- Both the player and the declared source of its successor are retained. -/
theorem advance_commutes (coding : State ≃ Target) (evaluator : State → Input → State)
    (player : Player State Input) (input : Input) :
    advance (recodeEvaluator coding evaluator) (recodePlayer coding player) input =
      (recodePlayer coding (advance evaluator player input).1,
        (advance evaluator player input).2) := by
  cases player with
  | mk current remaining live =>
      cases live
      · cases remaining with
        | nil => simp [advance, recodePlayer, recodeEvaluator]
        | cons row rest =>
            rcases row with ⟨expected, target⟩
            by_cases sameInput : input = expected <;>
              simp [advance, recodePlayer, recodeEvaluator, sameInput]
      · simp [advance, recodePlayer, recodeEvaluator]

theorem tick_commutes (coding : State ≃ Target) (machine : Machine State Input) (input : Input) :
    recodeMachine coding (tick machine input) = tick (recodeMachine coding machine) input := by
  have successor := congrArg Prod.fst (advance_commutes coding machine.evaluator machine.player input)
  exact congrArg (Machine.mk (recodeEvaluator coding machine.evaluator)) successor.symm

theorem command_commutes (coding : State ≃ Target) (command : Command State Input)
    (machine : Machine State Input) :
    recodeMachine coding (applyCommand command machine) =
      applyCommand (recodeCommand coding command) (recodeMachine coding machine) := by
  cases command with
  | feed input => exact tick_commutes coding machine input
  | replaceEvaluator evaluator => rfl

theorem plug_commutes (coding : State ≃ Target) (commands : List (Command State Input))
    (machine : Machine State Input) :
    recodeMachine coding (plug commands machine) =
      plug (commands.map (recodeCommand coding)) (recodeMachine coding machine) := by
  induction commands generalizing machine with
  | nil => rfl
  | cons command commands ih =>
      change recodeMachine coding (plug commands (applyCommand command machine)) =
        plug (commands.map (recodeCommand coding))
          (applyCommand (recodeCommand coding command) (recodeMachine coding machine))
      rw [ih, command_commutes]

/-- Reflection is proved from the target algorithm, using its actual input
event and the tick commutation law. -/
def operational (coding : State ≃ Target) : SemanticCoveredTranslation
    (theory (tick (State := State) (Input := Input)))
    (theory (tick (State := Target) (Input := Input))) where
  mapTerm := recodeMachine coding
  mapEquiv := by intro left right equal; cases equal; rfl
  mapStep := by
    rintro source target ⟨input, rfl⟩
    exact ⟨input, tick_commutes coding source input⟩
  liftStep := by
    rintro source target ⟨input, rfl⟩
    exact ⟨tick source input, ⟨input, rfl⟩, tick_commutes coding source input⟩

def interventions (coding : State ≃ Target) : InterventionMap
    (componentClass (State := State) (Input := Input))
    (componentClass (State := Target) (Input := Input)) where
  map commands := commands.map (recodeCommand coding)
  admissible _ := AdmissibleClass.top_admissible _

theorem interventions_onto (coding : State ≃ Target) :
    Function.Surjective (interventions (Input := Input) coding).label := by
  rintro ⟨commands, _⟩
  refine ⟨⟨commands.map (recodeCommand coding.symm), AdmissibleClass.top_admissible _⟩, ?_⟩
  apply Subtype.ext
  exact recodeCommands_inverse coding.symm commands

theorem observation_commutes (coding : State ≃ Target) (value : State)
    (machine : Machine State Input) :
    (observations (State := State)).observes value machine ↔
      (observations (State := Target)).observes (coding value) (recodeMachine coding machine) :=
  coding.injective.eq_iff.symm

/-- The square is earned for every actual command sequence. -/
def cover (coding : State ≃ Target) : SystemCover
    ((componentClass (State := State) (Input := Input)).saturated observations)
    ((componentClass (State := Target) (Input := Input)).saturated observations) :=
  ContextualRealization.saturatedCover (operational coding) (interventions coding)
    observations observations coding (observation_commutes coding)
    (fun {_} _ machine => plug_commutes coding _ machine)

theorem formula_iff (coding : State ≃ Target)
    (formula : Formula ((componentClass (State := State) (Input := Input)).saturated observations).Atom
      ((componentClass (State := State) (Input := Input)).saturated observations).Label)
    (machine : Machine State Input) :
    ((componentClass (State := Target)).saturated observations).sat
        (formula.map (cover coding).mapAtom (cover coding).mapLabel) (recodeMachine coding machine) ↔
      ((componentClass (State := State)).saturated observations).sat formula machine :=
  (cover coding).sat_map formula machine

theorem all_rungs_iff (coding : State ≃ Target) (rung : Hierarchy.Rung)
    (left right : Machine State Input) :
    Hierarchy.Agree (componentClass (State := Target)) observations rung
        (recodeMachine coding left) (recodeMachine coding right) ↔
      Hierarchy.Agree (componentClass (State := State)) observations rung left right :=
  ContextualRealization.all_rungs_iff (operational coding) (interventions coding)
    observations observations coding (observation_commutes coding)
    (fun {_} _ machine => plug_commutes coding _ machine)
    coding.surjective (interventions_onto coding) rung left right

namespace Controls

def boolToFin : Bool ≃ Fin 2 := finTwoEquiv.symm

/-- Changing representation retains the explicit evaluator intervention
that input-only testing fails to distinguish. -/
theorem recoded_replacement_separates :
    ((componentClass (State := Fin 2)).saturated observations).sat
        (ScriptedExecution.Controls.replacementTrue.map (cover boolToFin).mapAtom
          (cover boolToFin).mapLabel)
        (recodeMachine boolToFin ScriptedExecution.Controls.executor) ∧
      ¬ ((componentClass (State := Fin 2)).saturated observations).sat
        (ScriptedExecution.Controls.replacementTrue.map (cover boolToFin).mapAtom
          (cover boolToFin).mapLabel)
        (recodeMachine boolToFin ScriptedExecution.Controls.backup) := by
  exact ⟨(formula_iff boolToFin _ _).mpr ScriptedExecution.Controls.replacement_formula_separates.1,
    fun accepted => ScriptedExecution.Controls.replacement_formula_separates.2
      ((formula_iff boolToFin _ _).mp accepted)⟩

/-- Equal displayed states cannot supply a single target intervention
operator for the declared replacement: the two retained components respond
differently. This obstructs the square itself, before modal transport. -/
theorem no_displayed_replacement_operator :
    ¬ ∃ operation : Bool → Bool, ∀ machine : Machine Bool Bool,
      operation machine.player.current =
        (plug (replacementRun ScriptedExecution.Controls.forceTrue [false]) machine).player.current := by
  rintro ⟨operation, commutes⟩
  have direct := commutes ScriptedExecution.Controls.executor
  have backup := commutes ScriptedExecution.Controls.backup
  change operation false = true at direct
  change operation false = false at backup
  exact Bool.noConfusion (direct.symm.trans backup)

end Controls

end Mettapedia.GSLT.Causality.ScriptedExecutionRecoding
