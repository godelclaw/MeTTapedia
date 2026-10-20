import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.FiniteMuCalculusSource
import Mettapedia.OSLF.NativeTypes.Instances.Natural.Authored

/-!
# Execution of the authored counter's finite recurrence query

The existing fixed-point MeTTa library checks the complete parity observation
of the authored successor system. These certificates cover recurring even
states, empty acceptance, and insufficient query allowance at either phase.
They retain the complete store, answer list and I/O, then use determinism to
characterize every completed execution of the same query.

This is a selected workload correspondence, not correctness of the evaluator
on arbitrary fixed-point formulas. Query allowance and evaluator fuel are
distinct. The source Büchi property concerns existence of an infinite run;
it grants neither incoming coverage nor availability of a native provider.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.NaturalCounterExecution

open MeTTaIL WireKit
open Mettapedia.GSLT.LanguageDef.CettaWire
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Instances.Natural
open Mettapedia.OSLF.NativeTypes.Decision
open FiniteMuCalculusRuntime FiniteMuCalculusWire

/-- The existing shared Büchi formula; action zero denotes successor. -/
def formula : Formula Nat 1 := Formula.buchi 0

def queryBudget : Nat := FiniteMuCalculus.requiredBudget (State := Fin 2) formula

/-- Query encoding shared with the runtime gate. Both the finite carrier and
edge table come from the source counter's certified observation. -/
def queryTerm (accepting : Finset (Fin 2)) (budget : Nat) (phase : Fin 2) : Term :=
  .application "native:mu:check"
    [formulaTerm Term.natural formula,
     encodeList (Term.natural ∘ Fin.val) (List.finRange 2),
     encodeList (fun edge => Term.application "NativeEdge"
       [.natural edge.1.val, .natural 0, .natural edge.2.val]) Counter.edges,
     encodeList id [encodeList (Term.natural ∘ Fin.val)
       ((List.finRange 2).filter fun state => state ∈ accepting)],
     .natural budget, .natural phase.val]

def initial (state : Effects.State) (accepting : Finset (Fin 2)) (budget : Nat) (phase : Fin 2) : Eval.Configuration :=
  Eval.start state (encoded (queryTerm accepting budget phase))

def executionFuel : Nat := 30000

/- The store has function-valued fields, so equality of whole outcomes does
not have a decidable instance. Submit reflexivity directly to the kernel,
which checks the concrete execution by reduction. No evaluator result is
trusted or imported into the proof. The helper only accepts closed goals. -/
open Lean Meta Elab Tactic in
private meta def certifyClosedExecution : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let type ← goal.getType
    if type.hasFVar || type.hasMVar || type.hasLevelParam then
      throwError "expected a closed execution equality"
    let proof ← forallTelescope type fun parameters body => do
      let some (_, _, rhs) := body.eq? | throwError "expected equality"
      mkLambdaFVars parameters (← mkEqRefl rhs)
    let name ← withOptions (Elab.async.set · false) do
      mkAuxLemma [] type proof
    goal.assign (mkConst name)
  replaceMainGoal []

set_option maxRecDepth 100000 in
private theorem even_zero : ∀ state : Effects.State, Eval.run library.runtime executionFuel
    (initial state {0} queryBudget 0) =
    .complete state [.symbol "NativeProved"] [] [] := by
  run_tac certifyClosedExecution

set_option maxRecDepth 100000 in
private theorem even_one : ∀ state : Effects.State, Eval.run library.runtime executionFuel
    (initial state {0} queryBudget 1) =
    .complete state [.symbol "NativeProved"] [] [] := by
  run_tac certifyClosedExecution

set_option maxRecDepth 100000 in
private theorem empty_zero : ∀ state : Effects.State, Eval.run library.runtime executionFuel
    (initial state ∅ queryBudget 0) =
    .complete state [.symbol "NativeRefuted"] [] [] := by
  run_tac certifyClosedExecution

set_option maxRecDepth 100000 in
private theorem empty_one : ∀ state : Effects.State, Eval.run library.runtime executionFuel
    (initial state ∅ queryBudget 1) =
    .complete state [.symbol "NativeRefuted"] [] [] := by
  run_tac certifyClosedExecution

set_option maxRecDepth 100000 in
private theorem short_zero : ∀ state : Effects.State, Eval.run library.runtime executionFuel
    (initial state {0} 0 0) =
    .complete state [.symbol "NativeUnknown"] [] [] := by
  run_tac certifyClosedExecution

set_option maxRecDepth 100000 in
private theorem short_one : ∀ state : Effects.State, Eval.run library.runtime executionFuel
    (initial state {0} 0 1) =
    .complete state [.symbol "NativeUnknown"] [] [] := by
  run_tac certifyClosedExecution

theorem even_run (state : Effects.State) (phase : Fin 2) : Eval.run library.runtime executionFuel
    (initial state {0} queryBudget phase) =
    .complete state [.symbol "NativeProved"] [] [] := by
  fin_cases phase
  · exact even_zero state
  · exact even_one state

theorem empty_run (state : Effects.State) (phase : Fin 2) : Eval.run library.runtime executionFuel
    (initial state ∅ queryBudget phase) =
    .complete state [.symbol "NativeRefuted"] [] [] := by
  fin_cases phase
  · exact empty_zero state
  · exact empty_one state

theorem short_run (state : Effects.State) (phase : Fin 2) : Eval.run library.runtime executionFuel
    (initial state {0} 0 phase) =
    .complete state [.symbol "NativeUnknown"] [] [] := by
  fin_cases phase
  · exact short_zero state
  · exact short_one state

/-- Public checker verdict encoding, retaining rejection and uncertainty. -/
def verdict {P : Prop} : Option (Reference.Core.Outcome P) → String
  | none => "NativeRejected"
  | some (.proved _) => "NativeProved"
  | some (.refuted _) => "NativeRefuted"
  | some .unknown => "NativeUnknown"

theorem verdict_proved_iff {P : Prop} (result : Option (Reference.Core.Outcome P)) :
    verdict result = "NativeProved" ↔
      result.map Reference.Core.Outcome.answer = some (some true) := by
  cases result with
  | none => simp [verdict]
  | some outcome => cases outcome <;> simp [verdict, Reference.Core.Outcome.answer]

theorem verdict_refuted_iff {P : Prop} (result : Option (Reference.Core.Outcome P)) :
    verdict result = "NativeRefuted" ↔
      result.map Reference.Core.Outcome.answer = some (some false) := by
  cases result with
  | none => simp [verdict]
  | some outcome => cases outcome <;> simp [verdict, Reference.Core.Outcome.answer]

def checkerVerdict (accepting : Finset (Fin 2)) (phase : Fin 2) : String :=
  verdict (Mettapedia.OSLF.NativeTypes.Executable.Finite.check Counter.table
    (Formula.buchi .future) (fun _ => accepting) queryBudget phase)

private theorem even_checker (phase : Fin 2) : checkerVerdict {0} phase = "NativeProved" := by
  revert phase
  decide +kernel

private theorem empty_checker (phase : Fin 2) : checkerVerdict ∅ phase = "NativeRefuted" := by
  revert phase
  decide +kernel

/-- The actual MeTTa evaluator and the existing public finite checker agree
on the two counter observations, including the full execution packet. -/
theorem selected_run (state : Effects.State) (accepting : Finset (Fin 2))
    (selected : accepting = {0} ∨ accepting = ∅) (phase : Fin 2) :
    Eval.run library.runtime executionFuel (initial state accepting queryBudget phase) =
      .complete state [.symbol (checkerVerdict accepting phase)] [] [] := by
  rcases selected with rfl | rfl
  · rw [even_checker]
    exact even_run state phase
  · rw [empty_checker]
    exact empty_run state phase

theorem selected_completed_iff (before : Effects.State) (accepting : Finset (Fin 2))
    (selected : accepting = {0} ∨ accepting = ∅) (phase : Fin 2)
    (after : Effects.State) (answers input output : List OSLFCore.Atom) :
    (∃ fuel, Eval.run library.runtime fuel (initial before accepting queryBudget phase) =
      .complete after answers input output) ↔
      after = before ∧ answers = [.symbol (checkerVerdict accepting phase)] ∧
        input = [] ∧ output = [] :=
  Eval.path_completed_iff library.runtime _ before _ [] []
    (Eval.completed_run_has_path library.runtime executionFuel _ before _ [] []
      (selected_run before accepting selected phase)) after answers input output

theorem selected_verdict_iff (before : Effects.State) (accepting : Finset (Fin 2))
    (selected : accepting = {0} ∨ accepting = ∅) (phase : Fin 2) (answer : String) :
    (∃ fuel, Eval.run library.runtime fuel (initial before accepting queryBudget phase) =
      .complete before [.symbol answer] [] []) ↔ answer = checkerVerdict accepting phase := by
  simpa using selected_completed_iff before accepting selected phase before [.symbol answer] [] []

/-- Matching the truth value alone is insufficient: no completed execution
may add a second verdict occurrence. -/
theorem duplicate_verdict_never (before : Effects.State) (accepting : Finset (Fin 2))
    (selected : accepting = {0} ∨ accepting = ∅) (phase : Fin 2) (answer : OSLFCore.Atom) :
    ¬ ∃ fuel after input output,
      Eval.run library.runtime fuel (initial before accepting queryBudget phase) =
        .complete after [answer, answer] input output := by
  rintro ⟨fuel, after, input, output, completed⟩
  have packet := (selected_completed_iff before accepting selected phase after _ input output).mp
    ⟨fuel, completed⟩
  have lengths := congrArg List.length packet.2.1
  simp at lengths

open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.OSLF.NativeTypes.Semantics.BuchiTransport
open Mettapedia.GSLT.LanguageDef.Examples

/-- A completed positive MeTTa query means an actual accepting infinite path
of the authored GSLT, for every natural starting value. -/
theorem proved_iff_authored_path (before : Effects.State) (base : BasePremiseEvaluator)
    (accepting : Finset (Fin 2)) (selected : accepting = {0} ∨ accepting = ∅) (number : Nat) :
    (∃ fuel, Eval.run library.runtime fuel
      (initial before accepting queryBudget (Counter.phase number)) =
      .complete before [.symbol "NativeProved"] [] []) ↔
    BuchiPath (transitionSystem (gsltSpan (Authored.theory base))) .future
      (Authored.accepting accepting) (NativeNaturalCounter.counter number) := by
  rw [selected_verdict_iff before accepting selected, eq_comm]
  exact (verdict_proved_iff _).trans
    (Authored.check_buchi_iff base accepting queryBudget number (by decide +kernel))

theorem refuted_iff_no_authored_path (before : Effects.State) (base : BasePremiseEvaluator)
    (accepting : Finset (Fin 2)) (selected : accepting = {0} ∨ accepting = ∅) (number : Nat) :
    (∃ fuel, Eval.run library.runtime fuel
      (initial before accepting queryBudget (Counter.phase number)) =
      .complete before [.symbol "NativeRefuted"] [] []) ↔
    ¬ BuchiPath (transitionSystem (gsltSpan (Authored.theory base))) .future
      (Authored.accepting accepting) (NativeNaturalCounter.counter number) := by
  rw [selected_verdict_iff before accepting selected, eq_comm]
  exact (verdict_refuted_iff _).trans
    (Authored.check_negative_iff base accepting queryBudget number (by decide +kernel))

/-- The same positive packet is the meaning of the existing native formula
on authored terms, not only a graph-level recurrence observation. -/
theorem proved_iff_authored_formula (before : Effects.State) (base : BasePremiseEvaluator)
    (accepting : Finset (Fin 2)) (selected : accepting = {0} ∨ accepting = ∅) (number : Nat) :
    (∃ fuel, Eval.run library.runtime fuel
      (initial before accepting queryBudget (Counter.phase number)) =
      .complete before [.symbol "NativeProved"] [] []) ↔
    satisfies (transitionSystem (gsltSpan (Authored.theory base)))
      (fun _ => Authored.accepting accepting) (Formula.buchi .future)
      (NativeNaturalCounter.counter number) := by
  rw [selected_verdict_iff before accepting selected, eq_comm]
  exact (verdict_proved_iff _).trans
    (Authored.check_formula_iff base accepting queryBudget number (by decide +kernel))

theorem short_completed_iff (before : Effects.State) (phase : Fin 2)
    (after : Effects.State) (answers input output : List OSLFCore.Atom) :
    (∃ fuel, Eval.run library.runtime fuel (initial before {0} 0 phase) =
      .complete after answers input output) ↔
      after = before ∧ answers = [.symbol "NativeUnknown"] ∧ input = [] ∧ output = [] :=
  Eval.path_completed_iff library.runtime _ before _ [] []
    (Eval.completed_run_has_path library.runtime executionFuel _ before _ [] []
      (short_run before phase)) after answers input output

/-- Insufficient query allowance never becomes refutation, however much
evaluator fuel is supplied. -/
theorem short_never_refutes (before : Effects.State) (phase : Fin 2) :
    ¬ ∃ fuel after input output, Eval.run library.runtime fuel (initial before {0} 0 phase) =
      .complete after [.symbol "NativeRefuted"] input output := by
  rintro ⟨fuel, after, input, output, completed⟩
  have packet := (short_completed_iff before phase after _ input output).mp ⟨fuel, completed⟩
  simp at packet

/-- Exhausting the execution machine is distinct from a returned Unknown
packet and cannot authorize any completed verdict. -/
theorem no_evaluator_fuel (before : Effects.State) (accepting : Finset (Fin 2))
    (budget : Nat) (phase : Fin 2) :
    Eval.run library.runtime 0 (initial before accepting budget phase) =
      .exhausted (initial before accepting budget phase) := rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.NaturalCounterExecution
