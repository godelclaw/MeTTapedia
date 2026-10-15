import Mettapedia.Machines.ProductiveCoreAdapters

/-!
# CEK and Krivine instances of the common finite-run machine

The instances retain the existing evaluator states, loaders and transitions.
Their completed-value observers distinguish answers from stuck control.
Finite execution reflects and realizes the existing reachable-answer
judgments. Existing evaluator-to-machine adequacy transports to these runs;
no converse evaluator theorem or agreement of evaluation strategies is
inferred. Computational occurrence prices and terminal observation cost
remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProductiveFunctionalMachines

open Mettapedia.GSLT.Distinction.ProductiveBlocks
open ProductiveCoreAdapters

def cekMachine : Machine CEK.St (Occurrence CEK.St) CEK.Val Empty := answerMachine cekAnswerCore
def krivineMachine : Machine Krivine.KSt (Occurrence Krivine.KSt) Krivine.NVal Empty := answerMachine krivineAnswerCore

theorem cek_step_iff (state next : CEK.St) :
    cekMachine.step state = some (.publish [(state, next)] next) ↔ CEK.StepRel state next := by
  constructor
  · intro computed
    cases observed : cekAnswer state with
    | some value => simp [cekMachine, answerMachine, cekAnswerCore, observed] at computed
    | none =>
        simp only [cekMachine, answerMachine, cekAnswerCore, observed] at computed
        cases step : CEK.step state with
        | none => simp [step] at computed
        | some found =>
            simp only [step, Option.map_some, Option.some.injEq, Transition.publish.injEq] at computed
            obtain ⟨_, rfl⟩ := computed
            exact step
  · intro stepped
    exact answer_step cekAnswerCore stepped

theorem krivine_step_iff (state next : Krivine.KSt) :
    krivineMachine.step state = some (.publish [(state, next)] next) ↔ Krivine.KStepRel state next := by
  constructor
  · intro computed
    cases observed : krivineAnswer state with
    | some value => simp [krivineMachine, answerMachine, krivineAnswerCore, observed] at computed
    | none =>
        simp only [krivineMachine, answerMachine, krivineAnswerCore, observed] at computed
        cases step : Krivine.kstep state with
        | none => simp [step] at computed
        | some found =>
            simp only [step, Option.map_some, Option.some.injEq, Transition.publish.injEq] at computed
            obtain ⟨_, rfl⟩ := computed
            exact step
  · intro stepped
    exact answer_step krivineAnswerCore stepped

theorem cek_finish_iff (state : CEK.St) (value : CEK.Val) :
    cekMachine.step state = some (.finish value) ↔ cekAnswer state = some value := by
  constructor
  · intro computed
    cases observed : cekAnswer state with
    | some found =>
        simp only [cekMachine, answerMachine, cekAnswerCore, observed, Option.some.injEq, Transition.finish.injEq] at computed
        exact congrArg some computed
    | none =>
        cases step : CEK.step state <;> simp [cekMachine, answerMachine, cekAnswerCore, observed, step] at computed
  · exact observed_finish cekAnswerCore

theorem krivine_finish_iff (state : Krivine.KSt) (value : Krivine.NVal) :
    krivineMachine.step state = some (.finish value) ↔ krivineAnswer state = some value := by
  constructor
  · intro computed
    cases observed : krivineAnswer state with
    | some found =>
        simp only [krivineMachine, answerMachine, krivineAnswerCore, observed, Option.some.injEq, Transition.finish.injEq] at computed
        exact congrArg some computed
    | none =>
        cases step : Krivine.kstep state <;> simp [krivineMachine, answerMachine, krivineAnswerCore, observed, step] at computed
  · exact observed_finish krivineAnswerCore

theorem cek_produces_iff (term : Tm) (value : CEK.Val) :
    cekAnswerCore.Produces term value ↔
      ∃ fuel events, cekMachine.run fuel (cekCore.load term) = (events, .finished value) :=
  produces_iff_finished cekAnswerCore term value

theorem krivine_produces_iff (term : Tm) (value : Krivine.NVal) :
    krivineAnswerCore.Produces term value ↔
      ∃ fuel events, krivineMachine.run fuel (krivineCore.load term) = (events, .finished value) :=
  produces_iff_finished krivineAnswerCore term value

theorem cek_eval_realized {fuel : Nat} {term : Tm} {value : CEK.Val}
    (evaluated : CEK.evalV fuel [] term = some value) :
    ∃ budget events, cekMachine.run budget (cekCore.load term) = (events, .finished value) :=
  (cek_produces_iff term value).mp (cek_eval_to_produces evaluated)

theorem krivine_eval_realized {fuel : Nat} {term : Tm} {value : Krivine.NVal}
    (evaluated : Krivine.evalN fuel [] term = some value) :
    ∃ budget events, krivineMachine.run budget (krivineCore.load term) = (events, .finished value) :=
  (krivine_produces_iff term value).mp (krivine_eval_to_produces evaluated)

theorem cek_trace_resume {state residual : CEK.St} {events : List (Occurrence CEK.St)}
    (trace : Trace cekCore state events residual) (second : Nat) :
    cekMachine.run (events.length + second) state =
      (events ++ (cekMachine.run second residual).1, (cekMachine.run second residual).2) :=
  trace_answer_resume cekAnswerCore trace second

theorem krivine_trace_resume {state residual : Krivine.KSt} {events : List (Occurrence Krivine.KSt)}
    (trace : Trace krivineCore state events residual) (second : Nat) :
    krivineMachine.run (events.length + second) state =
      (events ++ (krivineMachine.run second residual).1, (krivineMachine.run second residual).2) :=
  trace_answer_resume krivineAnswerCore trace second

theorem cek_computational_account (price : CEK.St → Nat) (fuel : Nat) (state : CEK.St) :
    cekMachine.spent (computationalPrice cekCore price) fuel state = charge price (cekMachine.run fuel state).1 :=
  answer_spent_is_charge cekAnswerCore price fuel state

theorem krivine_computational_account (price : Krivine.KSt → Nat) (fuel : Nat) (state : Krivine.KSt) :
    krivineMachine.spent (computationalPrice krivineCore price) fuel state = charge price (krivineMachine.run fuel state).1 :=
  answer_spent_is_charge krivineAnswerCore price fuel state

end Mettapedia.Machines.ProductiveFunctionalMachines
