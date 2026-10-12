import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Captured authored function names in the explicit PeTTa machine

The closed machine treats variable-headed applications as data. PeTTa's
translator instead emits runtime dispatch after evaluating the arguments.
This component admits saturated calls to captured authored symbols whose
arguments are all strict. It uses the existing argument, clause and frame
machinery; closures, primitives, raw arguments and dynamic redefinition are
separate coverage obligations.

The two transition rules are disjoint: an admitted captured call replaces the
old data-entry step. It is not an additional nondeterministic alternative.
The frozen program is an execution context, not permission to reuse a result
under a different program. Existing closed-fragment laws remain unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BoundCalls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program)
open Eval

/-- Runtime variable dispatch evaluates arguments before invoking an authored
function. Literal `Atom` domains, I/O and standard primitive heads are excluded.
Literal control syntax has its own entry rules; a captured symbol spelling a
control word does not automatically inherit those literal rules. -/
def admitted (program : Program) (head : String) (arguments : List Atom) : Bool :=
  !ioHead head && !StdLib.known head &&
    program.equations.any (fun equation =>
      equation.head == head && equation.arguments.length == arguments.length) &&
    (List.range arguments.length).all (fun index => !argumentIsRaw program head index)

def target (program : Program) : Control → Option Control
  | .evaluate bindings (.expression (.var name :: arguments)) =>
      match applySubst bindings (.var name) with
      | .symbol head =>
          if admitted program head arguments then
            some (.arguments bindings (.function head) arguments [] 0)
          else none
      | _ => none
  | _ => none

/-- Admission is witnessed by a source equation of this arity and strict
demand at every argument occurrence, independently of the machine step. -/
theorem admitted_iff (program : Program) (head : String) (arguments : List Atom) :
    admitted program head arguments = true ↔
      ioHead head = false ∧ StdLib.known head = false ∧
      (∃ equation ∈ program.equations,
        equation.head = head ∧ equation.arguments.length = arguments.length) ∧
      (∀ index < arguments.length, argumentIsRaw program head index = false) := by
  simp [admitted, Bool.and_eq_true, List.any_eq_true, List.all_eq_true, and_assoc]

theorem target_captured (program : Program) (bindings : Subst) (name head : String)
    (arguments : List Atom) (captured : applySubst bindings (.var name) = .symbol head)
    (authorized : admitted program head arguments = true) :
    target program (.evaluate bindings (.expression (.var name :: arguments))) =
      some (.arguments bindings (.function head) arguments [] 0) := by
  simp [target, captured, authorized]

theorem target_spec (program : Program) (source selected : Control) :
    target program source = some selected ↔
      ∃ bindings name head arguments,
        source = .evaluate bindings (.expression (.var name :: arguments)) ∧
        applySubst bindings (.var name) = .symbol head ∧
        admitted program head arguments = true ∧
        selected = .arguments bindings (.function head) arguments [] 0 := by
  constructor
  · intro computed
    cases source with
    | evaluate bindings expression =>
      cases expression with
      | expression items =>
        cases items with
        | nil => simp [target] at computed
        | cons first arguments =>
          cases first with
          | var name =>
            cases captured : applySubst bindings (.var name) with
            | symbol head =>
              simp only [target, captured] at computed
              split at computed
              · rename_i authorized
                exact ⟨bindings, name, head, arguments, rfl, captured, authorized,
                  (Option.some.inj computed).symm⟩
              · contradiction
            | var value => simp [target, captured] at computed
            | grounded value => simp [target, captured] at computed
            | expression values => simp [target, captured] at computed
          | symbol head => simp [target] at computed
          | grounded value => simp [target] at computed
          | expression values => simp [target] at computed
      | var name => simp [target] at computed
      | symbol head => simp [target] at computed
      | grounded value => simp [target] at computed
    | arguments bindings destination pending values index => simp [target] at computed
    | sequence pending answers => simp [target] at computed
    | returned answers => simp [target] at computed
    | fault reason => simp [target] at computed
  · rintro ⟨bindings, name, head, arguments, rfl, captured, authorized, rfl⟩
    exact target_captured program bindings name head arguments captured authorized

inductive Transition (program : Program) : Configuration → Configuration → Prop where
  | captured {source : Configuration} (bindings : Subst) (name head : String)
      (arguments : List Atom)
      (control : source.control = .evaluate bindings (.expression (.var name :: arguments)))
      (resolved : applySubst bindings (.var name) = .symbol head)
      (authorized : admitted program head arguments = true) :
      Transition program source
        { source with control := .arguments bindings (.function head) arguments [] 0 }
  | core {source selected : Configuration}
      (unchanged : target program source.control = none)
      (original : DeclarativeSpec.Transition program source selected) :
      Transition program source selected

def step (program : Program) (source : Configuration) : Option Configuration :=
  match target program source.control with
  | some control => some { source with control }
  | none => Eval.step program source

/-- The executable extension checks precisely the independent rule's source
conditions; all other transitions are supplied by the existing calculus. -/
theorem step_iff (program : Program) (source selected : Configuration) :
    step program source = some selected ↔ Transition program source selected := by
  constructor
  · intro computed
    cases resolved : target program source.control with
    | none =>
      exact .core resolved (Eval.step_transition (by simpa [step, resolved] using computed))
    | some control =>
      obtain ⟨bindings, name, head, arguments, shape, captured, authorized, rfl⟩ :=
        (target_spec program source.control control).mp resolved
      have selectedEq : { source with control := .arguments bindings (.function head) arguments [] 0 } = selected :=
        Option.some.inj (by simpa [step, resolved] using computed)
      rw [← selectedEq]
      exact .captured bindings name head arguments shape captured authorized
  · intro transition
    cases transition with
    | captured bindings name head arguments shape captured authorized =>
      simp [step, shape, target_captured program bindings name head arguments captured authorized]
    | core unchanged original =>
      simpa [step, unchanged] using Eval.transition_step original

theorem deterministic {program : Program} {source first second : Configuration}
    (left : Transition program source first) (right : Transition program source second) :
    first = second :=
  Option.some.inj (((step_iff program source first).mpr left).symm.trans
    ((step_iff program source second).mpr right))

theorem core_step_unchanged (program : Program) (source : Configuration)
    (unresolved : target program source.control = none) :
    step program source = Eval.step program source := by simp [step, unresolved]

/-- A captured call retains the exact store, continuation and I/O. Resolving
a function name neither performs an effect nor duplicates a continuation. -/
theorem captured_context_retained (program : Program) (source : Configuration)
    (bindings : Subst) (name head : String) (arguments : List Atom)
    (shape : source.control = .evaluate bindings (.expression (.var name :: arguments)))
    (captured : applySubst bindings (.var name) = .symbol head)
    (authorized : admitted program head arguments = true) :
    ∃ selected, step program source = some selected ∧
      selected.state = source.state ∧ selected.frames = source.frames ∧
      selected.input = source.input ∧ selected.output = source.output := by
  exact ⟨_, (step_iff ..).mpr (.captured bindings name head arguments shape captured authorized),
    rfl, rfl, rfl, rfl⟩

def theory (program : Program) : Mettapedia.GSLT.GSLT where
  Term := Configuration
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Transition program
  rewrites_resp_left := by
    intro first other second same transition
    subst other
    exact ⟨second, transition, rfl⟩
  rewrites_resp_right := by
    intro first second other transition same
    subst other
    exact transition

/-- Only terminal controls have observations; unfinished work retains the
entire configuration and is not a logical refusal. -/
def observation (source : Configuration) : Option Outcome :=
  match source.control, source.frames with
  | .returned answers, [] => some (.complete source.state answers source.input source.output)
  | .fault reason, _ => some (.fault reason)
  | _, _ => none

def run (program : Program) : Nat → Configuration → Outcome
  | fuel, source =>
    match observation source with
    | some result => result
    | none =>
      match fuel with
      | 0 => .exhausted source
      | fuel + 1 =>
        match step program source with
        | some selected => run program fuel selected
        | none => .exhausted source

theorem terminal_has_no_step (program : Program) (source : Configuration) (result : Outcome)
    (terminal : observation source = some result) : step program source = none := by
  cases source with
  | mk state control frames input output =>
    cases control <;> cases frames <;> simp [observation] at terminal
    all_goals rfl

theorem run_succ_of_step (program : Program) (source selected : Configuration) (fuel : Nat)
    (transition : step program source = some selected) :
    run program (fuel + 1) source = run program fuel selected := by
  cases seen : observation source with
  | none => simp [run, seen, transition]
  | some result =>
    have stopped := terminal_has_no_step program source result seen
    rw [stopped] at transition
    contradiction

/-- Pausing and resuming preserves exactly the uninterrupted observation,
including order, duplicates, effects and pending work in the saved state. -/
theorem run_resume (program : Program) (first second : Nat) (source residual : Configuration)
    (paused : run program first source = .exhausted residual) :
    run program (first + second) source = run program second residual := by
  induction first generalizing source with
  | zero =>
    cases seen : observation source with
    | none =>
      have same : source = residual := Outcome.exhausted.inj (by simpa [run, seen] using paused)
      subst residual
      simp
    | some result =>
      cases source with
      | mk state control frames input output =>
        cases control <;> cases frames <;> simp [observation] at seen
        all_goals simp [run, observation] at paused
  | succ first ih =>
    cases seen : observation source with
    | some result =>
      cases source with
      | mk state control frames input output =>
        cases control <;> cases frames <;> simp [observation] at seen
        all_goals simp [run, observation] at paused
    | none =>
      cases next : step program source with
      | some selected =>
        have rest : run program first selected = .exhausted residual := by
          simpa [run, seen, next] using paused
        rw [Nat.add_right_comm, run_succ_of_step program source selected (first + second) next]
        exact ih selected rest
      | none =>
        have same : source = residual := Outcome.exhausted.inj (by simpa [run, seen, next] using paused)
        subst residual
        rw [show first + 1 + second = (first + second) + 1 by omega]
        cases second <;> simp only [run, seen, next]

theorem no_exhausted_observation (source : Configuration) (residual : Configuration) :
    observation source ≠ some (.exhausted residual) := by
  cases source with
  | mk state control frames input output =>
    cases control <;> cases frames <;> simp [observation]

theorem observation_complete_iff (source : Configuration) (state : Effects.State)
    (answers input output : List Atom) :
    observation source = some (.complete state answers input output) ↔
      source = finished state answers input output := by
  cases source with
  | mk store control frames pending printed =>
    cases control <;> cases frames <;> simp [observation, finished, Configuration.mk.injEq]

/-- Finite execution constructs paths in the independently specified GSLT.
No host result or guest-checker verdict is supplied as a transition. -/
theorem completed_has_path (program : Program) (fuel : Nat) (source : Configuration)
    (state : Effects.State) (answers input output : List Atom)
    (completed : run program fuel source = .complete state answers input output) :
    (theory program).MultiStep source (finished state answers input output) := by
  induction fuel generalizing source with
  | zero =>
    cases seen : observation source with
    | none => simp [run, seen] at completed
    | some result =>
      have resultEq : result = .complete state answers input output := by simpa [run, seen] using completed
      subst result
      rw [(observation_complete_iff ..).mp seen]
      exact .refl _
  | succ fuel ih =>
    cases seen : observation source with
    | some result =>
      have resultEq : result = .complete state answers input output := by simpa [run, seen] using completed
      subst result
      rw [(observation_complete_iff ..).mp seen]
      exact .refl _
    | none =>
      cases next : step program source with
      | none => simp [run, seen, next] at completed
      | some selected =>
        exact .step ((step_iff ..).mp next) (ih selected (by simpa [run, seen, next] using completed))

theorem path_has_sufficient_fuel (program : Program) {source target : Configuration}
    (path : (theory program).MultiStep source target) (state : Effects.State)
    (answers input output : List Atom) (terminal : target = finished state answers input output) :
    ∃ fuel, run program fuel source = .complete state answers input output := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec (theory program)
    (fun source target _ => target = finished state answers input output →
      ∃ fuel, run program fuel source = .complete state answers input output)
    (fun source terminal => ?_)
    (fun {_ _ _} transition _ ih terminal => ?_) source target path terminal
  · rw [terminal]
    exact ⟨0, rfl⟩
  · obtain ⟨fuel, completed⟩ := ih terminal
    exact ⟨fuel + 1, (run_succ_of_step program _ _ fuel ((step_iff ..).mpr transition)).trans completed⟩

theorem completed_iff_path (program : Program) (source : Configuration)
    (state : Effects.State) (answers input output : List Atom) :
    (∃ fuel, run program fuel source = .complete state answers input output) ↔
      (theory program).MultiStep source (finished state answers input output) :=
  ⟨fun ⟨fuel, completed⟩ => completed_has_path program fuel source state answers input output completed,
    fun path => path_has_sufficient_fuel program path state answers input output rfl⟩

theorem transition_empty_tail {program : Program} {source selected : Configuration}
    (vacant : NamedSpaces.Store.EmptyTail source.state []) (transition : Transition program source selected) :
    NamedSpaces.Store.EmptyTail selected.state [] := by
  cases transition with
  | captured => exact vacant
  | core _ original => exact DeclarativeSpec.transition_empty_tail vacant original

theorem transition_finite_cells {program : Program} {source selected : Configuration}
    (finite : NamedSpaces.Store.FiniteCells source.state) (transition : Transition program source selected) :
    NamedSpaces.Store.FiniteCells selected.state := by
  cases transition with
  | captured => exact finite
  | core _ original => exact DeclarativeSpec.transition_finite_cells finite original

end Mettapedia.Languages.MeTTa.PeTTa.BoundCalls
