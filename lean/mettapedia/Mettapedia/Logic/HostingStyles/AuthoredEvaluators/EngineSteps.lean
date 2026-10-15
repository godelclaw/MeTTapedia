import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ProgramExtension
import Mathlib.Logic.Relation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The equation engine, step by step

The shared equation engine evaluates a term by recursion with fuel
(`DeterministicEquations.eval`), and a call returns a value when some fuel
suffices (`Applies`).  The engine's directory has no small-step form: the
evaluator with fuel is its only semantics.  This module gives one.

* A **configuration** is a control and a stack of frames (`Configuration`).
  The control evaluates a term in an environment, evaluates the items of an
  expression from left to right, applies a head to evaluated arguments, holds
  a value, or has failed.  A frame waits for the value of a `let` or of an
  item.
* `step` is one move of the machine, a function: a configuration has at most
  one successor (`Step.deterministic`), and exactly the configurations that
  hold a value on an empty stack, or have failed, have none
  (`step_eq_none_iff`).
* **A call returns a value exactly when its configuration reaches that
  value** (`applies_iff_reaches`).  A call fails with some fuel exactly when
  its configuration reaches the failed one (`fails_iff_reaches`), and runs
  out of every fuel exactly when its configuration has runs of every length
  (`exhausts_iff_runs`).

## Steps and fuel

Fuel bounds the depth of an evaluation and steps count its size.

* A run of `count` steps to a value is a computation with fuel `count`
  (`apply_of_stepsIn`): the steps bound the fuel.
* A computation with fuel `fuel` is a run of at most
  `stepBound breadth fuel` steps, where `breadth` bounds the number of items
  of the expressions in the bodies of the program (`stepsIn_of_apply`), and
  `stepBound breadth fuel + 6 ≤ 6 * (breadth + 1) ^ fuel` for a positive
  breadth (`stepBound_le`).  The bound is exponential in the fuel: an
  expression of `breadth` items evaluates each of them.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AuthoredEvaluators

open Mettapedia.GSLT.LanguageDef.DeterministicEquations

/-! ## What a term asks of the evaluator -/

/-- What the evaluated items of an expression are for: a list value, the
arguments of a call, or the elements of an expression without a head symbol. -/
inductive ItemsKind where
  | list
  | data
  | call (head : String)

/-- **What a term asks of the evaluator**: nothing (it denotes a value, or
fails), the evaluation of a bound term and then of a body, or the evaluation
of items from left to right. -/
inductive Request where
  | value (result : Term)
  | failure
  | bind (name : String) (bound body : Term)
  | items (kind : ItemsKind) (items : List Term)

/-- The request of a term in an environment, by the cases of the engine's
`evalStep`. -/
def request (environment : Env) : Term → Request
  | .var name =>
    match environment.lookup name with
    | some result => .value result
    | none => .failure
  | .sym name => .value (.sym name)
  | .lit spelling => .value (.lit spelling)
  | .list items => .items .list items
  | .expr [] => .value (.expr [])
  | .expr [.sym "let", .var name, bound, body] => .bind name bound body
  | .expr [.sym "let", _, _, _] => .failure
  | .expr [.sym "metta-nullary", .sym name] => .value (.expr [.sym name])
  | .expr [.sym "metta-nullary", _] => .failure
  | .expr (.sym head :: arguments) => .items (.call head) arguments
  | .expr items => .items .data items

/-- What evaluated items are completed to, with a given evaluation of calls. -/
def completeWith (call : String → List Term → Outcome) : ItemsKind → List Term → Outcome
  | .list, values => .value (.list values)
  | .data, values => .value (.expr values)
  | .call head, values => call head values

/-- The answer to a request, with a given evaluation of terms and of calls. -/
def answerWith (ev : Env → Term → Outcome) (call : String → List Term → Outcome)
    (environment : Env) : Request → Outcome
  | .value result => .value result
  | .failure => .failure
  | .bind name bound body =>
    match ev environment bound with
    | .value result => ev ((name, result) :: environment) body
    | other => other
  | .items kind items =>
    match evalItemsWith ev environment items with
    | .values values => completeWith call kind values
    | .stop other => other

/-- **One step of the engine's evaluation answers the request of the term.** -/
theorem evalStep_eq_answerWith (ev : Env → Term → Outcome)
    (call : String → List Term → Outcome) (environment : Env) (term : Term) :
    evalStep ev call environment term = answerWith ev call environment (request environment term) := by
  unfold evalStep
  split
  · rename_i name
    simp only [request]
    cases environment.lookup name <;> rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rename_i first bound body notVariable
    rw [request.eq_7 environment first bound body notVariable]
    rfl
  · rfl
  · rename_i first notSymbol
    rw [request.eq_9 environment first notSymbol]
    rfl
  · rename_i head arguments first second third fourth
    rw [request.eq_10 environment head arguments first second third fourth]
    rfl
  · rename_i items first second third fourth fifth sixth
    rw [request.eq_11 environment items first second third fourth fifth sixth]
    rfl

theorem eval_succ (program : Program) (host : Host) (fuel : Nat) (environment : Env)
    (term : Term) :
    eval program host (fuel + 1) environment term =
      answerWith (eval program host fuel) (apply program host fuel) environment
        (request environment term) := by
  rw [eval]
  exact evalStep_eq_answerWith _ _ _ _

/-- **Positive**: a call asks for its arguments. -/
theorem request_call (environment : Env) :
    request environment (.expr [.sym "f", .var "x"]) = .items (.call "f") [.var "x"] := rfl

/-- **Negative**: a `let` that does not bind a variable asks for nothing; it
fails. -/
theorem request_let_not_variable (environment : Env) :
    request environment (.expr [.sym "let", .sym "x", .sym "a", .sym "b"]) = .failure := rfl

/-! ## The shapes of requests -/

/-- A request for a body is the request of a `let`. -/
theorem request_bind {environment : Env} {term : Term} {name : String} {bound body : Term}
    (asked : request environment term = .bind name bound body) :
    term = .expr [.sym "let", .var name, bound, body] := by
  unfold request at asked
  split at asked
  · split at asked <;> cases asked
  all_goals first
    | (cases asked; rfl)
    | cases asked

/-- A request for items is the request of a list, of an expression without a
head symbol, or of a call. -/
theorem request_items {environment : Env} {term : Term} {kind : ItemsKind} {items : List Term}
    (asked : request environment term = .items kind items) :
    term = .list items ∨ term = .expr items ∨ ∃ head, term = .expr (.sym head :: items) := by
  unfold request at asked
  split at asked
  · split at asked <;> cases asked
  all_goals first
    | (cases asked; exact .inl rfl)
    | (cases asked; exact .inr (.inl rfl))
    | (cases asked; exact .inr (.inr ⟨_, rfl⟩))
    | cases asked

/-! ## Configurations -/

/-- **A frame**: what waits for a value.  The body of a `let` waits for the
bound value; the items of an expression wait for the item before them. -/
inductive Frame where
  | bind (name : String) (body : Term) (environment : Env)
  | items (kind : ItemsKind) (done : List Term) (rest : List Term) (environment : Env)

/-- **The control of a configuration.**  In `items`, the values of the items
already evaluated are kept in reverse order. -/
inductive Control where
  | eval (environment : Env) (term : Term)
  | items (kind : ItemsKind) (done : List Term) (rest : List Term) (environment : Env)
  | apply (head : String) (arguments : List Term)
  | value (result : Term)
  | failed

/-- **A configuration of the engine**: a control and a stack of frames. -/
structure Configuration where
  control : Control
  stack : List Frame

/-- The configuration of a call on evaluated arguments. -/
def callConfiguration (head : String) (arguments : List Term) : Configuration :=
  ⟨.apply head arguments, []⟩

/-- The configuration that holds a value and waits for nothing. -/
def valueConfiguration (result : Term) : Configuration := ⟨.value result, []⟩

/-- The configuration that has failed. -/
def failedConfiguration : Configuration := ⟨.failed, []⟩

/-- What the evaluated items are handed to. -/
def complete : ItemsKind → List Term → Control
  | .list, values => .value (.list values)
  | .data, values => .value (.expr values)
  | .call head, values => .apply head values

/-- The move of a call on evaluated arguments: the first equation that
matches, a primitive of the host, or a constructor. -/
def dispatch (program : Program) (host : Host) (head : String) (arguments : List Term)
    (stack : List Frame) : Configuration :=
  if program.definesAt head arguments.length then
    match program.select head arguments with
    | some (equation, environment) => ⟨.eval environment equation.body, stack⟩
    | none => failedConfiguration
  else if program.defines head then failedConfiguration
  else
    match host.primitive head arguments with
    | .fault => failedConfiguration
    | .value result => ⟨.value result, stack⟩
    | .unhandled => ⟨.value (.expr (.sym head :: arguments)), stack⟩

/-- **One step of the engine.** -/
def step (program : Program) (host : Host) : Configuration → Option Configuration
  | ⟨.eval environment term, stack⟩ =>
    match request environment term with
    | .value result => some ⟨.value result, stack⟩
    | .failure => some failedConfiguration
    | .bind name bound body =>
        some ⟨.eval environment bound, .bind name body environment :: stack⟩
    | .items kind items => some ⟨.items kind [] items environment, stack⟩
  | ⟨.items kind done [] _, stack⟩ => some ⟨complete kind done.reverse, stack⟩
  | ⟨.items kind done (item :: rest) environment, stack⟩ =>
    some ⟨.eval environment item, .items kind done rest environment :: stack⟩
  | ⟨.apply head arguments, stack⟩ => some (dispatch program host head arguments stack)
  | ⟨.value result, .bind name body environment :: stack⟩ =>
    some ⟨.eval ((name, result) :: environment) body, stack⟩
  | ⟨.value result, .items kind done rest environment :: stack⟩ =>
    some ⟨.items kind (result :: done) rest environment, stack⟩
  | ⟨.value _, []⟩ => none
  | ⟨.failed, _⟩ => none

/-- **The step relation of the engine.** -/
def Step (program : Program) (host : Host) (source target : Configuration) : Prop :=
  step program host source = some target

/-- **A configuration has at most one step.** -/
theorem Step.deterministic {program : Program} {host : Host}
    {source first second : Configuration} (left : Step program host source first)
    (right : Step program host source second) : first = second :=
  Option.some.inj (left.symm.trans right)

/-- A configuration that holds a value and waits for nothing, or has failed. -/
def Terminal (configuration : Configuration) : Prop :=
  (∃ result, configuration = valueConfiguration result) ∨
    ∃ stack, configuration = ⟨.failed, stack⟩

/-- **Positive**: a configuration that holds a value and waits for nothing. -/
theorem terminal_valueConfiguration (result : Term) : Terminal (valueConfiguration result) :=
  .inl ⟨result, rfl⟩

/-- **Negative**: the configuration of a call. -/
theorem not_terminal_callConfiguration (head : String) (arguments : List Term) :
    ¬ Terminal (callConfiguration head arguments) := by
  rintro (⟨result, same⟩ | ⟨stack, same⟩) <;>
    simp [callConfiguration, valueConfiguration] at same

/-- **Exactly the terminal configurations have no step.** -/
theorem step_eq_none_iff (program : Program) (host : Host) (configuration : Configuration) :
    step program host configuration = none ↔ Terminal configuration := by
  obtain ⟨control, stack⟩ := configuration
  constructor
  · intro stuck
    cases control with
    | eval environment term =>
        simp only [step] at stuck
        split at stuck <;> cases stuck
    | items kind done rest environment =>
        cases rest <;> simp [step] at stuck
    | apply head arguments => simp [step] at stuck
    | value result =>
        cases stack with
        | nil => exact .inl ⟨result, rfl⟩
        | cons frame stack => cases frame <;> simp [step] at stuck
    | failed => exact .inr ⟨stack, rfl⟩
  · rintro (⟨result, same⟩ | ⟨other, same⟩)
    · cases same
      rfl
    · cases same
      rfl

/-- Runs of a given number of steps. -/
inductive StepsIn (program : Program) (host : Host) : Nat → Configuration → Configuration → Prop
  | zero (configuration : Configuration) : StepsIn program host 0 configuration configuration
  | succ {count : Nat} {source middle target : Configuration} :
      step program host source = some middle → StepsIn program host count middle target →
      StepsIn program host (count + 1) source target

/-- **A configuration reaches another**: by some number of steps. -/
def Reaches (program : Program) (host : Host) : Configuration → Configuration → Prop :=
  Relation.ReflTransGen (Step program host)

variable {program : Program} {host : Host}

theorem StepsIn.single {source target : Configuration}
    (moved : step program host source = some target) : StepsIn program host 1 source target :=
  .succ moved (.zero _)

theorem StepsIn.trans {first second : Nat} {source middle target : Configuration}
    (left : StepsIn program host first source middle)
    (right : StepsIn program host second middle target) :
    StepsIn program host (first + second) source target := by
  induction left with
  | zero => simpa using right
  | succ moved _ ih =>
      have joined := StepsIn.succ moved (ih right)
      rwa [Nat.add_right_comm] at joined

theorem StepsIn.reaches {count : Nat} {source target : Configuration}
    (steps : StepsIn program host count source target) : Reaches program host source target := by
  induction steps with
  | zero => exact .refl
  | succ moved _ ih => exact Relation.ReflTransGen.head moved ih

theorem reaches_iff_stepsIn {source target : Configuration} :
    Reaches program host source target ↔ ∃ count, StepsIn program host count source target := by
  constructor
  · intro reaches
    induction reaches using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, .zero _⟩
    | head moved _ ih =>
        obtain ⟨count, steps⟩ := ih
        exact ⟨count + 1, .succ moved steps⟩
  · rintro ⟨count, steps⟩
    exact steps.reaches

/-- A terminal configuration is reached by no step. -/
theorem StepsIn.eq_of_terminal {count : Nat} {source target : Configuration}
    (steps : StepsIn program host count source target) (terminal : Terminal source) :
    count = 0 ∧ target = source := by
  cases steps with
  | zero => exact ⟨rfl, rfl⟩
  | succ moved _ =>
      rw [(step_eq_none_iff program host source).mpr terminal] at moved
      cases moved

/-- **Runs are determined**: two runs from one configuration, the shorter to a
terminal configuration, are one run and its beginning. -/
theorem StepsIn.unique {first second : Nat} {source left right : Configuration}
    (short : StepsIn program host first source left) (terminal : Terminal left)
    (long : StepsIn program host second source right) (longer : first ≤ second) :
    second = first ∧ right = left := by
  induction short generalizing second right with
  | zero configuration =>
      obtain ⟨zero, same⟩ := long.eq_of_terminal terminal
      exact ⟨zero, same⟩
  | @succ count source middle target moved _ ih =>
      cases long with
      | zero => omega
      | @succ other _ between _ otherMoved rest =>
          obtain rfl : middle = between := Option.some.inj (moved.symm.trans otherMoved)
          obtain ⟨counted, same⟩ := ih terminal rest (by omega)
          exact ⟨by omega, same⟩

/-! ## What a configuration evaluates to, with fuel -/

variable (program host)

/-- The outcome of a control, with fuel. -/
def controlOutcome (fuel : Nat) : Control → Outcome
  | .eval environment term => eval program host fuel environment term
  | .items kind done rest environment =>
    match evalItemsWith (eval program host fuel) environment rest with
    | .values values => completeWith (apply program host fuel) kind (done.reverse ++ values)
    | .stop other => other
  | .apply head arguments => apply program host fuel head arguments
  | .value result => .value result
  | .failed => .failure

/-- The outcome of a frame that receives a value, with fuel. -/
def frameOutcome (fuel : Nat) : Frame → Term → Outcome
  | .bind name body environment, result =>
    eval program host fuel ((name, result) :: environment) body
  | .items kind done rest environment, result =>
    controlOutcome program host fuel (.items kind (result :: done) rest environment)

/-- The outcome of a stack that receives an outcome, with fuel: a value is
handed down the stack, and any other outcome is the outcome of the stack. -/
def resume (fuel : Nat) : List Frame → Outcome → Outcome
  | [], outcome => outcome
  | frame :: stack, outcome =>
    match outcome with
    | .value result => resume fuel stack (frameOutcome program host fuel frame result)
    | other => other

/-- **The outcome of a configuration, with fuel.** -/
def outcome (fuel : Nat) (configuration : Configuration) : Outcome :=
  resume program host fuel configuration.stack
    (controlOutcome program host fuel configuration.control)

variable {program host}

@[simp] theorem resume_failure (fuel : Nat) (stack : List Frame) :
    resume program host fuel stack .failure = .failure := by
  cases stack <;> rfl

@[simp] theorem resume_exhausted (fuel : Nat) (stack : List Frame) :
    resume program host fuel stack .exhausted = .exhausted := by
  cases stack <;> rfl

@[simp] theorem outcome_valueConfiguration (fuel : Nat) (result : Term) :
    outcome program host fuel (valueConfiguration result) = .value result := rfl

@[simp] theorem outcome_failed (fuel : Nat) (stack : List Frame) :
    outcome program host fuel ⟨.failed, stack⟩ = .failure :=
  resume_failure fuel stack

theorem outcome_callConfiguration (fuel : Nat) (head : String) (arguments : List Term) :
    outcome program host fuel (callConfiguration head arguments) =
      apply program host fuel head arguments := rfl

theorem controlOutcome_complete (fuel : Nat) (kind : ItemsKind) (values : List Term) :
    controlOutcome program host fuel (complete kind values) =
      completeWith (apply program host fuel) kind values := by
  cases kind <;> rfl

theorem refines_trans {first second third : Outcome} (left : Refines first second)
    (right : Refines second third) : Refines first third := by
  rcases left with exhausted | same
  · exact .inl exhausted
  · rcases right with exhausted | other
    · exact .inl (same.trans exhausted)
    · exact .inr (same.trans other)

theorem controlOutcome_refines (fuel : Nat) (control : Control) :
    Refines (controlOutcome program host fuel control)
      (controlOutcome program host (fuel + 1) control) := by
  cases control with
  | eval environment term => exact eval_refines_succ program host fuel environment term
  | items kind done rest environment =>
      simp only [controlOutcome]
      rcases evalItemsWith_refines (eval_refines_succ program host fuel) environment rest with
        same | exhausted
      · rw [← same]
        cases evalItemsWith (eval program host fuel) environment rest with
        | values values =>
            cases kind with
            | list => exact Refines.refl _
            | data => exact Refines.refl _
            | call head =>
                exact applyWith_refines program host (eval_refines_succ program host fuel) head _
        | stop other => exact Refines.refl _
      · rw [exhausted]
        exact .inl rfl
  | apply head arguments =>
      exact applyWith_refines program host (eval_refines_succ program host fuel) head arguments
  | value result => exact Refines.refl _
  | failed => exact Refines.refl _

theorem frameOutcome_refines (fuel : Nat) (frame : Frame) (result : Term) :
    Refines (frameOutcome program host fuel frame result)
      (frameOutcome program host (fuel + 1) frame result) := by
  cases frame with
  | bind name body environment => exact eval_refines_succ program host fuel _ body
  | items kind done rest environment =>
      exact controlOutcome_refines (program := program) (host := host) fuel
        (.items kind (result :: done) rest environment)

theorem resume_refines (fuel : Nat) :
    ∀ (stack : List Frame) {first second : Outcome}, Refines first second →
      Refines (resume program host fuel stack first) (resume program host (fuel + 1) stack second)
  | [], _, _, related => related
  | frame :: stack, first, second, related => by
      rcases related with exhausted | same
      · rw [exhausted]
        exact .inl rfl
      · subst same
        cases first with
        | value result =>
            exact resume_refines fuel stack (frameOutcome_refines fuel frame result)
        | failure => exact Refines.refl _
        | exhausted => exact .inl rfl

/-- **More fuel refines the outcome of a configuration.** -/
theorem outcome_refines_succ (fuel : Nat) (configuration : Configuration) :
    Refines (outcome program host fuel configuration)
      (outcome program host (fuel + 1) configuration) :=
  resume_refines fuel configuration.stack (controlOutcome_refines fuel configuration.control)

/-- **A step costs one unit of fuel at most**: the outcome of the successor
with some fuel is the outcome of the configuration with one unit more. -/
theorem outcome_step {source target : Configuration}
    (moved : step program host source = some target) (fuel : Nat) :
    Refines (outcome program host fuel target) (outcome program host (fuel + 1) source) := by
  obtain ⟨control, stack⟩ := source
  cases control with
  | eval environment term =>
      simp only [step] at moved
      have unfolded : outcome program host (fuel + 1) ⟨.eval environment term, stack⟩ =
          resume program host (fuel + 1) stack
            (answerWith (eval program host fuel) (apply program host fuel) environment
              (request environment term)) := by
        simp only [outcome, controlOutcome, eval_succ]
      rw [unfolded]
      cases asked : request environment term with
      | value result =>
          rw [asked] at moved
          cases moved
          exact resume_refines fuel stack (Refines.refl _)
      | failure =>
          rw [asked] at moved
          cases moved
          simp [answerWith, failedConfiguration]
          exact Refines.refl _
      | bind name bound body =>
          rw [asked] at moved
          cases moved
          simp only [outcome, controlOutcome, answerWith]
          cases eval program host fuel environment bound with
          | value result => exact resume_refines fuel stack (Refines.refl _)
          | failure =>
              simp only [resume, resume_failure]
              exact Refines.refl _
          | exhausted => exact .inl rfl
      | items kind items =>
          rw [asked] at moved
          cases moved
          simp only [outcome, controlOutcome, answerWith, List.reverse_nil, List.nil_append]
          exact resume_refines fuel stack (Refines.refl _)
  | items kind done rest environment =>
      have same : outcome program host fuel target =
          outcome program host fuel ⟨.items kind done rest environment, stack⟩ := by
        cases rest with
        | nil =>
            simp only [step, Option.some.injEq] at moved
            subst moved
            show resume program host fuel stack
                (controlOutcome program host fuel (complete kind done.reverse)) =
              resume program host fuel stack
                (controlOutcome program host fuel (.items kind done [] environment))
            rw [controlOutcome_complete]
            simp only [controlOutcome, evalItemsWith, List.append_nil]
        | cons item rest =>
            simp only [step, Option.some.injEq] at moved
            subst moved
            simp only [outcome, controlOutcome, evalItemsWith, resume]
            cases eval program host fuel environment item with
            | value result =>
                simp only [frameOutcome, controlOutcome, List.reverse_cons, List.append_assoc,
                  List.singleton_append]
                cases evalItemsWith (eval program host fuel) environment rest <;> rfl
            | failure => simp
            | exhausted => simp
      rw [same]
      exact outcome_refines_succ fuel _
  | apply head arguments =>
      have same : outcome program host fuel target =
          outcome program host fuel ⟨.apply head arguments, stack⟩ := by
        simp only [step, Option.some.injEq] at moved
        subst moved
        simp only [outcome, controlOutcome, dispatch, apply, applyWith]
        split
        · cases program.select head arguments with
          | none => simp [failedConfiguration]
          | some selected => rfl
        · split
          · simp [failedConfiguration]
          · cases host.primitive head arguments <;> simp [failedConfiguration]
      rw [same]
      exact outcome_refines_succ fuel _
  | value result =>
      cases stack with
      | nil => cases moved
      | cons frame stack =>
          have same : outcome program host fuel target =
              outcome program host fuel ⟨.value result, frame :: stack⟩ := by
            cases frame with
            | bind name body environment =>
                simp only [step, Option.some.injEq] at moved
                subst moved
                rfl
            | items kind done rest environment =>
                simp only [step, Option.some.injEq] at moved
                subst moved
                rfl
          rw [same]
          exact outcome_refines_succ fuel _
  | failed => cases moved

/-- **A run of some steps costs as many units of fuel at most.** -/
theorem outcome_stepsIn {count : Nat} {source target : Configuration}
    (steps : StepsIn program host count source target) (fuel : Nat) :
    Refines (outcome program host fuel target) (outcome program host (fuel + count) source) := by
  induction steps generalizing fuel with
  | zero => exact Refines.refl _
  | @succ count source middle target moved _ ih =>
      have first := ih fuel
      have second := outcome_step moved (fuel + count)
      rw [Nat.add_assoc] at second
      exact refines_trans first second

/-- **The steps bound the fuel**: a call whose configuration reaches a value
in some number of steps returns that value with as much fuel. -/
theorem apply_of_stepsIn {count : Nat} {head : String} {arguments : List Term} {result : Term}
    (steps : StepsIn program host count (callConfiguration head arguments)
      (valueConfiguration result)) :
    apply program host count head arguments = .value result := by
  have refined := outcome_stepsIn steps 0
  rw [Nat.zero_add, outcome_valueConfiguration, outcome_callConfiguration] at refined
  exact (refined.eq (fun wrong => by cases wrong)).symm

/-- A call whose configuration reaches the failed one fails, with as much
fuel as steps. -/
theorem apply_failure_of_stepsIn {count : Nat} {head : String} {arguments : List Term}
    {stack : List Frame}
    (steps : StepsIn program host count (callConfiguration head arguments) ⟨.failed, stack⟩) :
    apply program host count head arguments = .failure := by
  have refined := outcome_stepsIn steps 0
  rw [Nat.zero_add, outcome_failed, outcome_callConfiguration] at refined
  exact (refined.eq (fun wrong => by cases wrong)).symm

/-! ## The breadth of terms, and the bound on the steps -/

mutual
  /-- **The breadth of a term**: the largest number of items of an expression
  or of a list in it. -/
  def breadth : Term → Nat
    | .sym _ => 0
    | .lit _ => 0
    | .var _ => 0
    | .expr items => max items.length (breadthList items)
    | .list items => max items.length (breadthList items)

  /-- The largest breadth in a list of terms. -/
  def breadthList : List Term → Nat
    | [] => 0
    | term :: terms => max (breadth term) (breadthList terms)
end

theorem breadth_le_breadthList {items : List Term} {item : Term} (member : item ∈ items) :
    breadth item ≤ breadthList items := by
  induction items with
  | nil => cases member
  | cons first rest ih =>
      rw [breadthList]
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_max_left _ _
      · exact (ih later).trans (Nat.le_max_right _ _)

/-- **Positive**: a call on two arguments has breadth three. -/
theorem breadth_call : breadth (.expr [.sym "f", .var "x", .var "y"]) = 3 := by decide

/-- **Negative**: a symbol has no breadth. -/
theorem breadth_symbol (name : String) : breadth (.sym name) = 0 := rfl

/-- The items that a term asks for are fewer than its breadth, and no
broader. -/
theorem request_items_breadth {environment : Env} {term : Term} {kind : ItemsKind}
    {items : List Term} (asked : request environment term = .items kind items) :
    items.length ≤ breadth term ∧ ∀ item ∈ items, breadth item ≤ breadth term := by
  rcases request_items asked with rfl | rfl | ⟨head, rfl⟩
  · exact ⟨by rw [breadth]; exact Nat.le_max_left _ _, fun item member => by
      rw [breadth]
      exact (breadth_le_breadthList member).trans (Nat.le_max_right _ _)⟩
  · exact ⟨by rw [breadth]; exact Nat.le_max_left _ _, fun item member => by
      rw [breadth]
      exact (breadth_le_breadthList member).trans (Nat.le_max_right _ _)⟩
  · refine ⟨?_, fun item member => ?_⟩
    · rw [breadth, List.length_cons]
      exact (Nat.le_succ _).trans (Nat.le_max_left _ _)
    · rw [breadth]
      exact (breadth_le_breadthList (List.mem_cons_of_mem _ member)).trans (Nat.le_max_right _ _)

/-- A `let` has breadth four at least, and its parts are no broader. -/
theorem request_bind_breadth {environment : Env} {term : Term} {name : String}
    {bound body : Term} (asked : request environment term = .bind name bound body) :
    4 ≤ breadth term ∧ breadth bound ≤ breadth term ∧ breadth body ≤ breadth term := by
  obtain rfl := request_bind asked
  refine ⟨?_, ?_, ?_⟩
  · rw [breadth]
    exact Nat.le_max_left _ _
  · rw [breadth]
    exact (breadth_le_breadthList (by simp)).trans (Nat.le_max_right _ _)
  · rw [breadth]
    exact (breadth_le_breadthList (by simp)).trans (Nat.le_max_right _ _)

/-- **The bound on the steps of an evaluation with some fuel**, for terms of
a given breadth. -/
def stepBound (breadth : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 => (breadth + 1) * (stepBound breadth fuel + 2) + 2

/-- **Positive**: with one unit of fuel, a term of breadth two takes eight
steps at most. -/
theorem stepBound_one : stepBound 2 1 = 8 := rfl

/-- **Negative**: no fuel, no step. -/
theorem stepBound_zero (breadth : Nat) : stepBound breadth 0 = 0 := rfl

/-- The bound is exponential in the fuel. -/
theorem stepBound_le {breadth : Nat} (positive : 0 < breadth) :
    ∀ fuel, stepBound breadth fuel + 6 ≤ 6 * (breadth + 1) ^ fuel
  | 0 => by simp [stepBound]
  | fuel + 1 => by
      have previous := stepBound_le positive fuel
      have grown : (breadth + 1) * (stepBound breadth fuel + 6) ≤
          (breadth + 1) * (6 * (breadth + 1) ^ fuel) := Nat.mul_le_mul_left _ previous
      have expanded : (breadth + 1) * (stepBound breadth fuel + 6) =
          (breadth + 1) * (stepBound breadth fuel + 2) + (breadth + 1) * 4 := by ring
      have power : (breadth + 1) * (6 * (breadth + 1) ^ fuel) = 6 * (breadth + 1) ^ (fuel + 1) := by
        ring
      rw [stepBound]
      rw [expanded] at grown
      rw [power] at grown
      have four : 8 ≤ (breadth + 1) * 4 := by omega
      omega

/-- Where an outcome that is not exhaustion leaves the machine. -/
def landing (outcome : Outcome) (stack : List Frame) : Configuration :=
  match outcome with
  | .value result => ⟨.value result, stack⟩
  | _ => failedConfiguration

variable (program host)

/-- An evaluation with some fuel that ends is a run of the machine, within
the bound. -/
def EvalRuns (width fuel : Nat) : Prop :=
  ∀ (environment : Env) (term : Term) (stack : List Frame) (result : Outcome),
    eval program host fuel environment term = result → result ≠ .exhausted →
      breadth term ≤ width →
        ∃ count, count ≤ stepBound width fuel ∧
          StepsIn program host count ⟨.eval environment term, stack⟩ (landing result stack)

/-- A call with some fuel that ends is a run of the machine, within the
bound. -/
def ApplyRuns (width fuel : Nat) : Prop :=
  ∀ (head : String) (arguments : List Term) (stack : List Frame) (result : Outcome),
    apply program host fuel head arguments = result → result ≠ .exhausted →
      ∃ count, count ≤ stepBound width fuel + 1 ∧
        StepsIn program host count ⟨.apply head arguments, stack⟩ (landing result stack)

variable {program host}

theorem applyRuns_of_evalRuns {width fuel : Nat}
    (bodies : ∀ equation ∈ program, breadth equation.body ≤ width)
    (evaluations : EvalRuns program host width fuel) : ApplyRuns program host width fuel := by
  intro head arguments stack result computed ended
  have moved : step program host ⟨.apply head arguments, stack⟩ =
      some (dispatch program host head arguments stack) := rfl
  simp only [apply, applyWith] at computed
  by_cases defined : program.definesAt head arguments.length = true
  · rw [if_pos defined] at computed
    cases selected : program.select head arguments with
    | none =>
        rw [selected] at computed
        subst computed
        refine ⟨1, by omega, ?_⟩
        have target : dispatch program host head arguments stack = landing .failure stack := by
          simp [dispatch, defined, selected, landing]
        exact target ▸ StepsIn.single moved
    | some pair =>
        obtain ⟨equation, environment⟩ := pair
        rw [selected] at computed
        obtain ⟨count, bounded, steps⟩ := evaluations environment equation.body stack result
          computed ended (bodies equation (Program.selected_mem selected))
        have target : dispatch program host head arguments stack =
            ⟨.eval environment equation.body, stack⟩ := by
          simp [dispatch, defined, selected]
        refine ⟨1 + count, by omega, ?_⟩
        exact (StepsIn.single (target ▸ moved)).trans steps
  · rw [if_neg defined] at computed
    by_cases known : program.defines head = true
    · rw [if_pos known] at computed
      subst computed
      refine ⟨1, by omega, ?_⟩
      have target : dispatch program host head arguments stack = landing .failure stack := by
        simp [dispatch, defined, known, landing]
      exact target ▸ StepsIn.single moved
    · rw [if_neg known] at computed
      refine ⟨1, by omega, ?_⟩
      have target : dispatch program host head arguments stack = landing result stack := by
        simp only [dispatch, defined, known]
        cases primitive : host.primitive head arguments with
        | unhandled =>
            rw [primitive] at computed
            subst computed
            rfl
        | fault =>
            rw [primitive] at computed
            subst computed
            rfl
        | value value =>
            rw [primitive] at computed
            subst computed
            rfl
      exact target ▸ StepsIn.single moved

/-- The items of an expression, evaluated with some fuel, are a run of the
machine. -/
theorem itemsRun {width fuel : Nat} (evaluations : EvalRuns program host width fuel)
    (calls : ApplyRuns program host width fuel) (kind : ItemsKind) (environment : Env)
    (stack : List Frame) :
    ∀ (rest done : List Term) (result : Outcome),
      (match evalItemsWith (eval program host fuel) environment rest with
        | .values values => completeWith (apply program host fuel) kind (done.reverse ++ values)
        | .stop other => other) = result →
      result ≠ .exhausted → (∀ item ∈ rest, breadth item ≤ width) →
        ∃ count, count ≤ rest.length * (stepBound width fuel + 2) + (stepBound width fuel + 2) ∧
          StepsIn program host count ⟨.items kind done rest environment, stack⟩
            (landing result stack)
  | [], done, result, computed, ended, _ => by
      have moved : step program host ⟨.items kind done [] environment, stack⟩ =
          some ⟨complete kind done.reverse, stack⟩ := rfl
      simp only [evalItemsWith, List.append_nil] at computed
      cases kind with
      | list =>
          subst computed
          exact ⟨1, by omega, StepsIn.single moved⟩
      | data =>
          subst computed
          exact ⟨1, by omega, StepsIn.single moved⟩
      | call head =>
          obtain ⟨count, bounded, steps⟩ := calls head done.reverse stack result computed ended
          exact ⟨1 + count, by simp only [List.length_nil]; omega, (StepsIn.single moved).trans steps⟩
  | item :: rest, done, result, computed, ended, narrow => by
      have moved : step program host ⟨.items kind done (item :: rest) environment, stack⟩ =
          some ⟨.eval environment item, .items kind done rest environment :: stack⟩ := rfl
      simp only [evalItemsWith] at computed
      cases evaluated : eval program host fuel environment item with
      | value value =>
          rw [evaluated] at computed
          obtain ⟨first, firstBound, firstSteps⟩ := evaluations environment item
            (.items kind done rest environment :: stack) (.value value) evaluated
            (fun wrong => by cases wrong) (narrow item (List.mem_cons_self ..))
          have popped : step program host
              ⟨.value value, .items kind done rest environment :: stack⟩ =
              some ⟨.items kind (value :: done) rest environment, stack⟩ := rfl
          have later : (match evalItemsWith (eval program host fuel) environment rest with
              | .values values =>
                  completeWith (apply program host fuel) kind ((value :: done).reverse ++ values)
              | .stop other => other) = result := by
            rw [← computed]
            cases evalItemsWith (eval program host fuel) environment rest with
            | values values =>
                simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
            | stop other => rfl
          obtain ⟨second, secondBound, secondSteps⟩ := itemsRun evaluations calls kind environment
            stack rest (value :: done) result later ended
            (fun other member => narrow other (List.mem_cons_of_mem _ member))
          refine ⟨1 + first + 1 + second, ?_, ?_⟩
          · simp only [List.length_cons]
            have expanded : (rest.length + 1) * (stepBound width fuel + 2) =
                rest.length * (stepBound width fuel + 2) + (stepBound width fuel + 2) := by ring
            omega
          · exact (((StepsIn.single moved).trans firstSteps).trans (StepsIn.single popped)).trans
              secondSteps
      | failure =>
          rw [evaluated] at computed
          subst computed
          obtain ⟨first, firstBound, firstSteps⟩ := evaluations environment item
            (.items kind done rest environment :: stack) .failure evaluated
            (fun wrong => by cases wrong) (narrow item (List.mem_cons_self ..))
          refine ⟨1 + first, ?_, (StepsIn.single moved).trans firstSteps⟩
          simp only [List.length_cons]
          have expanded : (rest.length + 1) * (stepBound width fuel + 2) =
              rest.length * (stepBound width fuel + 2) + (stepBound width fuel + 2) := by ring
          omega
      | exhausted =>
          rw [evaluated] at computed
          exact absurd computed.symm ended

/-- **An evaluation with some fuel that ends is a run of the machine, within
the bound of its fuel.** -/
theorem evalRuns {width : Nat} (bodies : ∀ equation ∈ program, breadth equation.body ≤ width) :
    ∀ fuel, EvalRuns program host width fuel
  | 0 => by
      intro environment term stack result computed ended
      exact absurd computed.symm ended
  | fuel + 1 => by
      have evaluations := evalRuns bodies fuel
      have calls := applyRuns_of_evalRuns bodies evaluations
      intro environment term stack result computed ended narrow
      rw [eval_succ] at computed
      cases asked : request environment term with
      | value value =>
          rw [asked] at computed
          subst computed
          have moved : step program host ⟨.eval environment term, stack⟩ =
              some ⟨.value value, stack⟩ := by simp only [step, asked]
          exact ⟨1, by rw [stepBound]; nlinarith, StepsIn.single moved⟩
      | failure =>
          rw [asked] at computed
          subst computed
          have moved : step program host ⟨.eval environment term, stack⟩ =
              some failedConfiguration := by simp only [step, asked]
          exact ⟨1, by rw [stepBound]; nlinarith, StepsIn.single moved⟩
      | bind name bound body =>
          rw [asked] at computed
          obtain ⟨wide, boundNarrow, bodyNarrow⟩ := request_bind_breadth asked
          have moved : step program host ⟨.eval environment term, stack⟩ =
              some ⟨.eval environment bound, .bind name body environment :: stack⟩ := by
            simp only [step, asked]
          simp only [answerWith] at computed
          cases evaluated : eval program host fuel environment bound with
          | value value =>
              rw [evaluated] at computed
              obtain ⟨first, firstBound, firstSteps⟩ := evaluations environment bound
                (.bind name body environment :: stack) (.value value) evaluated
                (fun wrong => by cases wrong) (boundNarrow.trans narrow)
              have popped : step program host
                  ⟨.value value, .bind name body environment :: stack⟩ =
                  some ⟨.eval ((name, value) :: environment) body, stack⟩ := rfl
              obtain ⟨second, secondBound, secondSteps⟩ := evaluations
                ((name, value) :: environment) body stack result computed ended
                (bodyNarrow.trans narrow)
              refine ⟨1 + first + 1 + second, ?_, ?_⟩
              · rw [stepBound]
                have four : 4 ≤ width := wide.trans narrow
                nlinarith
              · exact (((StepsIn.single moved).trans firstSteps).trans
                  (StepsIn.single popped)).trans secondSteps
          | failure =>
              rw [evaluated] at computed
              subst computed
              obtain ⟨first, firstBound, firstSteps⟩ := evaluations environment bound
                (.bind name body environment :: stack) .failure evaluated
                (fun wrong => by cases wrong) (boundNarrow.trans narrow)
              refine ⟨1 + first, ?_, (StepsIn.single moved).trans firstSteps⟩
              rw [stepBound]
              nlinarith
          | exhausted =>
              rw [evaluated] at computed
              exact absurd computed.symm ended
      | items kind items =>
          rw [asked] at computed
          obtain ⟨few, itemsNarrow⟩ := request_items_breadth asked
          have moved : step program host ⟨.eval environment term, stack⟩ =
              some ⟨.items kind [] items environment, stack⟩ := by simp only [step, asked]
          have later : (match evalItemsWith (eval program host fuel) environment items with
              | .values values =>
                  completeWith (apply program host fuel) kind (([] : List Term).reverse ++ values)
              | .stop other => other) = result := by
            simpa only [answerWith, List.reverse_nil, List.nil_append] using computed
          obtain ⟨count, bounded, steps⟩ := itemsRun evaluations calls kind environment stack items
            [] result later ended (fun item member => (itemsNarrow item member).trans narrow)
          refine ⟨1 + count, ?_, (StepsIn.single moved).trans steps⟩
          rw [stepBound]
          have short : items.length ≤ width := few.trans narrow
          have scaled : items.length * (stepBound width fuel + 2) ≤
              width * (stepBound width fuel + 2) := Nat.mul_le_mul_right _ short
          have expanded : (width + 1) * (stepBound width fuel + 2) =
              width * (stepBound width fuel + 2) + (stepBound width fuel + 2) := by ring
          omega

/-! ## Calls and runs -/

/-- **The breadth of a program**: the largest breadth of the bodies of its
equations. -/
def Program.breadth (program : Program) : Nat :=
  (program.map fun equation => AuthoredEvaluators.breadth equation.body).foldr max 0

theorem Program.breadth_body {program : Program} {equation : Equation}
    (member : equation ∈ program) :
    AuthoredEvaluators.breadth equation.body ≤ Program.breadth program := by
  unfold Program.breadth
  induction program with
  | nil => cases member
  | cons first rest ih =>
      rw [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.mp member with rfl | later
      · exact Nat.le_max_left _ _
      · exact (ih later).trans (Nat.le_max_right _ _)

/-- **The fuel bounds the steps**: a call that ends with some fuel is a run
of the machine of at most `stepBound breadth fuel + 1` steps, for the breadth
of the program. -/
theorem stepsIn_of_apply {fuel : Nat} {head : String} {arguments : List Term}
    {result : Outcome} (computed : apply program host fuel head arguments = result)
    (ended : result ≠ .exhausted) :
    ∃ count, count ≤ stepBound (Program.breadth program) fuel + 1 ∧
      StepsIn program host count (callConfiguration head arguments) (landing result []) :=
  applyRuns_of_evalRuns (fun _ member => Program.breadth_body member)
    (evalRuns (fun _ member => Program.breadth_body member) fuel) head arguments [] result
    computed ended

/-- **A call returns a value exactly when its configuration reaches that
value.** -/
theorem applies_iff_reaches {head : String} {arguments : List Term} {result : Term} :
    Applies program host head arguments result ↔
      Reaches program host (callConfiguration head arguments) (valueConfiguration result) := by
  constructor
  · rintro ⟨fuel, computed⟩
    obtain ⟨count, -, steps⟩ := stepsIn_of_apply computed (fun wrong => by cases wrong)
    exact steps.reaches
  · intro reaches
    obtain ⟨count, steps⟩ := reaches_iff_stepsIn.mp reaches
    exact ⟨count, apply_of_stepsIn steps⟩

/-- **A call fails with some fuel exactly when its configuration reaches the
failed one.** -/
theorem fails_iff_reaches {head : String} {arguments : List Term} :
    (∃ fuel, apply program host fuel head arguments = .failure) ↔
      Reaches program host (callConfiguration head arguments) failedConfiguration := by
  constructor
  · rintro ⟨fuel, computed⟩
    obtain ⟨count, -, steps⟩ := stepsIn_of_apply computed (fun wrong => by cases wrong)
    exact steps.reaches
  · intro reaches
    obtain ⟨count, steps⟩ := reaches_iff_stepsIn.mp reaches
    exact ⟨count, apply_failure_of_stepsIn steps⟩

/-- A configuration that is not terminal has a step. -/
theorem exists_step_of_not_terminal {configuration : Configuration}
    (running : ¬ Terminal configuration) : ∃ next, step program host configuration = some next := by
  cases moved : step program host configuration with
  | none => exact absurd ((step_eq_none_iff program host configuration).mp moved) running
  | some next => exact ⟨next, rfl⟩

/-- From a configuration with runs of every length, each run is continued. -/
theorem exists_stepsIn_or_terminal (configuration : Configuration) :
    ∀ count, (∃ target, StepsIn program host count configuration target) ∨
      ∃ shorter target, shorter < count ∧ StepsIn program host shorter configuration target ∧
        Terminal target
  | 0 => .inl ⟨configuration, .zero _⟩
  | count + 1 => by
      rcases exists_stepsIn_or_terminal configuration count with ⟨target, steps⟩ |
          ⟨shorter, target, less, steps, terminal⟩
      · by_cases terminal : Terminal target
        · exact .inr ⟨count, target, Nat.lt_succ_self _, steps, terminal⟩
        · obtain ⟨next, moved⟩ := exists_step_of_not_terminal (program := program) (host := host)
            terminal
          exact .inl ⟨next, by simpa using steps.trans (StepsIn.single moved)⟩
      · exact .inr ⟨shorter, target, Nat.lt_succ_of_lt less, steps, terminal⟩

/-- **A call runs out of every fuel exactly when its configuration has runs
of every length.** -/
theorem exhausts_iff_runs {head : String} {arguments : List Term} :
    (∀ fuel, apply program host fuel head arguments = .exhausted) ↔
      ∀ count, ∃ target, StepsIn program host count (callConfiguration head arguments) target := by
  constructor
  · intro exhausts count
    rcases exists_stepsIn_or_terminal (program := program) (host := host)
        (callConfiguration head arguments) count with found | ⟨shorter, target, -, steps, terminal⟩
    · exact found
    · rcases terminal with ⟨result, rfl⟩ | ⟨stack, rfl⟩
      · have computed := apply_of_stepsIn steps
        rw [exhausts shorter] at computed
        cases computed
      · have computed := apply_failure_of_stepsIn steps
        rw [exhausts shorter] at computed
        cases computed
  · intro runs fuel
    by_contra ended
    obtain ⟨count, -, steps⟩ := stepsIn_of_apply (program := program) (host := host)
      (result := apply program host fuel head arguments) rfl ended
    have terminal : Terminal (landing (apply program host fuel head arguments) []) := by
      cases computed : apply program host fuel head arguments with
      | value result => exact .inl ⟨result, rfl⟩
      | failure => exact .inr ⟨[], rfl⟩
      | exhausted => exact absurd computed ended
    obtain ⟨target, longer⟩ := runs (count + 1)
    obtain ⟨wrong, -⟩ := steps.unique terminal longer (Nat.le_succ _)
    omega

/-! ## Examples -/

/-- A program with one equation: `(wrap x) = (Some x)`. -/
def wrapProgram : Program := [⟨"wrap", "wrap", [.var "x"], .expr [.sym "Some", .var "x"]⟩]

/-- The host without primitives. -/
def plainHost : Host := ⟨fun _ _ => .unhandled⟩

/-- **Positive**: the body of its equation has two items. -/
theorem wrapProgram_breadth : Program.breadth wrapProgram = 2 := by decide

/-- **Negative**: the empty program has no body. -/
theorem empty_breadth : Program.breadth [] = 0 := rfl

/-- **Positive**: the call `(wrap a)` runs to `(Some a)` in seven steps: the
equation is selected, the body asks for its item, the item is pushed, read
and popped, the items are completed, and `Some` is a constructor. -/
theorem wrap_steps (argument : Term) :
    StepsIn wrapProgram plainHost 7 (callConfiguration "wrap" [argument])
      (valueConfiguration (.expr [.sym "Some", argument])) :=
  .succ rfl (.succ rfl (.succ rfl (.succ rfl (.succ rfl (.succ rfl (.succ rfl (.zero _)))))))

/-- So fuel seven suffices; the evaluator with fuel needs two. -/
theorem wrap_fuel (argument : Term) :
    apply wrapProgram plainHost 7 "wrap" [argument] = .value (.expr [.sym "Some", argument]) ∧
      apply wrapProgram plainHost 2 "wrap" [argument] = .value (.expr [.sym "Some", argument]) :=
  ⟨apply_of_stepsIn (wrap_steps argument), rfl⟩

/-- **Negative**: the call of `wrap` on two arguments reaches the failed
configuration, in one step, and no value. -/
theorem wrap_wrong_arity (first second : Term) :
    StepsIn wrapProgram plainHost 1 (callConfiguration "wrap" [first, second])
      failedConfiguration ∧
      ∀ result, ¬ Reaches wrapProgram plainHost (callConfiguration "wrap" [first, second])
        (valueConfiguration result) := by
  refine ⟨.succ rfl (.zero _), fun result reaches => ?_⟩
  obtain ⟨fuel, computed⟩ := applies_iff_reaches.mpr reaches
  have failed : apply wrapProgram plainHost fuel "wrap" [first, second] = .failure := rfl
  rw [failed] at computed
  cases computed

/-- A program with one equation that calls itself: `(loop x) = (loop x)`. -/
def loopProgram : Program := [⟨"loop", "loop", [.var "x"], .expr [.sym "loop", .var "x"]⟩]

/-- **Negative**: the call `(loop a)` returns after six steps to itself, so it
has runs of every length and no fuel suffices. -/
theorem loop_steps (argument : Term) :
    StepsIn loopProgram plainHost 6 (callConfiguration "loop" [argument])
      (callConfiguration "loop" [argument]) :=
  .succ rfl (.succ rfl (.succ rfl (.succ rfl (.succ rfl (.succ rfl (.zero _))))))

theorem loop_exhausts (argument : Term) (fuel : Nat) :
    apply loopProgram plainHost fuel "loop" [argument] = .exhausted := by
  refine exhausts_iff_runs.mpr (fun count => ?_) fuel
  have cycles : ∀ rounds : Nat, StepsIn loopProgram plainHost (6 * rounds)
      (callConfiguration "loop" [argument]) (callConfiguration "loop" [argument]) := by
    intro rounds
    induction rounds with
    | zero => exact .zero _
    | succ rounds ih => simpa [Nat.mul_succ] using ih.trans (loop_steps argument)
  have prefixes : ∀ (total : Nat) {source target : Configuration},
      StepsIn loopProgram plainHost total source target → ∀ shorter ≤ total,
        ∃ middle, StepsIn loopProgram plainHost shorter source middle := by
    intro total source target steps
    induction steps with
    | zero configuration =>
        intro shorter short
        obtain rfl : shorter = 0 := by omega
        exact ⟨configuration, .zero _⟩
    | @succ count source middle target moved _ ih =>
        intro shorter short
        cases shorter with
        | zero => exact ⟨source, .zero _⟩
        | succ shorter =>
            obtain ⟨reached, steps⟩ := ih shorter (by omega)
            exact ⟨reached, .succ moved steps⟩
  exact prefixes (6 * count) (cycles count) count (by omega)

#print axioms not_terminal_callConfiguration
#print axioms evalStep_eq_answerWith
#print axioms Step.deterministic
#print axioms step_eq_none_iff
#print axioms StepsIn.unique
#print axioms outcome_step
#print axioms apply_of_stepsIn
#print axioms stepBound_le
#print axioms evalRuns
#print axioms stepsIn_of_apply
#print axioms applies_iff_reaches
#print axioms fails_iff_reaches
#print axioms exhausts_iff_runs
#print axioms wrap_steps
#print axioms wrap_wrong_arity
#print axioms loop_exhausts

end Mettapedia.Logic.HostingStyles.AuthoredEvaluators
