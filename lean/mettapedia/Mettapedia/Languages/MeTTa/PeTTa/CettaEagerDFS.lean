import Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay

/-!
# Eager value binding and depth-first continuation delivery

This additive source model uses the existing PeTTa atoms, program selection,
patterns and primitive table. A returned occurrence resumes its caller before
the next alternative. Bindings and frames belong to each alternative; performed
output, input and the named-space store belong to the whole execution.

`collapse` opens an independent search scope. Its caller remains suspended until
that scope exhausts, then receives one expression containing all inner answer
occurrences in order. The scope boundary does not discard performed effects.

The profile describes CeTTa's eager-value behavior. It does not assert equality
with the existing list-valued evaluator, SWI's static output unification, native
operation registries, native fault-as-value policies or compiled C execution.
External callback latency is outside the transition-count contract.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaEagerDFS

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program Cases)
open Effects (State Fault)

/-- The continuation consumes one value occurrence. -/
inductive Frame where
  | argument (bindings : Subst) (target : Eval.Target)
      (remaining values : List Atom) (index : Nat)
  | bind (bindings : Subst) (pattern body : Atom)
  | select (bindings : Subst) (cases : Cases)
  | branch (bindings : Subst) (yes no : Atom)
  deriving Repr

inductive Control where
  | evaluate (bindings : Subst) (expression : Atom)
  | arguments (bindings : Subst) (target : Eval.Target)
      (remaining values : List Atom) (index : Nat)
  | returned (value : Atom)
  | fault (reason : Fault)
  deriving Repr

structure Branch where
  control : Control
  frames : List Frame := []
  deriving Repr

/-- A scope owns its ordered frontier and its answer collection. `caller`
is absent only for the root scope. -/
structure Scope where
  frontier : List Branch
  collected : List Atom := []
  caller : Option (List Frame) := none
  deriving Repr

/-- These fields are globally threaded, including across failed alternatives.
Neither choice nor collection copies or rolls back this world. -/
structure World where
  state : State
  input : List Atom := []
  output : List Atom := []

structure Configuration where
  world : World
  scopes : List Scope

/-- A local source reduction either replaces the current branch, authorizes
ordered alternatives, enters a delimiter, or delivers a value to that scope. -/
inductive Movement where
  | next (branch : Branch)
  | alternatives (branches : List Branch)
  | collect (bindings : Subst) (expression : Atom) (caller : List Frame)
  | answer (value : Atom)
  deriving Repr

/-- Existing equation selection can only return evaluation controls. This
adapter retains the selected bindings, body and the new scalar continuation. -/
def clauseBranch (frames : List Frame) : Eval.Control → Option Branch
  | .evaluate bindings body => some ⟨.evaluate bindings body, frames⟩
  | _ => none

def equationBranches (program : Program) (head : String) (values : List Atom)
    (frames : List Frame) : List Branch :=
  (Eval.clauses program head values).filterMap (clauseBranch frames)

def returnedBranches (values : List Atom) (frames : List Frame) : List Branch :=
  values.map fun value => ⟨.returned value, frames⟩

def rawArgument (program : Program) (target : Eval.Target) (index : Nat) : Bool :=
  match target with
  | .data => false
  | .function head => Eval.argumentIsRaw program head index

/-- Local execution uses the actual shared source helpers and primitive table.
An alternative does not run recursively inside this operation. -/
def localStep (program : Program) (world : World) (branch : Branch) :
    Option (World × Movement) :=
  let resume := fun control frames => some (world, .next ⟨control, frames⟩)
  let replace := fun control => resume control branch.frames
  let push := fun frame bindings expression =>
    resume (.evaluate bindings expression) (frame :: branch.frames)
  match branch.control with
  | .fault _ => none
  | .arguments _ .data [] values _ => replace (.returned (.expression values))
  | .arguments _ (.function head) [] values _ =>
      if Eval.ioHead head then
        match head, values with
        | "readln!", [] =>
            match world.input with
            | [] => replace (.returned (.symbol "end_of_file"))
            | value :: rest => some ({ world with input := rest },
                .next ⟨.returned value, branch.frames⟩)
        | "println!", [value] => some ({ world with output := world.output ++ [value] },
            .next ⟨.returned (Effects.boolean true), branch.frames⟩)
        | "eval", [code] => replace (.evaluate [] code)
        | _, _ => replace (.fault (.invalidArguments head))
      else if StdLib.known head then
        match StdLib.apply world.state head values with
        | .ok (after, answers) => some ({ world with state := after },
            .alternatives (returnedBranches answers branch.frames))
        | .error reason => replace (.fault reason)
      else some (world, .alternatives (equationBranches program head values branch.frames))
  | .arguments bindings target (first :: rest) values index =>
      let frame := Frame.argument bindings target rest values index
      if rawArgument program target index then
        resume (.returned (applySubst bindings first)) (frame :: branch.frames)
      else push frame bindings first
  | .evaluate bindings expression =>
      match expression with
      | .var _ => replace (.returned (applySubst bindings expression))
      | .symbol _ | .grounded _ => replace (.returned expression)
      | .expression [.symbol "let", pattern, value, body] =>
          push (.bind bindings pattern body) bindings value
      | .expression [.symbol "let*", .expression pairs, body] =>
          match Eval.nestedLets pairs body with
          | some nested => replace (.evaluate bindings nested)
          | none => replace (.fault (.invalidArguments "let*"))
      | .expression [.symbol "case", value, .expression rows] =>
          match Eval.readCases rows with
          | some cases => push (.select bindings cases) bindings value
          | none => replace (.fault (.invalidArguments "case"))
      | .expression [.symbol "if", condition, yes, no] =>
          push (.branch bindings yes no) bindings condition
      | .expression [.symbol "collapse", expression] =>
          some (world, .collect bindings expression branch.frames)
      | .expression [.symbol "superpose", .expression alternatives] =>
          some (world, .alternatives
            (alternatives.map fun expression => ⟨.evaluate bindings expression, branch.frames⟩))
      | .expression [.symbol "empty"] => some (world, .alternatives [])
      | .expression [.symbol "quote", expression] => replace (.returned (applySubst bindings expression))
      | .expression (.symbol head :: arguments) =>
          if Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head) then
            replace (.arguments bindings (.function head) arguments [] 0)
          else replace (.arguments bindings .data (.symbol head :: arguments) [] 0)
      | .expression items => replace (.arguments bindings .data items [] 0)
  | .returned value =>
      match branch.frames with
      | [] => some (world, .answer value)
      | frame :: rest =>
          match frame with
          | .argument bindings target pending values index =>
              resume (.arguments bindings target pending (values ++ [value]) (index + 1)) rest
          | .bind bindings pattern body =>
              match SpaceSemantics.matchBinding bindings pattern value with
              | some bound => resume (.evaluate bound body) rest
              | none => some (world, .alternatives [])
          | .select bindings cases =>
              match SpaceSemantics.selectCase bindings value cases with
              | some (bound, body) => resume (.evaluate bound body) rest
              | none => some (world, .alternatives [])
          | .branch bindings yes no =>
              resume (.evaluate bindings (if value == Effects.boolean true then yes else no)) rest

/-- Install a local reduction at the head of the current scope. Choice puts
the authorized branches before the saved alternatives. -/
def install (world : World) (scope : Scope) (pending : List Branch)
    (parents : List Scope) : Movement → Configuration
  | .next branch => ⟨world, { scope with frontier := branch :: pending } :: parents⟩
  | .alternatives branches => ⟨world, { scope with frontier := branches ++ pending } :: parents⟩
  | .collect bindings expression frames =>
      ⟨world, { frontier := [⟨.evaluate bindings expression, []⟩], caller := some frames } ::
        { scope with frontier := pending } :: parents⟩
  | .answer value =>
      ⟨world, { scope with frontier := pending, collected := scope.collected ++ [value] } :: parents⟩

/-- Only exhaustion of the child scope releases its caller. Parent alternatives
remain saved throughout the complete collection. -/
def finishScope (world : World) (rows : List Atom) (frames : List Frame)
    (parent : Scope) (parents : List Scope) : Configuration :=
  ⟨world, { parent with frontier := ⟨.returned (.expression rows), frames⟩ :: parent.frontier } :: parents⟩

def step (program : Program) (configuration : Configuration) : Option Configuration :=
  match configuration.scopes with
  | [] => none
  | scope :: parents =>
      match scope.frontier with
      | [] =>
          match scope.caller, parents with
          | some frames, parent :: rest =>
              some (finishScope configuration.world scope.collected frames parent rest)
          | _, _ => none
      | branch :: pending =>
          (localStep program configuration.world branch).map fun (world, movement) =>
            install world scope pending parents movement

def start (state : State) (expression : Atom) (input : List Atom := []) : Configuration :=
  ⟨⟨state, input, []⟩, [{ frontier := [⟨.evaluate [] expression, []⟩] }]⟩

def answers (configuration : Configuration) : List Atom :=
  configuration.scopes.getLast? |>.map Scope.collected |>.getD []

def fault (configuration : Configuration) : Option Fault := do
  let scope ← configuration.scopes.head?
  let branch ← scope.frontier.head?
  match branch.control with
  | .fault reason => some reason
  | _ => none

def completed (configuration : Configuration) : Bool :=
  match configuration.scopes with
  | [{ frontier := [], caller := none, .. }] => true
  | _ => false

inductive Outcome where
  | complete (configuration : Configuration)
  | exhausted (configuration : Configuration)
  | fault (reason : Fault) (configuration : Configuration)

def observe (configuration : Configuration) : Outcome :=
  match fault configuration with
  | some reason => .fault reason configuration
  | none => if completed configuration then .complete configuration else .exhausted configuration

/-- Running and retaining configurations are independent recursive clients of
the same transition function. -/
def run (program : Program) : Nat → Configuration → Outcome
  | 0, configuration => observe configuration
  | fuel + 1, configuration =>
      match step program configuration with
      | none => observe configuration
      | some next => run program fuel next

def advance (program : Program) : Nat → Configuration → Configuration
  | 0, configuration => configuration
  | fuel + 1, configuration =>
      match step program configuration with
      | none => configuration
      | some next => advance program fuel next

def chunks (program : Program) : List Nat → Configuration → Configuration
  | [], configuration => configuration
  | fuel :: rest, configuration => chunks program rest (advance program fuel configuration)

/-! ## Independently authored source rules -/

/-- The source rules specify scalar continuation delivery. Primitive and
pattern premises refer to their existing semantic operations, never to either
driver's transition function. -/
inductive LocalTransition (program : Program) : World → Branch → World → Movement → Prop where
  | construct {world bindings values index frames} :
      LocalTransition program world ⟨.arguments bindings .data [] values index, frames⟩
        world (.next ⟨.returned (.expression values), frames⟩)
  | read_end {world bindings index frames} (input : world.input = []) :
      LocalTransition program world ⟨.arguments bindings (.function "readln!") [] [] index, frames⟩
        world (.next ⟨.returned (.symbol "end_of_file"), frames⟩)
  | read_line {world bindings index frames value rest} (input : world.input = value :: rest) :
      LocalTransition program world ⟨.arguments bindings (.function "readln!") [] [] index, frames⟩
        { world with input := rest } (.next ⟨.returned value, frames⟩)
  | print {world bindings index frames value} :
      LocalTransition program world ⟨.arguments bindings (.function "println!") [] [value] index, frames⟩
        { world with output := world.output ++ [value] }
        (.next ⟨.returned (Effects.boolean true), frames⟩)
  | evaluate_code {world bindings index frames code} :
      LocalTransition program world ⟨.arguments bindings (.function "eval") [] [code] index, frames⟩
        world (.next ⟨.evaluate [] code, frames⟩)
  | read_bad {world bindings index frames values} (invalid : values ≠ []) :
      LocalTransition program world ⟨.arguments bindings (.function "readln!") [] values index, frames⟩
        world (.next ⟨.fault (.invalidArguments "readln!"), frames⟩)
  | print_bad {world bindings index frames values} (invalid : ∀ value, values ≠ [value]) :
      LocalTransition program world ⟨.arguments bindings (.function "println!") [] values index, frames⟩
        world (.next ⟨.fault (.invalidArguments "println!"), frames⟩)
  | eval_bad {world bindings index frames values} (invalid : ∀ value, values ≠ [value]) :
      LocalTransition program world ⟨.arguments bindings (.function "eval") [] values index, frames⟩
        world (.next ⟨.fault (.invalidArguments "eval"), frames⟩)
  | primitive {world bindings head index frames values after returns}
      (ordinary : Eval.ioHead head = false) (known : StdLib.known head = true)
      (applied : StdLib.apply world.state head values = .ok (after, returns)) :
      LocalTransition program world ⟨.arguments bindings (.function head) [] values index, frames⟩
        { world with state := after } (.alternatives (returnedBranches returns frames))
  | primitive_fault {world bindings head index frames values reason}
      (ordinary : Eval.ioHead head = false) (known : StdLib.known head = true)
      (applied : StdLib.apply world.state head values = .error reason) :
      LocalTransition program world ⟨.arguments bindings (.function head) [] values index, frames⟩
        world (.next ⟨.fault reason, frames⟩)
  | equations {world bindings head index frames values}
      (ordinary : Eval.ioHead head = false) (unknown : StdLib.known head = false) :
      LocalTransition program world ⟨.arguments bindings (.function head) [] values index, frames⟩
        world (.alternatives (equationBranches program head values frames))
  | raw_argument {world bindings target first rest values index frames}
      (raw : rawArgument program target index = true) :
      LocalTransition program world ⟨.arguments bindings target (first :: rest) values index, frames⟩
        world (.next ⟨.returned (applySubst bindings first),
          .argument bindings target rest values index :: frames⟩)
  | evaluated_argument {world bindings target first rest values index frames}
      (eager : rawArgument program target index = false) :
      LocalTransition program world ⟨.arguments bindings target (first :: rest) values index, frames⟩
        world (.next ⟨.evaluate bindings first, .argument bindings target rest values index :: frames⟩)
  | variable {world bindings name frames} :
      LocalTransition program world ⟨.evaluate bindings (.var name), frames⟩
        world (.next ⟨.returned (applySubst bindings (.var name)), frames⟩)
  | symbol {world bindings name frames} :
      LocalTransition program world ⟨.evaluate bindings (.symbol name), frames⟩
        world (.next ⟨.returned (.symbol name), frames⟩)
  | grounded {world bindings value frames} :
      LocalTransition program world ⟨.evaluate bindings (.grounded value), frames⟩
        world (.next ⟨.returned (.grounded value), frames⟩)
  | let_enter {world bindings pattern value body frames} :
      LocalTransition program world
        ⟨.evaluate bindings (.expression [.symbol "let", pattern, value, body]), frames⟩
        world (.next ⟨.evaluate bindings value, .bind bindings pattern body :: frames⟩)
  | let_star {world bindings pairs body nested frames} (expanded : Eval.nestedLets pairs body = some nested) :
      LocalTransition program world
        ⟨.evaluate bindings (.expression [.symbol "let*", .expression pairs, body]), frames⟩
        world (.next ⟨.evaluate bindings nested, frames⟩)
  | let_star_bad {world bindings pairs body frames} (invalid : Eval.nestedLets pairs body = none) :
      LocalTransition program world
        ⟨.evaluate bindings (.expression [.symbol "let*", .expression pairs, body]), frames⟩
        world (.next ⟨.fault (.invalidArguments "let*"), frames⟩)
  | case_enter {world bindings value rows cases frames} (parsed : Eval.readCases rows = some cases) :
      LocalTransition program world
        ⟨.evaluate bindings (.expression [.symbol "case", value, .expression rows]), frames⟩
        world (.next ⟨.evaluate bindings value, .select bindings cases :: frames⟩)
  | case_bad {world bindings value rows frames} (invalid : Eval.readCases rows = none) :
      LocalTransition program world
        ⟨.evaluate bindings (.expression [.symbol "case", value, .expression rows]), frames⟩
        world (.next ⟨.fault (.invalidArguments "case"), frames⟩)
  | if_enter {world bindings condition yes no frames} :
      LocalTransition program world
        ⟨.evaluate bindings (.expression [.symbol "if", condition, yes, no]), frames⟩
        world (.next ⟨.evaluate bindings condition, .branch bindings yes no :: frames⟩)
  | collapse_enter {world bindings expression frames} :
      LocalTransition program world ⟨.evaluate bindings (.expression [.symbol "collapse", expression]), frames⟩
        world (.collect bindings expression frames)
  | superpose_enter {world bindings alternatives frames} :
      LocalTransition program world
        ⟨.evaluate bindings (.expression [.symbol "superpose", .expression alternatives]), frames⟩
        world (.alternatives
          (alternatives.map fun expression => ⟨.evaluate bindings expression, frames⟩))
  | empty_enter {world bindings frames} :
      LocalTransition program world ⟨.evaluate bindings (.expression [.symbol "empty"]), frames⟩
        world (.alternatives [])
  | quote_enter {world bindings expression frames} :
      LocalTransition program world ⟨.evaluate bindings (.expression [.symbol "quote", expression]), frames⟩
        world (.next ⟨.returned (applySubst bindings expression), frames⟩)
  | call_enter {world bindings head arguments frames}
      (notControl : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false)
      (callable : (Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true) :
      LocalTransition program world ⟨.evaluate bindings (.expression (.symbol head :: arguments)), frames⟩
        world (.next ⟨.arguments bindings (.function head) arguments [] 0, frames⟩)
  | data_enter {world bindings head arguments frames}
      (notControl : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false)
      (uncallable : (Eval.ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false) :
      LocalTransition program world ⟨.evaluate bindings (.expression (.symbol head :: arguments)), frames⟩
        world (.next ⟨.arguments bindings .data (.symbol head :: arguments) [] 0, frames⟩)
  | expression_enter {world bindings items frames}
      (unheaded : ∀ head rest, items ≠ .symbol head :: rest) :
      LocalTransition program world ⟨.evaluate bindings (.expression items), frames⟩
        world (.next ⟨.arguments bindings .data items [] 0, frames⟩)
  | answer {world value} :
      LocalTransition program world ⟨.returned value, []⟩ world (.answer value)
  | argument_return {world value bindings target pending values index rest} :
      LocalTransition program world
        ⟨.returned value, .argument bindings target pending values index :: rest⟩
        world (.next ⟨.arguments bindings target pending (values ++ [value]) (index + 1), rest⟩)
  | bind_return {world value bindings pattern body bound rest}
      (matched : SpaceSemantics.matchBinding bindings pattern value = some bound) :
      LocalTransition program world ⟨.returned value, .bind bindings pattern body :: rest⟩
        world (.next ⟨.evaluate bound body, rest⟩)
  | bind_failure {world value bindings pattern body rest}
      (unmatched : SpaceSemantics.matchBinding bindings pattern value = none) :
      LocalTransition program world ⟨.returned value, .bind bindings pattern body :: rest⟩
        world (.alternatives [])
  | case_return {world value bindings cases bound body rest}
      (selected : SpaceSemantics.selectCase bindings value cases = some (bound, body)) :
      LocalTransition program world ⟨.returned value, .select bindings cases :: rest⟩
        world (.next ⟨.evaluate bound body, rest⟩)
  | case_failure {world value bindings cases rest}
      (unmatched : SpaceSemantics.selectCase bindings value cases = none) :
      LocalTransition program world ⟨.returned value, .select bindings cases :: rest⟩
        world (.alternatives [])
  | if_return {world value bindings yes no rest} :
      LocalTransition program world ⟨.returned value, .branch bindings yes no :: rest⟩
        world (.next ⟨.evaluate bindings (if value == Effects.boolean true then yes else no), rest⟩)

inductive Transition (program : Program) : Configuration → Configuration → Prop where
  | branch {world after scope parents branch pending movement}
      (frontier : scope.frontier = branch :: pending)
      (source : LocalTransition program world branch after movement) :
      Transition program ⟨world, scope :: parents⟩ (install after scope pending parents movement)
  | collapse_return {world rows frames parent parents} :
      Transition program ⟨world, ⟨[], rows, some frames⟩ :: parent :: parents⟩
        (finishScope world rows frames parent parents)

theorem local_transition_step {program : Program} {world after : World}
    {branch : Branch} {movement : Movement}
    (source : LocalTransition program world branch after movement) :
    localStep program world branch = some (after, movement) := by
  cases source
  all_goals try solve | simp_all [localStep, Eval.ioHead]
  case call_enter =>
    simp only [localStep]
    split <;> simp_all [DeclarativeSpec.controlForm] <;> aesop
  case data_enter =>
    simp only [localStep]
    split <;> simp_all [DeclarativeSpec.controlForm]

theorem transition_step {program : Program} {source target : Configuration}
    (transition : Transition program source target) : step program source = some target := by
  cases transition with
  | branch frontier derivation => simp [step, frontier, local_transition_step derivation]
  | collapse_return => rfl

theorem local_step_transition {program : Program} {world after : World}
    {branch : Branch} {movement : Movement}
    (computed : localStep program world branch = some (after, movement)) :
    LocalTransition program world branch after movement := by
  cases branch with
  | mk control frames =>
      cases control with
      | fault reason => simp [localStep] at computed
      | arguments bindings target pending values index =>
          cases pending with
          | nil =>
              cases target with
              | data =>
                  simp only [localStep, Option.some.injEq, Prod.mk.injEq] at computed
                  rcases computed with ⟨rfl, rfl⟩
                  exact .construct
              | function head =>
                  simp only [localStep] at computed
                  split at computed
                  · rename_i isIO
                    simp [Eval.ioHead] at isIO
                    rcases isIO with read | print | evaluate
                    · subst head
                      cases values with
                      | nil =>
                          cases input : world.input with
                          | nil =>
                              simp only [input, Option.some.injEq, Prod.mk.injEq] at computed
                              rcases computed with ⟨rfl, rfl⟩
                              exact .read_end input
                          | cons value rest =>
                              simp only [input, Option.some.injEq, Prod.mk.injEq] at computed
                              rcases computed with ⟨rfl, rfl⟩
                              exact .read_line input
                      | cons value rest =>
                          simp at computed
                          rcases computed with ⟨rfl, rfl⟩
                          exact .read_bad (by simp)
                    · subst head
                      cases values with
                      | nil =>
                          simp at computed
                          rcases computed with ⟨rfl, rfl⟩
                          exact .print_bad (by simp)
                      | cons value rest =>
                          cases rest with
                          | nil =>
                              simp only [Option.some.injEq, Prod.mk.injEq] at computed
                              rcases computed with ⟨rfl, rfl⟩
                              exact .print
                          | cons next remaining =>
                              simp at computed
                              rcases computed with ⟨rfl, rfl⟩
                              exact .print_bad (by simp)
                    · subst head
                      cases values with
                      | nil =>
                          simp at computed
                          rcases computed with ⟨rfl, rfl⟩
                          exact .eval_bad (by simp)
                      | cons value rest =>
                          cases rest with
                          | nil =>
                              simp only [Option.some.injEq, Prod.mk.injEq] at computed
                              rcases computed with ⟨rfl, rfl⟩
                              exact .evaluate_code
                          | cons next remaining =>
                              simp at computed
                              rcases computed with ⟨rfl, rfl⟩
                              exact .eval_bad (by simp)
                  · rename_i notIO
                    split at computed
                    · rename_i known
                      cases applied : StdLib.apply world.state head values with
                      | error reason =>
                          simp only [applied, Option.some.injEq, Prod.mk.injEq] at computed
                          rcases computed with ⟨rfl, rfl⟩
                          exact .primitive_fault (Bool.eq_false_iff.mpr notIO) known applied
                      | ok result =>
                          rcases result with ⟨state, returns⟩
                          simp only [applied, Option.some.injEq, Prod.mk.injEq] at computed
                          rcases computed with ⟨rfl, rfl⟩
                          exact .primitive (Bool.eq_false_iff.mpr notIO) known applied
                    · rename_i unknown
                      simp only [Option.some.injEq, Prod.mk.injEq] at computed
                      rcases computed with ⟨rfl, rfl⟩
                      exact .equations (Bool.eq_false_iff.mpr notIO) (Bool.eq_false_iff.mpr unknown)
          | cons first rest =>
              simp only [localStep] at computed
              split at computed
              · rename_i raw
                simp only [Option.some.injEq, Prod.mk.injEq] at computed
                rcases computed with ⟨rfl, rfl⟩
                exact .raw_argument raw
              · rename_i eager
                simp only [Option.some.injEq, Prod.mk.injEq] at computed
                rcases computed with ⟨rfl, rfl⟩
                exact .evaluated_argument (Bool.eq_false_iff.mpr eager)
      | evaluate bindings expression =>
          simp only [localStep] at computed
          split at computed
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .variable
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .symbol
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .grounded
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .let_enter
          · split at computed
            · rcases Option.some.inj computed with ⟨rfl, rfl⟩
              exact .let_star (by assumption)
            · rcases Option.some.inj computed with ⟨rfl, rfl⟩
              exact .let_star_bad (by assumption)
          · split at computed
            · rcases Option.some.inj computed with ⟨rfl, rfl⟩
              exact .case_enter (by assumption)
            · rcases Option.some.inj computed with ⟨rfl, rfl⟩
              exact .case_bad (by assumption)
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .if_enter
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .collapse_enter
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .superpose_enter
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .empty_enter
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            exact .quote_enter
          · split at computed
            · rcases Option.some.inj computed with ⟨rfl, rfl⟩
              apply LocalTransition.call_enter _ (by assumption)
              simp only [DeclarativeSpec.controlForm]
              split <;> simp_all
            · rename_i uncallable
              rcases Option.some.inj computed with ⟨rfl, rfl⟩
              apply LocalTransition.data_enter _ (Bool.eq_false_iff.mpr uncallable)
              simp only [DeclarativeSpec.controlForm]
              split <;> simp_all
          · rcases Option.some.inj computed with ⟨rfl, rfl⟩
            apply LocalTransition.expression_enter
            aesop
      | returned value =>
          cases frames with
          | nil =>
              simp only [localStep, Option.some.injEq, Prod.mk.injEq] at computed
              rcases computed with ⟨rfl, rfl⟩
              exact .answer
          | cons frame rest =>
              cases frame with
              | argument bindings target pending values index =>
                  simp only [localStep, Option.some.injEq, Prod.mk.injEq] at computed
                  rcases computed with ⟨rfl, rfl⟩
                  exact .argument_return
              | bind bindings pattern body =>
                  simp only [localStep] at computed
                  split at computed
                  · simp only [Option.some.injEq, Prod.mk.injEq] at computed
                    rcases computed with ⟨rfl, rfl⟩
                    exact .bind_return (by assumption)
                  · simp only [Option.some.injEq, Prod.mk.injEq] at computed
                    rcases computed with ⟨rfl, rfl⟩
                    exact .bind_failure (by assumption)
              | select bindings cases =>
                  simp only [localStep] at computed
                  split at computed
                  · simp only [Option.some.injEq, Prod.mk.injEq] at computed
                    rcases computed with ⟨rfl, rfl⟩
                    exact .case_return (by assumption)
                  · simp only [Option.some.injEq, Prod.mk.injEq] at computed
                    rcases computed with ⟨rfl, rfl⟩
                    exact .case_failure (by assumption)
              | branch bindings yes no =>
                  simp only [localStep, Option.some.injEq, Prod.mk.injEq] at computed
                  rcases computed with ⟨rfl, rfl⟩
                  exact .if_return

theorem step_transition {program : Program} {source target : Configuration}
    (computed : step program source = some target) : Transition program source target := by
  cases source with
  | mk world scopes =>
      cases scopes with
      | nil => simp [step] at computed
      | cons scope parents =>
          cases frontier : scope.frontier with
          | nil =>
              cases caller : scope.caller with
              | none => simp [step, frontier, caller] at computed
              | some frames =>
                  cases parents with
                  | nil => simp [step, frontier, caller] at computed
                  | cons parent rest =>
                      simp only [step, frontier, caller, Option.some.injEq] at computed
                      subst target
                      cases scope with
                      | mk work collected continuation =>
                          simp only at frontier caller
                          subst work
                          subst continuation
                          exact .collapse_return
          | cons branch pending =>
              simp only [step, frontier] at computed
              cases reduced : localStep program world branch with
              | none => simp [reduced] at computed
              | some result =>
                  rcases result with ⟨after, movement⟩
                  simp only [reduced, Option.map_some, Option.some.injEq] at computed
                  subst target
                  exact .branch frontier (local_step_transition reduced)

theorem step_iff_transition (program : Program) (source target : Configuration) :
    step program source = some target ↔ Transition program source target :=
  ⟨step_transition, transition_step⟩

/-! ## Exact finite execution and resumption -/

theorem transition_deterministic {program : Program} {source first second : Configuration}
    (left : Transition program source first) (right : Transition program source second) :
    first = second :=
  Option.some.inj ((transition_step left).symm.trans (transition_step right))

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

@[simp] theorem theory_step_iff (program : Program) (source target : Configuration) :
    (theory program).Step source target ↔ step program source = some target :=
  (step_iff_transition program source target).symm

theorem advance_stopped (program : Program) (fuel : Nat) (configuration : Configuration)
    (stopped : step program configuration = none) :
    advance program fuel configuration = configuration := by
  cases fuel <;> simp [advance, stopped]

theorem run_stopped (program : Program) (fuel : Nat) (configuration : Configuration)
    (stopped : step program configuration = none) :
    run program fuel configuration = observe configuration := by
  cases fuel <;> simp [run, stopped]

theorem run_advance (program : Program) (fuel : Nat) (configuration : Configuration) :
    run program 0 (advance program fuel configuration) = run program fuel configuration := by
  induction fuel generalizing configuration with
  | zero => rfl
  | succ fuel ih =>
      cases next : step program configuration with
      | none => simp [run, advance, next]
      | some target => simpa only [advance, run, next] using ih target

theorem advance_split (program : Program) (first second : Nat) (configuration : Configuration) :
    advance program second (advance program first configuration) =
      advance program (first + second) configuration := by
  induction first generalizing configuration with
  | zero => simp [advance]
  | succ first ih =>
      cases next : step program configuration with
      | none =>
          rw [advance_stopped program (first + 1) configuration next,
            advance_stopped program second configuration next,
            advance_stopped program (first + 1 + second) configuration next]
      | some target => simpa [advance, next, Nat.succ_add] using ih target

theorem chunks_eq_advance_sum (program : Program) (fuels : List Nat) (configuration : Configuration) :
    chunks program fuels configuration = advance program fuels.sum configuration := by
  induction fuels generalizing configuration with
  | nil => rfl
  | cons fuel rest ih =>
      rw [chunks, ih, advance_split]
      rfl

theorem advance_path (program : Program) (fuel : Nat) (configuration : Configuration) :
    (theory program).MultiStep configuration (advance program fuel configuration) := by
  induction fuel generalizing configuration with
  | zero => exact .refl _
  | succ fuel ih =>
      cases next : step program configuration with
      | none =>
          simp only [advance, next]
          exact .refl _
      | some target =>
          exact .step (step_transition next) (by simpa [advance, next] using ih target)

/-- An exact source execution counts applications of the independently
authored rules. Completion and unused allowance do not manufacture steps. -/
inductive SourceRun (program : Program) : Nat → Configuration → Configuration → Prop where
  | refl (configuration) : SourceRun program 0 configuration configuration
  | next {source intermediate target count}
      (first : Transition program source intermediate)
      (rest : SourceRun program count intermediate target) :
      SourceRun program (count + 1) source target

theorem source_run_advances {program : Program} {count : Nat} {source target : Configuration}
    (sourceRun : SourceRun program count source target) : advance program count source = target := by
  induction sourceRun with
  | refl => rfl
  | next first _ ih => simpa [advance, transition_step first] using ih

theorem advance_has_source_run (program : Program) (fuel : Nat) (configuration : Configuration) :
    ∃ count ≤ fuel, SourceRun program count configuration (advance program fuel configuration) := by
  induction fuel generalizing configuration with
  | zero => exact ⟨0, Nat.le_refl 0, .refl _⟩
  | succ fuel ih =>
      cases next : step program configuration with
      | none =>
          exact ⟨0, Nat.zero_le _, by simpa [advance, next] using SourceRun.refl configuration⟩
      | some target =>
          obtain ⟨count, bound, path⟩ := ih target
          exact ⟨count + 1, Nat.succ_le_succ bound,
            by simpa [advance, next] using SourceRun.next (step_transition next) path⟩

theorem stopped_of_fault (program : Program) (configuration : Configuration) (reason : Fault)
    (isFault : fault configuration = some reason) : step program configuration = none := by
  cases configuration with
  | mk world scopes =>
      cases scopes with
      | nil => simp [fault] at isFault
      | cons scope parents =>
          cases scope with
          | mk frontier collected caller =>
              cases frontier with
              | nil => simp [fault] at isFault
              | cons branch pending =>
                  cases branch with
                  | mk control frames =>
                      cases control <;> simp_all [fault, step, localStep]

theorem stopped_of_completed (program : Program) (configuration : Configuration)
    (isComplete : completed configuration = true) : step program configuration = none := by
  cases configuration with
  | mk world scopes =>
      cases scopes with
      | nil => simp [completed] at isComplete
      | cons scope parents =>
          cases scope with
          | mk frontier collected caller =>
              cases frontier <;> cases caller <;> cases parents <;>
                simp_all [completed, step]

def resume (program : Program) (fuel : Nat) : Outcome → Outcome
  | .exhausted configuration => run program fuel configuration
  | outcome => outcome

theorem resume_observe (program : Program) (fuel : Nat) (configuration : Configuration) :
    resume program fuel (observe configuration) = run program fuel configuration := by
  cases isFault : fault configuration with
  | some reason =>
      rw [run_stopped program fuel configuration (stopped_of_fault program configuration reason isFault)]
      simp [observe, isFault, resume]
  | none =>
      cases isComplete : completed configuration with
      | false => simp [observe, isFault, isComplete, resume]
      | true =>
          rw [run_stopped program fuel configuration (stopped_of_completed program configuration isComplete)]
          simp [observe, isFault, isComplete, resume]

theorem resume_run (program : Program) (first second : Nat) (configuration : Configuration) :
    resume program second (run program first configuration) =
      run program (first + second) configuration := by
  rw [← run_advance program first configuration]
  change resume program second (observe (advance program first configuration)) = _
  rw [resume_observe, ← run_advance program second, advance_split, run_advance]

def checkpoints (program : Program) : List Nat → Configuration → List Configuration
  | [], _ => []
  | fuel :: rest, configuration =>
      let reached := advance program fuel configuration
      reached :: checkpoints program rest reached

def resumeChunks (program : Program) : List Nat → Outcome → Outcome
  | [], outcome => outcome
  | fuel :: rest, outcome => resumeChunks program rest (resume program fuel outcome)

theorem resumeChunks_run (program : Program) (fuels : List Nat) (paid : Nat)
    (configuration : Configuration) :
    resumeChunks program fuels (run program paid configuration) =
      run program (paid + fuels.sum) configuration := by
  induction fuels generalizing paid with
  | nil => simp [resumeChunks]
  | cons fuel rest ih =>
      rw [resumeChunks, resume_run, ih]
      simp [Nat.add_assoc]

theorem chunks_readout (program : Program) (fuels : List Nat) (configuration : Configuration) :
    run program 0 (chunks program fuels configuration) =
      resumeChunks program fuels (run program 0 configuration) := by
  rw [chunks_eq_advance_sum, run_advance, resumeChunks_run, Nat.zero_add]

/-! ## Retained scopes and performed effects -/

inductive ScopesValid : List Scope → Prop where
  | root (work rows) : ScopesValid [⟨work, rows, none⟩]
  | nested {parents} (work rows frames) (valid : ScopesValid parents) :
      ScopesValid (⟨work, rows, some frames⟩ :: parents)

theorem start_scopes_valid (state : State) (expression : Atom) (input : List Atom) :
    ScopesValid (start state expression input).scopes := .root _ _

theorem ScopesValid.nonempty {scopes : List Scope} (valid : ScopesValid scopes) : scopes ≠ [] := by
  cases valid <;> simp

theorem ScopesValid.replace_head {scope : Scope} {parents : List Scope}
    (valid : ScopesValid (scope :: parents)) (work : List Branch) (rows : List Atom) :
    ScopesValid ({ scope with frontier := work, collected := rows } :: parents) := by
  cases valid with
  | root => exact .root _ _
  | nested _ _ _ parentValid => exact .nested _ _ _ parentValid

theorem transition_scopes_valid {program : Program} {source target : Configuration}
    (transition : Transition program source target) (valid : ScopesValid source.scopes) :
    ScopesValid target.scopes := by
  cases transition with
  | branch frontier derivation =>
      cases derivation <;> simp only [install]
      all_goals try exact valid.replace_head _ _
      exact .nested _ _ _ (valid.replace_head _ _)
  | collapse_return =>
      cases valid with
      | nested _ _ _ parentValid => exact parentValid.replace_head _ _

theorem advance_scopes_valid (program : Program) (fuel : Nat) (configuration : Configuration)
    (valid : ScopesValid configuration.scopes) : ScopesValid (advance program fuel configuration).scopes := by
  induction fuel generalizing configuration with
  | zero => exact valid
  | succ fuel ih =>
      cases next : step program configuration with
      | none => simpa [advance, next] using valid
      | some target =>
          simpa [advance, next] using ih target (transition_scopes_valid (step_transition next) valid)

theorem local_output_extension {program : Program} {world after : World} {branch : Branch}
    {movement : Movement} (transition : LocalTransition program world branch after movement) :
    ∃ suffix, after.output = world.output ++ suffix := by
  cases transition
  all_goals try exact ⟨[], (List.append_nil _).symm⟩
  exact ⟨[_], rfl⟩

theorem transition_output_extension {program : Program} {source target : Configuration}
    (transition : Transition program source target) :
    ∃ suffix, target.world.output = source.world.output ++ suffix := by
  cases transition with
  | branch frontier derivation =>
      obtain ⟨suffix, appended⟩ := local_output_extension derivation
      cases derivation <;> exact ⟨suffix, appended⟩
  | collapse_return => exact ⟨[], (List.append_nil _).symm⟩

theorem advance_output_extension (program : Program) (fuel : Nat) (configuration : Configuration) :
    ∃ suffix, (advance program fuel configuration).world.output = configuration.world.output ++ suffix := by
  induction fuel generalizing configuration with
  | zero => exact ⟨[], (List.append_nil _).symm⟩
  | succ fuel ih =>
      cases next : step program configuration with
      | none => exact ⟨[], by simp [advance, next]⟩
      | some target =>
          obtain ⟨first, appended⟩ := transition_output_extension (step_transition next)
          obtain ⟨rest, later⟩ := ih target
          exact ⟨first ++ rest, by simpa [advance, next, appended, List.append_assoc] using later⟩

theorem local_input_suffix {program : Program} {world after : World} {branch : Branch}
    {movement : Movement} (transition : LocalTransition program world branch after movement) :
    ∃ consumed, world.input = consumed ++ after.input := by
  cases transition
  all_goals try exact ⟨[], rfl⟩
  rename_i value rest input
  exact ⟨[value], input⟩

theorem transition_input_suffix {program : Program} {source target : Configuration}
    (transition : Transition program source target) :
    ∃ consumed, source.world.input = consumed ++ target.world.input := by
  cases transition with
  | branch frontier derivation =>
      obtain ⟨consumed, retained⟩ := local_input_suffix derivation
      cases derivation <;> exact ⟨consumed, retained⟩
  | collapse_return => exact ⟨[], rfl⟩

theorem advance_input_suffix (program : Program) (fuel : Nat) (configuration : Configuration) :
    ∃ consumed, configuration.world.input = consumed ++ (advance program fuel configuration).world.input := by
  induction fuel generalizing configuration with
  | zero => exact ⟨[], rfl⟩
  | succ fuel ih =>
      cases next : step program configuration with
      | none => exact ⟨[], by simp [advance, next]⟩
      | some target =>
          obtain ⟨first, consumed⟩ := transition_input_suffix (step_transition next)
          obtain ⟨rest, retained⟩ := ih target
          exact ⟨first ++ rest, by simpa [advance, next, retained, List.append_assoc] using consumed⟩

/-! ## Equation occurrence retention and pending code support -/

/-- This embedding records a scalar control in the existing control datatype.
It makes no claim that list-valued and scalar continuation execution agree. -/
def controlImage : Control → Eval.Control
  | .evaluate bindings expression => .evaluate bindings expression
  | .arguments bindings target remaining values index =>
      .arguments bindings target remaining values index
  | .returned value => .returned [value]
  | .fault reason => .fault reason

theorem selected_clause_shape (program : Program) (head : String) (values : List Atom)
    {control : Eval.Control} (member : control ∈ Eval.clauses program head values) :
    ∃ bindings body, control = .evaluate bindings body := by
  unfold Eval.clauses at member
  obtain ⟨equation, _, selected⟩ := List.mem_filterMap.mp member
  split at selected
  · cases matched : SpaceSemantics.matchValue [] (.expression equation.arguments) (.expression values) with
    | none => simp [matched] at selected
    | some bindings =>
        simp only [matched, Option.map_some, Option.some.injEq] at selected
        exact ⟨bindings, equation.body, selected.symm⟩
  · contradiction

theorem clause_occurrences_recovered (program : Program) (head : String) (values : List Atom)
    (frames : List Frame) :
    (equationBranches program head values frames).map (fun branch => controlImage branch.control) =
      Eval.clauses program head values := by
  have recover : ∀ controls : List Eval.Control,
      (∀ control ∈ controls, ∃ bindings body, control = .evaluate bindings body) →
      (controls.filterMap (clauseBranch frames)).map (fun branch => controlImage branch.control) = controls := by
    intro controls
    induction controls with
    | nil => intro _; rfl
    | cons control rest ih =>
        intro shapes
        obtain ⟨bindings, body, rfl⟩ := shapes control (by simp)
        have tail := ih (fun item member => shapes item (List.mem_cons_of_mem _ member))
        simpa only [List.filterMap_cons, clauseBranch, List.map_cons, controlImage] using
          congrArg (List.cons (.evaluate bindings body)) tail
  exact recover _ (fun control member => selected_clause_shape program head values member)

theorem equation_branches_length (program : Program) (head : String) (values : List Atom)
    (frames : List Frame) :
    (equationBranches program head values frames).length = (Eval.clauses program head values).length := by
  simpa using congrArg List.length (clause_occurrences_recovered program head values frames)

def controlWithin (allowed : String → Bool) (control : Control) : Bool :=
  Eval.controlWithin allowed (controlImage control)

def frameWithin (allowed : String → Bool) : Frame → Bool
  | .argument _ target pending _ _ => Eval.targetWithin allowed target && Eval.atomsWithin allowed pending
  | .bind _ _ body => Eval.codeWithin allowed body
  | .select _ cases => cases.all (fun row => Eval.codeWithin allowed row.2)
  | .branch _ yes no => Eval.codeWithin allowed yes && Eval.codeWithin allowed no

def branchWithin (allowed : String → Bool) (branch : Branch) : Bool :=
  controlWithin allowed branch.control && branch.frames.all (frameWithin allowed)

def scopeWithin (allowed : String → Bool) (scope : Scope) : Bool :=
  scope.frontier.all (branchWithin allowed) &&
    (scope.caller.map (fun frames => frames.all (frameWithin allowed))).getD true

def configurationWithin (allowed : String → Bool) (configuration : Configuration) : Prop :=
  configuration.scopes.all (scopeWithin allowed) = true

def movementWithin (allowed : String → Bool) : Movement → Bool
  | .next branch => branchWithin allowed branch
  | .alternatives branches => branches.all (branchWithin allowed)
  | .collect _ expression frames =>
      Eval.codeWithin allowed expression && frames.all (frameWithin allowed)
  | .answer _ => true

theorem equation_branches_within {allowed : String → Bool} {program : Program} {head : String}
    (closed : Eval.ProgramClosed allowed program) (supported : allowed head = true)
    (values : List Atom) (frames : List Frame) (frameCodes : frames.all (frameWithin allowed) = true) :
    (equationBranches program head values frames).all (branchWithin allowed) = true := by
  rw [List.all_eq_true]
  intro branch member
  obtain ⟨control, controlMember, mapped⟩ := List.mem_filterMap.mp member
  obtain ⟨bindings, body, shape⟩ := selected_clause_shape program head values controlMember
  subst control
  simp only [clauseBranch, Option.some.injEq] at mapped
  subst branch
  have codes : (Eval.clauses program head values).all (Eval.controlWithin allowed) = true := by
    simpa only [Eval.controlsWithin_eq_all] using Eval.clauses_within allowed closed supported values
  have code := List.all_eq_true.mp codes (Eval.Control.evaluate bindings body) controlMember
  simp only [branchWithin, Bool.and_eq_true]
  exact ⟨code, frameCodes⟩

theorem local_transition_within {allowed : String → Bool} {program : Program}
    {world after : World} {branch : Branch} {movement : Movement}
    (closed : Eval.ProgramClosed allowed program)
    (transition : LocalTransition program world branch after movement)
    (within : branchWithin allowed branch = true) : movementWithin allowed movement = true := by
  cases transition
  all_goals try solve |
    simp_all [movementWithin, branchWithin, controlWithin, controlImage, frameWithin,
      Eval.controlWithin, Eval.targetWithin, Eval.codeWithin,
      Eval.atomsWithin, Eval.expressionHeadWithin, Bool.and_eq_true, returnedBranches,
      List.all_map]
  case equations bindings head index frames values _ _ =>
    simp only [branchWithin, controlWithin, controlImage, Eval.controlWithin,
      Eval.targetWithin, Eval.atomsWithin, Bool.and_true, Bool.and_eq_true] at within
    exact equation_branches_within closed within.1.1 values frames within.2
  case let_star bindings pairs body nested frames expanded =>
    simp only [movementWithin, branchWithin, controlWithin, controlImage, Eval.controlWithin,
      Bool.and_eq_true]
    refine ⟨Eval.nestedLets_within allowed closed.binding expanded ?_ ?_, ?_⟩
    all_goals simp_all [branchWithin, controlWithin, controlImage, Eval.controlWithin,
      Eval.codeWithin, Eval.atomsWithin, Eval.expressionHeadWithin, Bool.and_eq_true]
  case case_enter bindings value rows cases frames parsed =>
    simp only [movementWithin, branchWithin, controlWithin, controlImage, Eval.controlWithin,
      List.all_cons, frameWithin, Bool.and_eq_true]
    refine ⟨?_, Eval.readCases_within allowed parsed ?_, ?_⟩
    all_goals simp_all [branchWithin, controlWithin, controlImage, Eval.controlWithin,
      Eval.codeWithin, Eval.atomsWithin, Eval.expressionHeadWithin, Bool.and_eq_true]
  case case_return value bindings cases rest bound body selected =>
    simp only [branchWithin, controlWithin, controlImage, Eval.controlWithin, Bool.true_and,
      List.all_cons, frameWithin, Bool.and_eq_true] at within
    simp only [movementWithin, branchWithin, controlWithin, controlImage, Eval.controlWithin,
      Bool.and_eq_true]
    exact ⟨Eval.selected_body_within allowed (SpaceSemantics.selectCase_sound selected) within.1, within.2⟩
  case if_return value bindings yes no rest =>
    simp only [branchWithin, controlWithin, controlImage, Eval.controlWithin, Bool.true_and,
      List.all_cons, frameWithin, Bool.and_eq_true] at within
    simp only [movementWithin, branchWithin, controlWithin, controlImage, Eval.controlWithin,
      Bool.and_eq_true]
    refine ⟨?_, within.2⟩
    split
    · exact within.1.1
    · exact within.1.2

theorem install_within {allowed : String → Bool} {world : World} {scope : Scope}
    {pending : List Branch} {parents : List Scope} {movement : Movement}
    (old : scopeWithin allowed { scope with frontier := pending } = true)
    (outer : parents.all (scopeWithin allowed) = true)
    (changed : movementWithin allowed movement = true) :
    configurationWithin allowed (install world scope pending parents movement) := by
  have oldCodes := old
  simp only [scopeWithin, Bool.and_eq_true] at oldCodes
  have withFrontier (work : List Branch) (rows : List Atom)
      (workCodes : work.all (branchWithin allowed) = true) :
      scopeWithin allowed { scope with frontier := work, collected := rows } = true := by
    simp only [scopeWithin, Bool.and_eq_true]
    exact ⟨workCodes, oldCodes.2⟩
  cases movement with
  | next branch =>
      simp only [configurationWithin, install, List.all_cons, Bool.and_eq_true]
      refine ⟨withFrontier _ _ ?_, outer⟩
      simp only [List.all_cons, Bool.and_eq_true]
      exact ⟨changed, oldCodes.1⟩
  | alternatives branches =>
      simp only [configurationWithin, install, List.all_cons, Bool.and_eq_true]
      refine ⟨withFrontier _ _ ?_, outer⟩
      simp only [List.all_append, Bool.and_eq_true]
      exact ⟨changed, oldCodes.1⟩
  | collect bindings expression frames =>
      simp only [configurationWithin, install, List.all_cons, Bool.and_eq_true]
      refine ⟨?_, old, outer⟩
      simp only [movementWithin, Bool.and_eq_true] at changed
      simp [scopeWithin, branchWithin, controlWithin, controlImage, Eval.controlWithin,
        changed.1, changed.2]
  | answer value =>
      simp only [configurationWithin, install, List.all_cons, Bool.and_eq_true]
      exact ⟨withFrontier _ _ oldCodes.1, outer⟩

theorem transition_within {allowed : String → Bool} {program : Program}
    {source target : Configuration} (closed : Eval.ProgramClosed allowed program)
    (transition : Transition program source target)
    (within : configurationWithin allowed source) : configurationWithin allowed target := by
  cases transition with
  | branch frontier derivation =>
      simp only [configurationWithin, List.all_cons, Bool.and_eq_true] at within
      have head := within.1
      simp only [scopeWithin, frontier, List.all_cons, Bool.and_eq_true] at head
      apply install_within _ within.2 (local_transition_within closed derivation head.1.1)
      simp only [scopeWithin, Bool.and_eq_true]
      exact ⟨head.1.2, head.2⟩
  | collapse_return =>
      simp only [configurationWithin, List.all_cons, Bool.and_eq_true] at within
      have frameCodes := within.1
      simp only [scopeWithin, List.all_nil, Bool.true_and, Option.map_some, Option.getD_some] at frameCodes
      have parentCodes := within.2.1
      simp only [scopeWithin, Bool.and_eq_true] at parentCodes
      simp only [configurationWithin, finishScope, List.all_cons, Bool.and_eq_true]
      refine ⟨?_, within.2.2⟩
      simp only [scopeWithin, List.all_cons, branchWithin, controlWithin, controlImage,
        Eval.controlWithin, Bool.true_and, Bool.and_eq_true]
      exact ⟨⟨frameCodes, parentCodes.1⟩, parentCodes.2⟩

theorem advance_within (program : Program) (fuel : Nat) (configuration : Configuration)
    {allowed : String → Bool} (closed : Eval.ProgramClosed allowed program)
    (within : configurationWithin allowed configuration) :
    configurationWithin allowed (advance program fuel configuration) := by
  induction fuel generalizing configuration with
  | zero => exact within
  | succ fuel ih =>
      cases next : step program configuration with
      | none => simpa [advance, next] using within
      | some target =>
          simpa [advance, next] using ih target (transition_within closed (step_transition next) within)

theorem transition_preserves_state {program : Program} {source target : Configuration}
    (within : configurationWithin ProgramReplay.readOnlyHead source)
    (transition : Transition program source target) : target.world.state = source.world.state := by
  cases transition with
  | branch frontier derivation =>
      cases derivation
      all_goals try rfl
      rename_i bindings head index frames values after returns _ _ applied
      simp only [configurationWithin, List.all_cons, Bool.and_eq_true] at within
      have headCodes := within.1
      simp only [scopeWithin, frontier, List.all_cons, branchWithin, controlWithin,
        controlImage, Eval.controlWithin, Eval.targetWithin, Eval.atomsWithin,
        Bool.and_true, Bool.and_eq_true] at headCodes
      exact ProgramReplay.primitive_preserves_state headCodes.1.1.1.1 applied
  | collapse_return => rfl

theorem advance_preserves_state (program : Program) (fuel : Nat) (configuration : Configuration)
    (closed : Eval.ProgramClosed ProgramReplay.readOnlyHead program)
    (within : configurationWithin ProgramReplay.readOnlyHead configuration) :
    (advance program fuel configuration).world.state = configuration.world.state := by
  induction fuel generalizing configuration with
  | zero => rfl
  | succ fuel ih =>
      cases next : step program configuration with
      | none => simp [advance, next]
      | some target =>
          have transition := step_transition next
          simpa only [advance, next] using
            (ih target (transition_within closed transition within)).trans
              (transition_preserves_state within transition)

theorem chunks_loaded_store_reconstruction (program : Program) (fuels : List Nat)
    (expression : Atom) (input : List Atom)
    (checked : ProgramReplay.readOnlyProgram program = true)
    (code : Eval.codeWithin ProgramReplay.readOnlyHead expression = true) :
    let reached := chunks program fuels (start (Effects.loaded program) expression input)
    NamedSpaces.Store.reconstruct reached.world.state.core [] reached.world.state.spacesPrefix
      (reached.world.state.cellRows []) = reached.world.state := by
  dsimp only
  have initial : configurationWithin ProgramReplay.readOnlyHead
      (start (Effects.loaded program) expression input) := by
    simp [configurationWithin, start, scopeWithin, branchWithin, controlWithin, controlImage, Eval.controlWithin, code]
  have same := advance_preserves_state program fuels.sum
    (start (Effects.loaded program) expression input)
    (ProgramReplay.checked_program_closed program checked) initial
  rw [chunks_eq_advance_sum, same]
  exact ProgramReplay.loaded_store_reconstruction program

/-! ## Positive and distinguishing controls -/

namespace Examples

def call (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)

def a : Atom := .symbol "a"
def b : Atom := .symbol "b"
def seven : Atom := .grounded (.int 7)
def pair (first second : Atom) : Atom := call "Pair" [first, second]
def choice : Atom := call "superpose" [.expression [a, b]]

def program : Program :=
  { equations := [
      { head := "dup", arguments := [.var "x"], body := .var "x" },
      { head := "dup", arguments := [.var "x"], body := .var "x" },
      { head := "mark", arguments := [.var "x"], body :=
          call "let" [.var "ignored", call "println!" [.var "x"], .var "x"] }]
    declarations := [], layout := [.equation, .equation, .equation] }

def initial (expression : Atom) : Configuration := start (Effects.loaded program) expression
def mark (expression : Atom) : Atom := call "mark" [expression]
def nested : Atom := mark (mark choice)
def letContinuation : Atom := call "let" [.var "held", mark choice, mark (.var "held")]
def twoArguments : Atom := pair (mark choice) (mark choice)
def collected : Atom := mark (call "collapse" [mark choice])
def collectedLet : Atom := call "let"
  [.var "held", call "collapse" [mark choice], mark (.var "held")]
def correlated : Atom := call "let" [.var "held", choice, pair (.var "held") (.var "held")]
def independent : Atom := pair choice choice

theorem authored_program_admitted : ProgramReplay.readOnlyProgram program = true := by decide

theorem duplicate_equation_occurrences_retained :
    answers (advance program 9 (initial (call "dup" [seven]))) = [seven, seven] := by
  with_unfolding_all rfl

theorem duplicates_do_not_become_a_set :
    (answers (advance program 9 (initial (call "dup" [seven])))).length ≠ 1 := by
  rw [duplicate_equation_occurrences_retained]
  decide

/-- A prepared frontier lets the controls isolate the continuation rule from
the earlier argument evaluation. Complete authored runs remain executable via
`nested`, `letContinuation`, `twoArguments`, `collected` and `collectedLet`. -/
def printFrame : Frame := .argument [] (.function "println!") [] [] 0

def readyPrint (value : Atom) (frames : List Frame) : Branch :=
  ⟨.arguments [] (.function "println!") [] [value] 1, frames⟩

def scalarPrefix : Configuration :=
  ⟨⟨Effects.loaded program, [], []⟩,
    [{ frontier := [readyPrint a [printFrame], readyPrint b [printFrame]] }]⟩

def letPrefix : Configuration :=
  ⟨⟨Effects.loaded program, [], []⟩,
    [{ frontier := [readyPrint a [.bind [] (.var "held") (.var "held"), printFrame],
                    readyPrint b [.bind [] (.var "held") (.var "held"), printFrame]] }]⟩

theorem scalar_delivery_resumes_caller_first :
    (advance program 7 scalarPrefix).world.output =
      [a, Effects.boolean true, b, Effects.boolean true] := by rfl

theorem scalar_delivery_is_not_batched :
    (advance program 3 scalarPrefix).world.output ≠ [a, b] := by
  decide +kernel

theorem let_continuation_resumes_caller_first :
    (advance program 5 letPrefix).world.output = [a, Effects.boolean true] := by
  with_unfolding_all rfl

theorem argument_delivery_preserves_pending_work (first : Atom) (pending values : List Atom)
    (index : Nat) (frames : List Frame) :
    localStep program ⟨Effects.loaded program, [], []⟩
      ⟨.returned first, .argument [] .data pending values index :: frames⟩ =
      some (⟨Effects.loaded program, [], []⟩,
        .next ⟨.arguments [] .data pending (values ++ [first]) (index + 1), frames⟩) := by rfl

theorem independent_arguments_keep_cartesian_occurrences :
    answers (advance program 30 (initial independent)) =
      [pair a a, pair a b, pair b a, pair b b] := by
  with_unfolding_all rfl

theorem binding_keeps_choice_correlation :
    answers (advance program 30 (initial correlated)) = [pair a a, pair b b] := by
  with_unfolding_all rfl

theorem independent_choice_is_not_shared_choice :
    answers (advance program 30 (initial independent)) ≠
      answers (advance program 30 (initial correlated)) := by
  rw [independent_arguments_keep_cartesian_occurrences, binding_keeps_choice_correlation]
  decide

def collapsePrefix : Configuration :=
  ⟨⟨Effects.loaded program, [], []⟩,
    [{ frontier := [readyPrint a [], readyPrint b []], caller := some [printFrame] },
     { frontier := [] }]⟩

def collapseLetPrefix : Configuration :=
  ⟨⟨Effects.loaded program, [], []⟩,
    [{ frontier := [readyPrint a [], readyPrint b []],
       caller := some [.bind [] (.var "held") (.var "held"), printFrame] },
     { frontier := [] }]⟩

theorem collapse_collects_before_releasing_caller :
    (advance program 8 collapsePrefix).world.output =
      [a, b, .expression [Effects.boolean true, Effects.boolean true]] ∧
      answers (advance program 8 collapsePrefix) = [Effects.boolean true] := by
  exact ⟨rfl, rfl⟩

theorem collapse_let_keeps_the_same_delimiter :
    (advance program 9 collapseLetPrefix).world.output =
      [a, b, .expression [Effects.boolean true, Effects.boolean true]] := by
  with_unfolding_all rfl

theorem collapse_does_not_interleave_its_caller :
    (advance program 4 collapsePrefix).world.output ≠ [a, .expression [Effects.boolean true], b] := by
  decide +kernel

theorem collapse_residual_retains_inner_and_outer_scopes :
    (advance program 3 (initial collected)).scopes.length = 2 := by with_unfolding_all rfl

theorem completed_empty_choice_is_not_a_pause :
    completed (advance program 1 (initial (call "empty" []))) = true ∧
      answers (advance program 1 (initial (call "empty" []))) = [] := by
  exact ⟨rfl, rfl⟩

theorem collapse_empty_delivers_one_empty_expression :
    answers (advance program 4 (initial (call "collapse" [call "empty" []]))) =
      [.expression []] := by rfl

def eagerMismatch : Atom := call "let"
  [.symbol "mismatch", call "println!" [call "Seen" [.grounded (.int 9)]], .symbol "value"]

/-- The selected profile performs the value before matching it. Static output
unification before execution would erase this effect. -/
theorem eager_mismatch_retains_performed_effect :
    (advance program 14 (initial eagerMismatch)).world.output =
      [call "Seen" [.grounded (.int 9)]] ∧
      answers (advance program 14 (initial eagerMismatch)) = [] := by
  with_unfolding_all exact ⟨rfl, rfl⟩

def effectThenFault : Atom := call "let"
  [.var "ignored", call "println!" [.symbol "once"], call "%" [seven, .grounded (.int 0)]]

theorem effect_immediately_before_pause_is_retained :
    (advance program 6 (initial effectThenFault)).world.output = [.symbol "once"] ∧
      completed (advance program 6 (initial effectThenFault)) = false ∧
      fault (advance program 6 (initial effectThenFault)) = none := by
  with_unfolding_all exact ⟨rfl, rfl, rfl⟩

theorem fault_retains_performed_effect_and_residual :
    (advance program 15 (initial effectThenFault)).world.output = [.symbol "once"] ∧
      fault (advance program 15 (initial effectThenFault)) = some .zeroDivisor ∧
      completed (advance program 15 (initial effectThenFault)) = false := by
  with_unfolding_all exact ⟨rfl, rfl, rfl⟩

theorem nested_split_preserves_complete_residual :
    chunks program [14, 0, 10, 25] (initial nested) = advance program 49 (initial nested) := by
  rw [chunks_eq_advance_sum]
  rfl

theorem collapse_split_preserves_complete_residual :
    chunks program [2, 13, 12, 15] (initial collected) = advance program 42 (initial collected) := by
  rw [chunks_eq_advance_sum]
  rfl

def lostAlternative : Configuration :=
  { (initial choice) with scopes := [{ frontier := [⟨.evaluate [] a, []⟩] }] }

theorem omitting_saved_alternative_changes_answers :
    answers (advance program 5 (initial choice)) ≠ answers (advance program 5 lostAlternative) := by
  decide +kernel

def batchPrefix : Eval.Configuration :=
  { state := Effects.loaded program
    control := .sequence
      [.arguments [] (.function "println!") [] [a] 1,
       .arguments [] (.function "println!") [] [b] 1] []
    frames := [.bind [] (.var "held") (call "println!" [.var "held"])] }

/-- Existing batch semantics remains a separate, valid reference endpoint.
Its inner sequence completes before the caller receives its answers. -/
theorem batch_prefix_differs_from_scalar_delivery :
    (ProgramReplay.advance program 5 batchPrefix).output = [a, b] ∧
      (advance program 3 scalarPrefix).world.output = [a, Effects.boolean true] := by
  with_unfolding_all exact ⟨rfl, rfl⟩

end Examples

end Mettapedia.Languages.MeTTa.PeTTa.CettaEagerDFS
