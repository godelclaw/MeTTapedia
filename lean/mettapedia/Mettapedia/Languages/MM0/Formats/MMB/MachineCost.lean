import Mathlib.Computability.StateTransition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mettapedia.Languages.MM0.Formats.MMB.Machine
import Mettapedia.Machines.ProductiveCoreAdapters
import Mettapedia.GSLT.Distinction.SimulationComposition

/-!
# The MMB proof machine checks in linearly many transitions

`Machine.run` executes a proof stream one command at a time, and a theorem application
or a definition unfolding runs the unify stream of its declaration inside one command.
This module spells the same machine out one transition at a time: one transition
starts a command, one transition executes a unify command, and one transition ends a
unification. `next` is that transition function, and it agrees with `run`: from a state
and a proof stream it reaches the result of `run`.

The bound is stated with Mathlib's `StateTransition.EvalsToInTime`. Let `U` be the
length of the longest unify stream among the theorems and definitions of the tables.
A proof stream of `n` commands finishes, accepted or rejected, within `(U + 2) * n + 1`
transitions (`run_evalsToInTime`). For fixed tables this is linear in the length of
the proof.

What one transition costs is a separate matter. It touches the arguments of one
declaration and the heap of one unification, so its work is bounded by the size of
the largest declaration, which is constant for fixed tables. That reading assumes the
store and heap are arrays and that expressions are compared by position, as in the
reference verifier `mm0-c`. This module counts transitions only. It also joins
completed retained runs to the unchanged assertion acceptance test.
`MeTTa.Formats.MMB.ExecutedSoundness` composes this exact checking boundary with
the independently stated kernel derivability theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Formats.MMB

open StateTransition

/-! ## Splitting the commands that unify -/

/-- The part of a theorem step before its unification, for the theorem's entry: the
state after popping the target and the arguments, the target, and the starting unifier. -/
def prepareThm (entry : ThmEntry) (state : State) : Option (State × Nat × Unifier) := do
  let (e, state) ← state.popExpr
  let (args, state) ← state.popExprs entry.args.length
  let types ← args.mapM state.typeOf
  if (types.zip entry.args).all (fun (source, target) => source.fits target) &&
      thmArgsDisjoint entry.args types then
    some (state, e, ⟨[e], args.map (·, false), state.stack, state.hyps⟩)
  else none

/-- The part of a theorem step after its unification. -/
def finishThm (state : State) (e : Nat) (save : Bool) (u : Unifier) : State :=
  if save then
    { state with stack := .proof e :: u.main, heap := state.heap ++ [.proof e] }
  else { state with stack := .proof e :: u.main }

theorem stepThm_eq (tables : Tables) (state : State) (T : Nat) (save : Bool) :
    stepThm tables state T save =
      (tables.thms[T]?).bind fun entry =>
        (prepareThm entry state).bind fun prepared =>
          (unifyRun prepared.1.store .apply prepared.2.2 entry.unify).map
            (finishThm prepared.1 prepared.2.1 save) := by
  unfold stepThm prepareThm
  cases tables.thms[T]? with
  | none => rfl
  | some entry =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases state.popExpr with
      | none => rfl
      | some popped =>
          obtain ⟨e, afterTarget⟩ := popped
          simp only [Option.bind_some]
          cases afterTarget.popExprs entry.args.length with
          | none => rfl
          | some poppedArgs =>
              obtain ⟨args, afterArgs⟩ := poppedArgs
              simp only [Option.bind_some]
              cases args.mapM afterArgs.typeOf with
              | none => rfl
              | some types =>
                  simp only [Option.bind_some]
                  split
                  · simp only [Option.bind_some, Option.map_eq_bind]
                    congr 1
                  · rfl

/-- The expressions an unfolding works on: the new expression `e`, the right side of the
goal, the head term and arguments of the goal's left side, and the stack below the
goal. -/
def unfoldTarget (state : State) : Option (Nat × Nat × Nat × List Nat × List Elem) :=
  match state.stack with
  | .expr e :: .goal left right :: rest =>
      match state.store[left]? with
      | some ⟨.app t args, _⟩ => some (e, right, t, args, rest)
      | _ => none
  | _ => none

/-- The part of an unfolding after its unification. -/
def finishUnfold (state : State) (e right : Nat) (u : Unifier) : State :=
  { state with stack := .goal e right :: u.main }

theorem step_unfold_eq (tables : Tables) (mode : Mode) (state : State) :
    step tables mode state .unfold =
      (unfoldTarget state).bind fun target =>
        (tables.terms[target.2.2.1]?).bind fun entry =>
          entry.value.bind fun value =>
            (unifyRun state.store .definition
              ⟨[target.1], target.2.2.2.1.map (·, false), target.2.2.2.2, state.hyps⟩ value).map
              (finishUnfold state target.1 target.2.1) := by
  obtain ⟨store, stack, heap, hyps, nextBound, varCount⟩ := state
  rcases stack with _ | ⟨first, _ | ⟨second, rest⟩⟩
  · rfl
  · cases first <;> rfl
  · cases first <;> cases second <;> try rfl
    rename_i e left right
    simp only [step, unfoldTarget, Option.bind_eq_bind]
    cases store[left]? with
    | none => rfl
    | some leftAlloc =>
        obtain ⟨node, type⟩ := leftAlloc
        cases node with
        | var _ => rfl
        | app t args =>
            simp only [Option.bind_some]
            cases tables.terms[t]? with
            | none => rfl
            | some entry =>
                simp only [Option.bind_some]
                cases entry.value with
                | none => rfl
                | some value =>
                    simp only [Option.bind_some, Option.map_eq_bind]
                    rfl

/-! ## One transition at a time -/

/-- What a unification returns to when it ends. -/
inductive Continuation where
  | theorem (popped : State) (e : Nat) (save : Bool)
  | unfold (state : State) (e right : Nat)

def Continuation.finish : Continuation → Unifier → State
  | .theorem popped e save, u => finishThm popped e save u
  | .unfold state e right, u => finishUnfold state e right u

/-- A configuration of the machine between two transitions. -/
inductive Config where
  | commands (state : State) (rest : List ProofCmd)
  | unify (store : List Alloc) (mode : UMode) (unifier : Unifier) (stream : List UnifyCmd)
      (continuation : Continuation) (rest : List ProofCmd)
  | done (result : Option State)

/-- Start a theorem application: prepare it and enter its unification. -/
def startThm (tables : Tables) (state : State) (T : Nat) (save : Bool) (rest : List ProofCmd) :
    Config :=
  match tables.thms[T]? with
  | none => .done none
  | some entry =>
      match prepareThm entry state with
      | some (popped, e, u) => .unify popped.store .apply u entry.unify (.theorem popped e save) rest
      | none => .done none

/-- Start an unfolding: prepare it and enter its unification. -/
def startUnfold (tables : Tables) (state : State) (rest : List ProofCmd) : Config :=
  match unfoldTarget state with
  | none => .done none
  | some (e, right, t, args, below) =>
      match tables.terms[t]? with
      | none => .done none
      | some entry =>
          match entry.value with
          | none => .done none
          | some value =>
              .unify state.store .definition ⟨[e], args.map (·, false), below, state.hyps⟩ value
                (.unfold state e right) rest

/-- Start a command: unifying commands enter a unification, the others take one step. -/
def startCommand (tables : Tables) (mode : Mode) (state : State) (cmd : ProofCmd)
    (rest : List ProofCmd) : Config :=
  match cmd with
  | .thm T => if mode = .assertion then startThm tables state T false rest else .done none
  | .thmSave T => if mode = .assertion then startThm tables state T true rest else .done none
  | .unfold => startUnfold tables state rest
  | cmd =>
      match step tables mode state cmd with
      | some state' => .commands state' rest
      | none => .done none

/-- The transition function. A finished configuration has no successor. -/
def next (tables : Tables) (mode : Mode) : Config → Option Config
  | .done _ => none
  | .commands state [] => some (.done (some state))
  | .commands state (cmd :: rest) => some (startCommand tables mode state cmd rest)
  | .unify _ umode u [] continuation rest =>
      some (if u.stack = [] ∧ (umode ≠ .statement ∨ u.hyps = []) then
        .commands (continuation.finish u) rest else .done none)
  | .unify store umode u (cmd :: stream) continuation rest =>
      some (match unifyStep store umode u cmd with
        | some u' => .unify store umode u' stream continuation rest
        | none => .done none)

/-! ## Agreement with `run`, and the bound -/

/-- The length of the longest unify stream of a theorem or a definition in the tables. -/
def unifyBound (tables : Tables) : Nat :=
  max (tables.thms.foldr (fun entry bound => max entry.unify.length bound) 0)
    (tables.terms.foldr (fun entry bound => max ((entry.value.map List.length).getD 0) bound) 0)

theorem le_foldr_max {α : Type} (f : α → Nat) {l : List α} {x : α} (member : x ∈ l) :
    f x ≤ l.foldr (fun a bound => max (f a) bound) 0 := by
  induction l with
  | nil => cases member
  | cons a l ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact le_max_left _ _
      · exact (ih later).trans (le_max_right _ _)

theorem thm_unify_le {tables : Tables} {T : Nat} {entry : ThmEntry}
    (lookup : tables.thms[T]? = some entry) : entry.unify.length ≤ unifyBound tables :=
  (le_foldr_max (fun entry : ThmEntry => entry.unify.length)
    (List.mem_of_getElem? lookup)).trans (le_max_left _ _)

theorem value_le {tables : Tables} {t : Nat} {entry : TermEntry} {value : List UnifyCmd}
    (lookup : tables.terms[t]? = some entry) (valued : entry.value = some value) :
    value.length ≤ unifyBound tables := by
  have bound := le_foldr_max (fun entry : TermEntry => (entry.value.map List.length).getD 0)
    (List.mem_of_getElem? lookup)
  simp only [valued, Option.map_some, Option.getD_some] at bound
  exact bound.trans (le_max_right _ _)

/-- The configuration a unification ends in, given its result. -/
def afterUnify (continuation : Continuation) (rest : List ProofCmd) : Option Unifier → Config
  | some u => .commands (continuation.finish u) rest
  | none => .done none

/-- A unification of a stream of length `k` ends within `k + 1` transitions in the
configuration determined by `unifyRun`. -/
def unify_evalsToInTime (tables : Tables) (mode : Mode) (store : List Alloc) (umode : UMode)
    (continuation : Continuation) (rest : List ProofCmd) :
    ∀ (stream : List UnifyCmd) (u : Unifier),
      EvalsToInTime (next tables mode) (.unify store umode u stream continuation rest)
        (some (afterUnify continuation rest (unifyRun store umode u stream))) (stream.length + 1)
  | [], u => by
      refine ⟨⟨1, ?_⟩, le_refl _⟩
      by_cases ended : u.stack = [] ∧ (umode ≠ .statement ∨ u.hyps = [])
      · simp [flip, next, unifyRun, ended, afterUnify]
      · simp [flip, next, unifyRun, ended, afterUnify]
  | cmd :: stream, u => by
      cases stepped : unifyStep store umode u cmd with
      | none =>
          refine ⟨⟨1, ?_⟩, by simp⟩
          simp [flip, next, stepped, unifyRun, afterUnify]
      | some u' =>
          have first : EvalsToInTime (next tables mode)
              (.unify store umode u (cmd :: stream) continuation rest)
              (some (.unify store umode u' stream continuation rest)) 1 :=
            ⟨⟨1, by simp [flip, next, stepped]⟩, le_refl _⟩
          have remaining := unify_evalsToInTime tables mode store umode continuation rest stream u'
          have total := EvalsToInTime.trans _ _ _ _ _ _ first remaining
          have same : unifyRun store umode u (cmd :: stream) = unifyRun store umode u' stream := by
            simp [unifyRun, stepped]
          rw [same]
          exact ⟨total.toEvalsTo, by simpa [Nat.add_comm] using total.steps_le_m⟩

/-- The configuration a command ends in, given the result of `step`. -/
def afterStep (rest : List ProofCmd) : Option State → Config
  | some state => .commands state rest
  | none => .done none

/-- A command finishes within `U + 2` transitions in the configuration determined by
`step`. -/
def command_evalsToInTime (tables : Tables) (mode : Mode) (state : State) (cmd : ProofCmd)
    (rest : List ProofCmd) :
    EvalsToInTime (next tables mode) (.commands state (cmd :: rest))
      (some (afterStep rest (step tables mode state cmd))) (unifyBound tables + 2) := by
  have startStep : EvalsToInTime (next tables mode) (.commands state (cmd :: rest))
      (some (startCommand tables mode state cmd rest)) 1 :=
    ⟨⟨1, by simp [flip, next]⟩, le_refl _⟩
  -- Commands without unification end at their start.
  have plain : ∀ result, startCommand tables mode state cmd rest = afterStep rest result →
      step tables mode state cmd = result →
      EvalsToInTime (next tables mode) (.commands state (cmd :: rest))
        (some (afterStep rest (step tables mode state cmd))) (unifyBound tables + 2) := by
    intro result started stepped
    rw [stepped, ← started]
    exact ⟨startStep.toEvalsTo, startStep.steps_le_m.trans (by omega)⟩
  -- A theorem application: prepare, unify, finish.
  have theoremCase : ∀ (T : Nat) (save : Bool), mode = .assertion →
      startCommand tables mode state cmd rest = startThm tables state T save rest →
      step tables mode state cmd = stepThm tables state T save →
      EvalsToInTime (next tables mode) (.commands state (cmd :: rest))
        (some (afterStep rest (step tables mode state cmd))) (unifyBound tables + 2) := by
    intro T save _ started stepped
    rw [stepped, stepThm_eq]
    cases lookup : tables.thms[T]? with
    | none =>
        have : startCommand tables mode state cmd rest = .done none := by
          rw [started, startThm, lookup]
        rw [this] at startStep
        exact ⟨startStep.toEvalsTo, startStep.steps_le_m.trans (by omega)⟩
    | some entry =>
        simp only [Option.bind_some]
        cases prepared : prepareThm entry state with
        | none =>
            have : startCommand tables mode state cmd rest = .done none := by
              rw [started, startThm, lookup]
              simp only [prepared]
            rw [this] at startStep
            exact ⟨startStep.toEvalsTo, startStep.steps_le_m.trans (by omega)⟩
        | some preparation =>
            obtain ⟨popped, e, u⟩ := preparation
            have entered : startCommand tables mode state cmd rest =
                .unify popped.store .apply u entry.unify (.theorem popped e save) rest := by
              rw [started, startThm, lookup]
              simp only [prepared]
            rw [entered] at startStep
            have unified := unify_evalsToInTime tables mode popped.store .apply
              (.theorem popped e save) rest entry.unify u
            have total := EvalsToInTime.trans _ _ _ _ _ _ startStep unified
            have length := thm_unify_le lookup
            have same : afterUnify (.theorem popped e save) rest
                  (unifyRun popped.store .apply u entry.unify) =
                afterStep rest ((unifyRun popped.store .apply u entry.unify).map
                  (finishThm popped e save)) := by
              cases unifyRun popped.store .apply u entry.unify <;> rfl
            simp only [Option.bind_some]
            rw [← same]
            exact ⟨total.toEvalsTo, total.steps_le_m.trans (by omega)⟩
  cases cmd with
  | thm T =>
      by_cases assertion : mode = .assertion
      · exact theoremCase T false assertion (by simp [startCommand, assertion])
          (by simp [step, assertion])
      · exact plain none (by simp [startCommand, assertion, afterStep]) (by simp [step, assertion])
  | thmSave T =>
      by_cases assertion : mode = .assertion
      · exact theoremCase T true assertion (by simp [startCommand, assertion])
          (by simp [step, assertion])
      · exact plain none (by simp [startCommand, assertion, afterStep]) (by simp [step, assertion])
  | unfold =>
      rw [step_unfold_eq]
      have rejected : startCommand tables mode state .unfold rest = .done none →
          EvalsToInTime (next tables mode) (.commands state (.unfold :: rest))
            (some (.done none)) (unifyBound tables + 2) := by
        intro started
        rw [started] at startStep
        exact ⟨startStep.toEvalsTo, startStep.steps_le_m.trans (by omega)⟩
      cases target : unfoldTarget state with
      | none => exact rejected (by simp [startCommand, startUnfold, target])
      | some data =>
          obtain ⟨e, right, t, args, below⟩ := data
          simp only [Option.bind_some]
          cases lookup : tables.terms[t]? with
          | none => exact rejected (by simp [startCommand, startUnfold, target, lookup])
          | some entry =>
              simp only [Option.bind_some]
              cases valued : entry.value with
              | none => exact rejected (by simp [startCommand, startUnfold, target, lookup, valued])
              | some value =>
                  simp only [Option.bind_some]
                  have entered : startCommand tables mode state .unfold rest =
                      .unify state.store .definition ⟨[e], args.map (·, false), below, state.hyps⟩
                        value (.unfold state e right) rest := by
                    simp [startCommand, startUnfold, target, lookup, valued]
                  rw [entered] at startStep
                  have unified := unify_evalsToInTime tables mode state.store .definition
                    (.unfold state e right) rest value ⟨[e], args.map (·, false), below, state.hyps⟩
                  have total := EvalsToInTime.trans _ _ _ _ _ _ startStep unified
                  have length := value_le lookup valued
                  have same : afterUnify (.unfold state e right) rest
                        (unifyRun state.store .definition
                          ⟨[e], args.map (·, false), below, state.hyps⟩ value) =
                      afterStep rest ((unifyRun state.store .definition
                        ⟨[e], args.map (·, false), below, state.hyps⟩ value).map
                        (finishUnfold state e right)) := by
                    cases unifyRun state.store .definition
                      ⟨[e], args.map (·, false), below, state.hyps⟩ value <;> rfl
                  rw [← same]
                  exact ⟨total.toEvalsTo, total.steps_le_m.trans (by omega)⟩
  | term t =>
      exact plain (step tables mode state (.term t))
        (by simp only [startCommand]; cases step tables mode state (.term t) <;> rfl) rfl
  | termSave t =>
      exact plain (step tables mode state (.termSave t))
        (by simp only [startCommand]; cases step tables mode state (.termSave t) <;> rfl) rfl
  | ref index =>
      exact plain (step tables mode state (.ref index))
        (by simp only [startCommand]; cases step tables mode state (.ref index) <;> rfl) rfl
  | dummy sort =>
      exact plain (step tables mode state (.dummy sort))
        (by simp only [startCommand]; cases step tables mode state (.dummy sort) <;> rfl) rfl
  | hyp =>
      exact plain (step tables mode state .hyp)
        (by simp only [startCommand]; cases step tables mode state .hyp <;> rfl) rfl
  | conv =>
      exact plain (step tables mode state .conv)
        (by simp only [startCommand]; cases step tables mode state .conv <;> rfl) rfl
  | refl =>
      exact plain (step tables mode state .refl)
        (by simp only [startCommand]; cases step tables mode state .refl <;> rfl) rfl
  | symm =>
      exact plain (step tables mode state .symm)
        (by simp only [startCommand]; cases step tables mode state .symm <;> rfl) rfl
  | cong =>
      exact plain (step tables mode state .cong)
        (by simp only [startCommand]; cases step tables mode state .cong <;> rfl) rfl
  | convCut =>
      exact plain (step tables mode state .convCut)
        (by simp only [startCommand]; cases step tables mode state .convCut <;> rfl) rfl
  | convSave =>
      exact plain (step tables mode state .convSave)
        (by simp only [startCommand]; cases step tables mode state .convSave <;> rfl) rfl
  | save =>
      exact plain (step tables mode state .save)
        (by simp only [startCommand]; cases step tables mode state .save <;> rfl) rfl

/-- **Linear checking.** From any state, a proof stream of `n` commands reaches the result
of `run` within `(U + 2) * n + 1` transitions, where `U` is the length of the longest
unify stream in the tables. -/
def run_evalsToInTime (tables : Tables) (mode : Mode) :
    ∀ (cmds : List ProofCmd) (state : State),
      EvalsToInTime (next tables mode) (.commands state cmds)
        (some (.done (run tables mode state cmds))) ((unifyBound tables + 2) * cmds.length + 1)
  | [], state => ⟨⟨1, by simp [flip, next, run]⟩, by simp⟩
  | cmd :: cmds, state => by
      have first := command_evalsToInTime tables mode state cmd cmds
      cases stepped : step tables mode state cmd with
      | none =>
          rw [stepped] at first
          have finished : run tables mode state (cmd :: cmds) = none := by simp [run, stepped]
          rw [finished]
          refine ⟨first.toEvalsTo, first.steps_le_m.trans ?_⟩
          have expand : (unifyBound tables + 2) * (cmds.length + 1) =
              (unifyBound tables + 2) * cmds.length + (unifyBound tables + 2) := Nat.mul_succ _ _
          simp only [List.length_cons]
          omega
      | some state' =>
          rw [stepped] at first
          have remaining := run_evalsToInTime tables mode cmds state'
          have total := EvalsToInTime.trans _ _ _ _ _ _ first remaining
          have same : run tables mode state (cmd :: cmds) = run tables mode state' cmds := by
            simp [run, stepped]
          rw [same]
          refine ⟨total.toEvalsTo, total.steps_le_m.trans ?_⟩
          have expand : (unifyBound tables + 2) * (cmds.length + 1) =
              (unifyBound tables + 2) * cmds.length + (unifyBound tables + 2) := Nat.mul_succ _ _
          simp only [List.length_cons]
          omega

/-- The transitions of a run, as a number: at most `(U + 2) * n + 1`. -/
theorem run_steps_le (tables : Tables) (mode : Mode) (cmds : List ProofCmd) (state : State) :
    (run_evalsToInTime tables mode cmds state).steps ≤ (unifyBound tables + 2) * cmds.length + 1 :=
  (run_evalsToInTime tables mode cmds state).steps_le_m

/-! ## The common event-machine interface

Each internal command or unification transition publishes its source and destination
configuration as an operational occurrence. These events are not external effects.
A completed stream reports its execution result, including rejection; successful
execution alone does not authorize a theorem or validate a whole MMB file.
-/

open Mettapedia.Machines
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The existing microstep machine, with an observer for completed streams. -/
def answerCore (tables : Tables) (mode : Mode) :
    AnswerMachineCore (State × List ProofCmd) (Option State) where
  State := Config
  load input := .commands input.1 input.2
  step := next tables mode
  answer
    | .done result => some result
    | _ => none
  answer_final := by
    intro config result observed
    cases config <;> simp_all [next]

/-- The constructed occurrence-preserving instance of the shared runner. -/
def eventMachine (tables : Tables) (mode : Mode) :
    Machine Config (ProductiveCoreAdapters.Occurrence Config) (Option State) Empty :=
  ProductiveCoreAdapters.answerMachine (answerCore tables mode)

/-- The binary command/unification machine as an object of the existing
checking-machine category. Its state, occurrences and verdict are unchanged;
the command-stream verdict is not a whole-file theorem-admission claim. -/
def checkingObject (tables : Tables) (mode : Mode) :
    ObservedMachine (ProductiveCoreAdapters.Occurrence Config) (Option State) Empty :=
  ObservedMachine.of (eventMachine tables mode)

/-- The old transition bound constructs a connected occurrence trace, with no
    unification call hidden inside one event. -/
theorem command_trace (tables : Tables) (mode : Mode) (state : State)
    (cmds : List ProofCmd) :
    ∃ events, ProductiveCoreAdapters.Trace (answerCore tables mode).toMachineCore
        (.commands state cmds) events (.done (run tables mode state cmds)) ∧
      events.length ≤ (unifyBound tables + 2) * cmds.length + 1 := by
  have execution := run_evalsToInTime tables mode cmds state
  obtain ⟨events, trace, length⟩ := ProductiveCoreAdapters.trace_of_iteration
    (answerCore tables mode).toMachineCore execution.steps execution.evals_in_steps
  exact ⟨events, trace, length ▸ execution.steps_le_m⟩

/-- All command streams complete in the common runner; the final observation
    costs one extra advance beyond the published microsteps. -/
theorem event_run_complete (tables : Tables) (mode : Mode) (state : State)
    (cmds : List ProofCmd) :
    ∃ events, events.length ≤ (unifyBound tables + 2) * cmds.length + 1 ∧
      (eventMachine tables mode).run (events.length + 1) (.commands state cmds) =
        (events, .finished (run tables mode state cmds)) := by
  obtain ⟨events, trace, bounded⟩ := command_trace tables mode state cmds
  exact ⟨events, bounded,
    ProductiveCoreAdapters.trace_answer_finish (answerCore tables mode) trace rfl⟩

/-- A completed event-machine execution reports exactly the independent stream
    executor's result, in both directions. -/
theorem event_finished_iff (tables : Tables) (mode : Mode) (state : State)
    (cmds : List ProofCmd) (result : Option State) :
    (∃ fuel events, (eventMachine tables mode).run fuel (.commands state cmds) =
      (events, .finished result)) ↔ run tables mode state cmds = result := by
  constructor
  · intro observed
    have actual := (ProductiveCoreAdapters.produces_iff_finished
      (answerCore tables mode) (state, cmds) result).mpr observed
    obtain ⟨events, trace, _⟩ := command_trace tables mode state cmds
    have specified : (answerCore tables mode).Produces (state, cmds)
        (run tables mode state cmds) := ⟨_, trace.reachable _, rfl⟩
    exact (answerCore tables mode).produces_unique specified actual
  · intro same
    obtain ⟨events, _, ran⟩ := event_run_complete tables mode state cmds
    exact ⟨events.length + 1, events, same ▸ ran⟩

/-- Arbitrary budget splits preserve the entire command/unification residual. -/
theorem event_run_add (tables : Tables) (mode : Mode) (first second : Nat)
    (config : Config) :
    (eventMachine tables mode).run (first + second) config =
      (eventMachine tables mode).continueRun second
        ((eventMachine tables mode).run first config) :=
  Machine.run_add _ _ _ _

/-- Every saved prefix has a finite completion with the same chronological
occurrences and stream result. The bound on the whole run remains the one
proved for the original microstep machine. -/
theorem event_run_complete_after (tables : Tables) (mode : Mode) (state : State)
    (cmds : List ProofCmd) (first : Nat) :
    ∃ events, events.length ≤ (unifyBound tables + 2) * cmds.length + 1 ∧
      (eventMachine tables mode).continueRun (events.length + 1)
        ((eventMachine tables mode).run first (.commands state cmds)) =
          (events, .finished (run tables mode state cmds)) := by
  obtain ⟨events, bound, completed⟩ := event_run_complete tables mode state cmds
  refine ⟨events, bound, ?_⟩
  rw [← event_run_add, Nat.add_comm first, event_run_add, completed]
  rfl

/-! ## Assertion checking from retained execution

The common checkpoint contains the existing configuration and chronological
microstep occurrences. Its final assertion observer validates the completed
state; it never restarts the proof stream. Argument-loading refusal, stream
refusal and final-statement refusal all remain refusals. An exhausted budget
has no assertion verdict.
-/

/-- Load the assertion's own arguments, retaining the original proof stream.
Loading refusal is terminal; successful loading has not checked a command. -/
def beginAssertion (tables : Tables) (entry : ThmEntry) (commands : List ProofCmd) :
    List (ProductiveCoreAdapters.Occurrence Config) × Outcome Config (Option State) Empty :=
  match loadArgs tables.sorts entry.args with
  | none => ([], .finished none)
  | some state => ([], .exhausted (.commands state commands))

/-- MM0 assertions use the common retained trajectory directly, including the
microstep continuation inside a theorem application or definition unfolding. -/
def assertionTrajectory (tables : Tables) (entry : ThmEntry) (commands : List ProofCmd) :
    Mettapedia.Coalgebra.CoherentPrefixTower.ResumableTrajectory
      (eventMachine tables .assertion).continueRun (beginAssertion tables entry commands) :=
  (eventMachine tables .assertion).retainedTrajectory (beginAssertion tables entry commands)

/-- The assertion observer only checks completed stream results. In particular,
`none` means no verdict yet, while `some false` means completed refusal. -/
def assertionVerdict (tables : Tables) (entry : ThmEntry) (isAxiom : Bool) :
    Outcome Config (Option State) Empty → Option Bool
  | .finished none => some false
  | .finished (some after) => some (finishAssertion tables entry after isAxiom)
  | _ => none

theorem assertionTrajectory_loaded (tables : Tables) (entry : ThmEntry)
    (commands : List ProofCmd) (loaded : State)
    (initialized : loadArgs tables.sorts entry.args = some loaded) (fuel : Nat) :
    (assertionTrajectory tables entry commands).observation fuel =
      (eventMachine tables .assertion).run fuel (.commands loaded commands) := by
  simp [assertionTrajectory, beginAssertion, initialized, Machine.retainedTrajectory,
    Machine.continueRun]

theorem assertionTrajectory_load_refused (tables : Tables) (entry : ThmEntry)
    (commands : List ProofCmd) (refused : loadArgs tables.sorts entry.args = none) (fuel : Nat) :
    (assertionTrajectory tables entry commands).observation fuel = ([], .finished none) := by
  simp [assertionTrajectory, beginAssertion, refused, Machine.retainedTrajectory,
    Machine.continueRun]

/-- Resuming preserves the entire checkpoint, not merely its final Boolean. -/
theorem assertionTrajectory_resume (tables : Tables) (entry : ThmEntry)
    (commands : List ProofCmd) (first extra : Nat) :
    (assertionTrajectory tables entry commands).observation (first + extra) =
      (eventMachine tables .assertion).continueRun extra
        ((assertionTrajectory tables entry commands).observation first) :=
  (assertionTrajectory tables entry commands).resume first extra

/-- The published occurrence history never shrinks or restarts on resumption. -/
theorem assertionTrajectory_events_prefix (tables : Tables) (entry : ThmEntry)
    (commands : List ProofCmd) (first extra : Nat) :
    ((assertionTrajectory tables entry commands).observation first).1.IsPrefix
      ((assertionTrajectory tables entry commands).observation (first + extra)).1 :=
  (assertionTrajectory tables entry commands).observer_prefix_after_resume Prod.fst
    (eventMachine tables .assertion).continueRun_events_prefix first extra

/-- A verdict observed at any budget agrees exactly with the original full
assertion checker. This includes refusals after successful command execution. -/
theorem assertionTrajectory_verdict_sound (tables : Tables) (entry : ThmEntry)
    (commands : List ProofCmd) (isAxiom : Bool) (fuel : Nat) (verdict : Bool)
    (observed : assertionVerdict tables entry isAxiom
      ((assertionTrajectory tables entry commands).observation fuel).2 = some verdict) :
    checkAssertion tables entry commands isAxiom = verdict := by
  cases initialized : loadArgs tables.sorts entry.args with
  | none =>
      rw [assertionTrajectory_load_refused tables entry commands initialized] at observed
      have same : false = verdict := Option.some.inj observed
      simp only [checkAssertion, initialized, Option.bind_none]
      exact same
  | some loaded =>
      rw [assertionTrajectory_loaded tables entry commands loaded initialized] at observed
      cases completed : (eventMachine tables .assertion).run fuel (.commands loaded commands) with
      | mk events outcome =>
          rw [completed] at observed
          cases outcome with
          | exhausted _ | stuck _ | suspended _ _ | faulted => cases observed
          | finished result =>
              have executed := (event_finished_iff tables .assertion loaded commands result).mp
                ⟨fuel, events, completed⟩
              cases result with
              | none =>
                  have same : false = verdict := Option.some.inj observed
                  simp only [checkAssertion, initialized, Option.bind_some, executed]
                  exact same
              | some after =>
                  have same : finishAssertion tables entry after isAxiom = verdict :=
                    Option.some.inj observed
                  exact (checkAssertion_of_run tables entry commands isAxiom loaded after
                    initialized executed).trans same

/-- After any previously spent budget, the same retained execution eventually
publishes the original assertion verdict. No proof prefix is rerun. -/
theorem assertionTrajectory_verdict_complete (tables : Tables) (entry : ThmEntry)
    (commands : List ProofCmd) (isAxiom : Bool) (first : Nat) :
    ∃ extra, assertionVerdict tables entry isAxiom
      ((assertionTrajectory tables entry commands).observation (first + extra)).2 =
        some (checkAssertion tables entry commands isAxiom) := by
  cases initialized : loadArgs tables.sorts entry.args with
  | none =>
      refine ⟨0, ?_⟩
      rw [assertionTrajectory_load_refused tables entry commands initialized]
      simp only [assertionVerdict, checkAssertion, initialized, Option.bind_none]
  | some loaded =>
      obtain ⟨events, _, completed⟩ := event_run_complete_after tables .assertion loaded commands first
      refine ⟨events.length + 1, ?_⟩
      rw [assertionTrajectory_resume,
        assertionTrajectory_loaded tables entry commands loaded initialized, completed]
      cases executed : run tables .assertion loaded commands <;>
        simp only [assertionVerdict, checkAssertion, initialized, Option.bind_some, executed]

/-- Exact preservation and reflection of acceptance and rejection, independently
of where execution was paused. -/
theorem assertionTrajectory_verdict_iff (tables : Tables) (entry : ThmEntry)
    (commands : List ProofCmd) (isAxiom : Bool) (first : Nat) (verdict : Bool) :
    (∃ extra, assertionVerdict tables entry isAxiom
      ((assertionTrajectory tables entry commands).observation (first + extra)).2 = some verdict) ↔
        checkAssertion tables entry commands isAxiom = verdict := by
  constructor
  · rintro ⟨extra, observed⟩
    exact assertionTrajectory_verdict_sound tables entry commands isAxiom (first + extra) verdict observed
  · intro same
    obtain ⟨extra, observed⟩ := assertionTrajectory_verdict_complete tables entry commands isAxiom first
    exact ⟨extra, same ▸ observed⟩

/-- Published occurrences account for the actual microsteps, excluding the
    terminal observation. -/
theorem event_computational_count (tables : Tables) (mode : Mode) (fuel : Nat)
    (config : Config) :
    (eventMachine tables mode).spent
        (ProductiveCoreAdapters.computationalPrice (answerCore tables mode).toMachineCore
          (fun _ => 1)) fuel config =
      ((eventMachine tables mode).run fuel config).1.length :=
  ProductiveCoreAdapters.answer_computational_count (answerCore tables mode) fuel config

/-- The adapter does not hide unification or proof computation as administration. -/
theorem event_no_administration (tables : Tables) (mode : Mode) (config target : Config) :
    (eventMachine tables mode).step config ≠ some (.silent target) :=
  ProductiveCoreAdapters.answer_no_administration (answerCore tables mode) config target

/-! ## Controls -/

/-- A table with one axiom whose unify stream has length three. -/
def controlTables : Tables :=
  ⟨[], [], [⟨[], [.term 0, .term 1, .hyp]⟩]⟩

example : unifyBound controlTables = 3 := by decide

/-- The empty proof stream finishes in one transition with the unchanged execution state. -/
example : (run_evalsToInTime controlTables .assertion [] ⟨[], [], [], [], 0, 0⟩).steps ≤ 1 :=
  run_steps_le _ _ _ _

/-- A stream that applies a theorem with an empty stack is rejected; the bound still
holds, at `(3 + 2) * 1 + 1 = 6` transitions. -/
example : run controlTables .assertion ⟨[], [], [], [], 0, 0⟩ [.thm 0] = none := by decide

example : (run_evalsToInTime controlTables .assertion [.thm 0] ⟨[], [], [], [], 0, 0⟩).steps ≤ 6 :=
  run_steps_le _ _ _ _

end Mettapedia.Languages.MM0.Formats.MMB
