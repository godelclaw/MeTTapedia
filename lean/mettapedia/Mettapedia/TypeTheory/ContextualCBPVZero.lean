import Mettapedia.TypeTheory.ContextualCBPVNormalization
import Mettapedia.TypeTheory.ContextualCBPVEquations

/-!
# Zero answers: a nullary choice for the contextual effect signature

The existing contextual programs (`Program`) have no nullary choice: every
execution has at least one world. A computation with zero answers, such as
`(empty)`, therefore needs a larger free signature.

* `ProgramZ` is the free computation with `pure`, the nullary choice `zero`,
  and the operations of `Program`. It is a monad (`bind_pure`, `bind_assoc`),
  and `zero` is a left zero of sequencing (`zero_bind`).
* `Program.toZ` embeds `Program` into it. The embedding is a monad morphism
  (`toZ_pure`, `toZ_bind`), injective, and preserves the isolated-world
  observation exactly (`runWorldsAt_toZ`): adding the nullary choice is
  conservative over every existing contextual program.
* `zero` is an **occurrence-free** observation: it has no world
  (`runWorldsAt_zero`), a branch that ends in it leaves no world
  (`runWorldsAt_bind_zero`), and beside an alternative it contributes nothing
  but the branch step (`runWorldsAt_choose_zero_left`, `_right`). No program in
  the image of `Program` has an empty observation (`runWorldsAt_toZ_ne_nil`),
  so zero answers are new.

**In ContextualCBPV.** `withZero sig` extends a signature's raise kinds by one
reserved kind `none`. `empty` raises it, and the top-level observer
`observeZ` reads that leaf as the nullary choice. Raising is algebraic, so
`empty` passes through `to`, application and every handler of a user kind,
exactly as the nullary choice does (`empty_bind`, `empty_app`,
`empty_handle`). The reserved kind must not be handled: a handler for it
recovers an occurrence (`handled_empty_is_not_zero`). This presentation uses
the existing calculus unchanged; a first-class `empty` former whose
denotation lands in `ProgramZ`-algebras is the core-calculus form of the same
operation.

The zoo's zero answers, unit datum and error value are three different
observations (`zero_unit_error_apart`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualDependentSequencing

universe uState uAnswer uOther uLast uIntent

/-! ## The free signature with a nullary choice -/

/-- Contextual programs with a nullary choice. -/
inductive ProgramZ (State : Type uState) (Answer : Type uAnswer) (Intent : Type uIntent) where
  | pure (answer : Answer)
  | zero
  | choose (left right : ProgramZ State Answer Intent)
  | read (next : State → ProgramZ State Answer Intent)
  | write (state : State) (next : ProgramZ State Answer Intent)
  | intent (request : Intent) (next : ProgramZ State Answer Intent)

namespace ProgramZ

variable {State : Type uState} {Answer : Type uAnswer} {Other : Type uOther}
  {Last : Type uLast} {Intent : Type uIntent}

/-- Sequencing; `zero` absorbs the continuation. -/
def bind : ProgramZ State Answer Intent → (Answer → ProgramZ State Other Intent) →
    ProgramZ State Other Intent
  | .pure answer, next => next answer
  | .zero, _ => .zero
  | .choose left right, next => .choose (bind left next) (bind right next)
  | .read continuation, next => .read fun state => bind (continuation state) next
  | .write state continuation, next => .write state (bind continuation next)
  | .intent request continuation, next => .intent request (bind continuation next)

/-- Mapping answers. -/
def map (function : Answer → Other) (program : ProgramZ State Answer Intent) :
    ProgramZ State Other Intent :=
  bind program fun answer => .pure (function answer)

@[simp] theorem pure_bind (answer : Answer) (next : Answer → ProgramZ State Other Intent) :
    bind (.pure answer) next = next answer := rfl

/-- **`zero` is a left zero of sequencing.** -/
@[simp] theorem zero_bind (next : Answer → ProgramZ State Other Intent) :
    bind (.zero : ProgramZ State Answer Intent) next = .zero := rfl

@[simp] theorem bind_pure (program : ProgramZ State Answer Intent) :
    bind program (fun answer => .pure answer) = program := by
  induction program with
  | pure answer => rfl
  | zero => rfl
  | choose left right leftIH rightIH => simp only [bind, leftIH, rightIH]
  | read next ih => simp only [bind, ih]
  | write state next ih => simp only [bind, ih]
  | intent request next ih => simp only [bind, ih]

theorem bind_assoc (program : ProgramZ State Answer Intent)
    (next : Answer → ProgramZ State Other Intent) (later : Other → ProgramZ State Last Intent) :
    bind (bind program next) later = bind program (fun answer => bind (next answer) later) := by
  induction program with
  | pure answer => rfl
  | zero => rfl
  | choose left right leftIH rightIH => simp only [bind, leftIH, rightIH]
  | read continuation ih => simp only [bind, ih]
  | write state continuation ih => simp only [bind, ih]
  | intent request continuation ih => simp only [bind, ih]

/-! ### The isolated-world observer -/

/-- Every alternative from its own parent state; `zero` has no world. -/
def runWorldsAt : ProgramZ State Answer Intent → State → BranchTrace →
    List (WorldResult State Answer Intent)
  | .pure answer, state, branch =>
      [{ branch := branch, answer := answer, state := state, intents := [] }]
  | .zero, _, _ => []
  | .choose left right, state, branch =>
      runWorldsAt left state (false :: branch) ++ runWorldsAt right state (true :: branch)
  | .read next, state, branch => runWorldsAt (next state) state branch
  | .write newState next, _, branch => runWorldsAt next newState branch
  | .intent request next, state, branch =>
      (runWorldsAt next state branch).map fun result =>
        { result with intents := request :: result.intents }

/-- **`zero` is occurrence-free.** -/
@[simp] theorem runWorldsAt_zero (state : State) (branch : BranchTrace) :
    runWorldsAt (.zero : ProgramZ State Answer Intent) state branch = [] := rfl

/-- The sequencing law of the observer, as for `Program`. -/
theorem runWorldsAt_bind (program : ProgramZ State Answer Intent)
    (next : Answer → ProgramZ State Other Intent) (state : State) (branch : BranchTrace) :
    runWorldsAt (program.bind next) state branch =
      (runWorldsAt program state branch).flatMap fun prior =>
        (runWorldsAt (next prior.answer) prior.state prior.branch).map
          (WorldResult.prependIntents prior.intents) := by
  induction program generalizing state branch with
  | pure answer =>
      simp only [bind, runWorldsAt, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact (List.map_id _).symm
  | zero => rfl
  | choose left right leftIH rightIH =>
      simp only [bind, runWorldsAt, leftIH, rightIH, List.flatMap_append]
  | read continuation ih => exact ih state state branch
  | write newState continuation ih => exact ih newState branch
  | intent request continuation ih =>
      simp only [bind, runWorldsAt, ih, List.map_flatMap, List.flatMap_map, List.map_map,
        Function.comp_def, WorldResult.prependIntents]
      rfl

/-- A branch that ends in `zero` leaves no world, whatever it did before. -/
theorem runWorldsAt_bind_zero (program : ProgramZ State Answer Intent) (state : State)
    (branch : BranchTrace) :
    runWorldsAt (program.bind fun _ => (.zero : ProgramZ State Other Intent)) state branch = [] := by
  rw [runWorldsAt_bind]
  simp

/-- Beside an alternative, `zero` contributes only the branch step. -/
theorem runWorldsAt_choose_zero_left (program : ProgramZ State Answer Intent) (state : State)
    (branch : BranchTrace) :
    runWorldsAt (.choose .zero program) state branch = runWorldsAt program state (true :: branch) :=
  rfl

theorem runWorldsAt_choose_zero_right (program : ProgramZ State Answer Intent) (state : State)
    (branch : BranchTrace) :
    runWorldsAt (.choose program .zero) state branch =
      runWorldsAt program state (false :: branch) := by
  simp [runWorldsAt]

/-- What a world is apart from its branch path. -/
def WorldResult.content (world : WorldResult State Answer Intent) :
    Answer × State × List Intent :=
  (world.answer, world.state, world.intents)

/-- Answers, states and intents do not depend on the branch path so far. -/
theorem runWorldsAt_content_branch (program : ProgramZ State Answer Intent) (state : State)
    (branch other : BranchTrace) :
    (runWorldsAt program state branch).map WorldResult.content =
      (runWorldsAt program state other).map WorldResult.content := by
  induction program generalizing state branch other with
  | pure answer => rfl
  | zero => rfl
  | choose left right leftIH rightIH =>
      simp only [runWorldsAt, List.map_append]
      rw [leftIH state (false :: branch) (false :: other),
        rightIH state (true :: branch) (true :: other)]
  | read next ih => exact ih state state branch other
  | write newState next ih => exact ih newState branch other
  | intent request next ih =>
      simp only [runWorldsAt, List.map_map]
      have := congrArg (List.map fun (content : Answer × State × List Intent) =>
        (content.1, content.2.1, request :: content.2.2)) (ih state branch other)
      simpa [List.map_map, Function.comp_def, WorldResult.content] using this

/-- **`zero` is a unit of choice for everything but the branch path.** -/
theorem choose_zero_content (program : ProgramZ State Answer Intent) (state : State)
    (branch : BranchTrace) :
    (runWorldsAt (.choose .zero program) state branch).map WorldResult.content =
      (runWorldsAt program state branch).map WorldResult.content := by
  rw [runWorldsAt_choose_zero_left]
  exact runWorldsAt_content_branch program state (true :: branch) branch

end ProgramZ

/-! ## The embedding of `Program` -/

namespace Program

variable {State : Type uState} {Answer : Type uAnswer} {Other : Type uOther}
  {Intent : Type uIntent}

/-- Every contextual program is a program with a nullary choice that does not
use it. -/
def toZ : Program State Answer Intent → ProgramZ State Answer Intent
  | .pure answer => .pure answer
  | .choose left right => .choose (toZ left) (toZ right)
  | .read next => .read fun state => toZ (next state)
  | .write state next => .write state (toZ next)
  | .intent request next => .intent request (toZ next)

@[simp] theorem toZ_pure (answer : Answer) :
    toZ (.pure answer : Program State Answer Intent) = .pure answer := rfl

/-- **The embedding is a monad morphism.** -/
theorem toZ_bind (program : Program State Answer Intent)
    (next : Answer → Program State Other Intent) :
    toZ (program.bind next) = (toZ program).bind fun answer => toZ (next answer) := by
  induction program with
  | pure answer => rfl
  | choose left right leftIH rightIH =>
      simp only [Program.bind, toZ, ProgramZ.bind, leftIH, rightIH]
  | read continuation ih => simp only [Program.bind, toZ, ProgramZ.bind, ih]
  | write state continuation ih => simp only [Program.bind, toZ, ProgramZ.bind, ih]
  | intent request continuation ih => simp only [Program.bind, toZ, ProgramZ.bind, ih]

theorem toZ_injective : Function.Injective (toZ : Program State Answer Intent → _) := by
  intro first second equal
  induction first generalizing second with
  | pure answer =>
      cases second <;> simp only [toZ, ProgramZ.pure.injEq, reduceCtorEq] at equal
      rw [equal]
  | choose left right leftIH rightIH =>
      cases second <;> simp only [toZ, ProgramZ.choose.injEq, reduceCtorEq] at equal
      rw [leftIH equal.1, rightIH equal.2]
  | read next ih =>
      cases second with
      | read next' =>
          simp only [toZ, ProgramZ.read.injEq] at equal
          congr 1
          funext state
          exact ih state (congrFun equal state)
      | _ => simp only [toZ, reduceCtorEq] at equal
  | write state next ih =>
      cases second <;> simp only [toZ, ProgramZ.write.injEq, reduceCtorEq] at equal
      rw [equal.1, ih equal.2]
  | intent request next ih =>
      cases second <;> simp only [toZ, ProgramZ.intent.injEq, reduceCtorEq] at equal
      rw [equal.1, ih equal.2]

/-- **Conservativity.** The embedding preserves the isolated-world
observation exactly. -/
theorem runWorldsAt_toZ (program : Program State Answer Intent) (state : State)
    (branch : BranchTrace) :
    ProgramZ.runWorldsAt (toZ program) state branch = runWorldsAt program state branch := by
  induction program generalizing state branch with
  | pure answer => rfl
  | choose left right leftIH rightIH =>
      simp only [toZ, ProgramZ.runWorldsAt, runWorldsAt, leftIH, rightIH]
  | read next ih => exact ih state state branch
  | write newState next ih => exact ih newState branch
  | intent request next ih => simp only [toZ, ProgramZ.runWorldsAt, runWorldsAt, ih]

/-- No embedded program has an empty observation. -/
theorem runWorldsAt_toZ_ne_nil (program : Program State Answer Intent) (state : State)
    (branch : BranchTrace) : ProgramZ.runWorldsAt (toZ program) state branch ≠ [] := by
  rw [runWorldsAt_toZ]
  induction program generalizing state branch with
  | pure answer => exact List.cons_ne_nil _ _
  | choose left right leftIH _ =>
      intro empty
      exact leftIH state (false :: branch) (List.append_eq_nil_iff.mp empty).1
  | read next ih => exact ih state state branch
  | write newState next ih => exact ih newState branch
  | intent request next ih =>
      intro empty
      exact ih state branch (List.map_eq_nil_iff.mp empty)

/-- **Zero answers are new**: `zero` is not observed like any contextual
program, so it is not in the image of the embedding. -/
theorem zero_not_embedded (state : State) (branch : BranchTrace) :
    ¬ ∃ program : Program State Answer Intent,
      ProgramZ.runWorldsAt (toZ program) state branch =
        ProgramZ.runWorldsAt (.zero : ProgramZ State Answer Intent) state branch := by
  rintro ⟨program, equal⟩
  exact runWorldsAt_toZ_ne_nil program state branch (equal.trans rfl)

end Program

/-! ## `empty` in ContextualCBPV -/

/-- The signature with one reserved raise kind, `none`, for the nullary
choice; a user kind `k` is `some k`. -/
abbrev withZero (sig : Signature) : Signature :=
  { sig with Kind := Option sig.Kind }

variable {sig : Signature} [DecidableEq sig.Kind]

/-- `(empty)`: raise the reserved kind. The payload is irrelevant. -/
abbrev emptyC {context : List (VTy sig.Ground)} {type : CTy sig.Ground}
    (blank : sig.Data sig.payloadSort) : Comp (withZero sig) context type :=
  .raise none (.const (sig := withZero sig) sig.payloadSort blank)

/-- The top-level observer of the extended signature: a reserved-kind leaf is
the nullary choice; user kinds stay raised no-values. -/
def zeroLeaf {Answer : Type} :
    Answer ⊕ Raised (withZero sig) → ProgramZ (State sig) (Answer ⊕ Raised sig) (Request sig)
  | .inl answer => .pure (.inl answer)
  | .inr (some kind, payload) => .pure (.inr (kind, payload))
  | .inr (none, _) => .zero

def observeZ {Answer : Type}
    (program : Program (State sig) (Answer ⊕ Raised (withZero sig)) (Request sig)) :
    ProgramZ (State sig) (Answer ⊕ Raised sig) (Request sig) :=
  (Program.toZ program).bind zeroLeaf

/-- The observed program of a closed returner of the extended signature. -/
def Comp.observedZ {answer : VTy sig.Ground} (code : Comp (withZero sig) [] (.ret answer)) :
    ProgramZ (State sig) (VTy.den (withZero sig) answer ⊕ Raised sig) (Request sig) :=
  observeZ (CTy.asProgram (withZero sig) (code.den Env.empty))

theorem empty_observed {answer : VTy sig.Ground} (blank : sig.Data sig.payloadSort) :
    (emptyC (type := .ret answer) blank : Comp (withZero sig) [] (.ret answer)).observedZ =
      .zero := rfl

/-- **`empty` absorbs its continuation.** -/
theorem empty_bind {answer result : VTy sig.Ground} (blank : sig.Data sig.payloadSort)
    (body : Comp (withZero sig) [answer] (.ret result)) :
    (Comp.bind (emptyC blank) body).observedZ = .zero := by
  unfold Comp.observedZ
  rw [show (Comp.bind (emptyC blank) body).den Env.empty =
      (Comp.raise none (.const (sig := withZero sig) sig.payloadSort blank)).den Env.empty from
    HeadStep.den_eq (.bindRaise none _ body) Env.empty]
  rfl

/-- **`empty` passes through application.** -/
theorem empty_app {domain : VTy sig.Ground} {result : VTy sig.Ground}
    (blank : sig.Data sig.payloadSort) (argument : Val (withZero sig) [] domain) :
    (Comp.app (emptyC (type := .arrow domain (.ret result)) blank) argument).observedZ = .zero := by
  unfold Comp.observedZ
  rw [show (Comp.app (emptyC (type := .arrow domain (.ret result)) blank) argument).den Env.empty =
      (Comp.raise none (.const (sig := withZero sig) sig.payloadSort blank)).den Env.empty from
    HeadStep.den_eq (.appRaise none _ argument) Env.empty]
  rfl

/-- **`empty` passes through every handler of a user kind.** -/
theorem empty_handle {answer result : VTy sig.Ground} (blank : sig.Data sig.payloadSort)
    (kind : sig.Kind) (onReturn : Comp (withZero sig) [answer] (.ret result))
    (onRaise : Comp (withZero sig) [.ground sig.payloadSort] (.ret result)) :
    (Comp.handle (emptyC blank) (some kind) onReturn onRaise).observedZ = .zero := by
  unfold Comp.observedZ
  rw [show (Comp.handle (emptyC blank) (some kind) onReturn onRaise).den Env.empty =
      (Comp.raise none (.const (sig := withZero sig) sig.payloadSort blank)).den Env.empty from
    HeadStep.den_eq (.handleOther _ onReturn onRaise (by simp)) Env.empty]
  rfl

/-- **Beside an alternative, `empty` contributes only the branch step.** -/
theorem empty_choose_observed {answer : VTy sig.Ground} (blank : sig.Data sig.payloadSort)
    (code : Comp (withZero sig) [] (.ret answer)) (state : State sig) (branch : BranchTrace) :
    ProgramZ.runWorldsAt (Comp.choose (emptyC blank) code).observedZ state branch =
      ProgramZ.runWorldsAt code.observedZ state (true :: branch) := rfl

/-- **The reserved kind must not be handled**: a handler for it turns zero
answers into an occurrence, which the nullary choice never has. -/
theorem handled_empty_is_not_zero {answer : VTy sig.Ground} (blank : sig.Data sig.payloadSort)
    (value : Val (withZero sig) [] answer) (state : State sig) (branch : BranchTrace) :
    ProgramZ.runWorldsAt
        (Comp.handle (emptyC blank) none (.ret (.var .zero)) (.ret (value.rename (Ren.weaken _))) :
          Comp (withZero sig) [] (.ret answer)).observedZ state branch ≠ [] := by
  have step := HeadStep.den_eq
    (.handleCaught (none : Option sig.Kind) (.const (sig := withZero sig) sig.payloadSort blank)
      (.ret (.var .zero) : Comp (withZero sig) [answer] (.ret answer))
      (.ret (value.rename (Ren.weaken _)))) Env.empty
  unfold Comp.observedZ
  rw [step]
  change ProgramZ.runWorldsAt ((Program.toZ (Program.pure (Sum.inl _))).bind zeroLeaf) state
    branch ≠ []
  simp [Program.toZ, zeroLeaf, ProgramZ.runWorldsAt]

/-! ## Zero answers, the unit datum and an error are three observations -/

/-- Zero answers, a returned value and a raised user kind are observed
differently: no world, a returned answer, a raised no-value. -/
theorem zero_unit_error_apart {answer : VTy sig.Ground} (blank : sig.Data sig.payloadSort)
    (value : Val (withZero sig) [] answer) (kind : sig.Kind) (state : State sig) :
    ProgramZ.runWorldsAt (emptyC (type := .ret answer) blank).observedZ state [] = [] ∧
      ((ProgramZ.runWorldsAt (Comp.ret value).observedZ state []).map WorldResult.answer =
        [.inl (value.den Env.empty)]) ∧
      ((ProgramZ.runWorldsAt
          (Comp.raise (sig := withZero sig) (context := []) (type := .ret answer) (some kind)
            (.const (sig := withZero sig) sig.payloadSort blank)).observedZ state []).map
          WorldResult.answer = [.inr (kind, blank)]) :=
  ⟨rfl, rfl, rfl⟩

#print axioms ProgramZ.bind_assoc
#print axioms ProgramZ.runWorldsAt_bind
#print axioms ProgramZ.choose_zero_content
#print axioms Program.toZ_bind
#print axioms Program.toZ_injective
#print axioms Program.runWorldsAt_toZ
#print axioms Program.zero_not_embedded
#print axioms empty_bind
#print axioms empty_app
#print axioms empty_handle
#print axioms empty_choose_observed
#print axioms handled_empty_is_not_zero
#print axioms zero_unit_error_apart

end Mettapedia.TypeTheory.ContextualCBPV
