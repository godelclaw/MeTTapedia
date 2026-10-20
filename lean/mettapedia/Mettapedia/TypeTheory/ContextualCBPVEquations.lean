import Mettapedia.TypeTheory.ContextualCBPVOperational
import Mettapedia.GSLT.Dynamics.ContextualStrategyQualification

/-!
# CBPV equations and qualified strategies in the contextual algebra model

**Equations.** Levy's CBPV equations hold in the existing algebra model,
as equalities of algebra elements (which retain branch structure, state
updates, deferred intents and occurrence multiplicity):

* thunk/force: `force (thunk M) = M`, `thunk (force V) = V`;
* return/`to`: `ret V to x. N = N[V/x]`, `M to x. ret x = M`, and
  associativity of `to`;
* functions: `(λx. M) V = M[V/x]`, `λx. M x = M`; pairs: `split` β;
* algebraicity: `choose`, `read`, `write`, `intent` and `raise` commute with
  every evaluation frame (`HeadStep`), and `M to x. N` is the handler that
  raises every kind again (`bind_eq_handle_reraise`).

**Qualified strategies.** `ContextualStrategyQualification` licenses result
reuse and discarding for read-only programs. At the CBPV level the two
licences separate:

* reuse (`M to x. M to y. N` as `M to x. N[x/y]`) holds for every read-only
  returner, including one that raises: a raised no-value is copyable;
* discarding (`M to x. N` as `N`, `x` unused) needs read-only *and*
  raise-free: a raise is not discardable (`raise_not_discardable`).

These are Führmann's copyable/discardable distinctions for this effect
signature. Controls: an independent second choice gives four occurrences, a
reused one two (`independent_choice_four`, `correlated_choice_two`); an
eager `let` of a two-way choice gives two occurrences of an unused body
(`eager_let_two_occurrences`); a thunked unused argument is never run
(`thunked_argument_one_occurrence`) while the call-by-value translation runs
it (`eager_argument_two_occurrences`); a shared argument used twice gives two
correlated pairs, a re-forced one four (`shared_argument_two_pairs`,
`reforced_argument_four_pairs`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.GSLT.Dynamics.ContextualStrategyQualification
open Mettapedia.TypeTheory.ContextualDependentSequencing

variable {sig : Signature} [DecidableEq sig.Kind]

/-! ## Equations -/

section Equations

variable {context : List (VTy sig.Ground)}

theorem force_thunk {type : CTy sig.Ground} (body : Comp sig context type)
    (η : Env sig context) : (Comp.force (.thunk body)).den η = body.den η := rfl

theorem thunk_force {type : CTy sig.Ground} (suspended : Val sig context (.thunk type))
    (η : Env sig context) : (Val.thunk (.force suspended)).den η = suspended.den η := rfl

theorem ret_bind {answer : VTy sig.Ground} {type : CTy sig.Ground}
    (value : Val sig context answer) (body : Comp sig (answer :: context) type)
    (η : Env sig context) :
    (Comp.bind (.ret value) body).den η = (body.instantiate value).den η :=
  HeadStep.den_eq (.bindRet value body) η

theorem bind_ret {answer : VTy sig.Ground} (first : Comp sig context (.ret answer))
    (η : Env sig context) :
    (Comp.bind first (.ret (.var .zero))).den η = first.den η := by
  change Program.bind (Program.map (Sum.elim (fun value => Program.pure (Sum.inl value))
      (fun raised => Program.pure (Sum.inr raised))) (CTy.asProgram sig (first.den η)))
      (fun program => program) = CTy.asProgram sig (first.den η)
  have pointwise : Sum.elim (fun value => (Program.pure (Sum.inl value) :
      Program (State sig) (VTy.den sig answer ⊕ Raised sig) (Request sig)))
      (fun raised => Program.pure (Sum.inr raised)) = fun result => Program.pure result := by
    funext result
    cases result <;> rfl
  rw [pointwise, Program.map, ContextualComputationKleisli.Program.bind_assoc]
  exact ContextualComputationKleisli.Program.bind_pure _

omit [DecidableEq sig.Kind] in
/-- Sequencing into the free algebra of a returner is `Program.bind`. -/
theorem continue_ret {answer : VTy sig.Ground} {Answer : Type}
    (program : Program (State sig) (Answer ⊕ Raised sig) (Request sig))
    (next : Answer → (CTy.alg sig (.ret answer)).A)
    (onRaise : Raised sig → (CTy.alg sig (.ret answer)).A) :
    CTy.asProgram sig (CTy.continue sig (.ret answer) program next onRaise) =
      Program.bind program (fun result => CTy.asProgram sig (Sum.elim next onRaise result)) :=
  ContextualAlgebraSequencing.sequence_free program (Sum.elim next onRaise)

theorem bind_assoc {answer middle : VTy sig.Ground} {type : CTy sig.Ground}
    (first : Comp sig context (.ret answer)) (second : Comp sig (answer :: context) (.ret middle))
    (third : Comp sig (middle :: context) type) (η : Env sig context) :
    (Comp.bind (.bind first second) third).den η =
      (Comp.bind first (.bind second (Comp.weakenUnder third))).den η := by
  change CTy.continue sig type (CTy.asProgram sig (CTy.continue sig (.ret middle)
      (CTy.asProgram sig (first.den η))
      (fun answer => second.den (η.extend answer)) (CTy.raiseAt sig _)))
      (fun value => third.den (η.extend value)) (CTy.raiseAt sig type) =
    CTy.continue sig type (CTy.asProgram sig (first.den η))
      (fun answer => CTy.continue sig type (CTy.asProgram sig (second.den (η.extend answer)))
        (fun value => (Comp.weakenUnder third).den ((η.extend answer).extend value))
        (CTy.raiseAt sig type)) (CTy.raiseAt sig type)
  rw [continue_ret]
  unfold CTy.continue
  rw [ContextualAlgebraSequencing.sequence_bind]
  congr 1
  funext result
  cases result with
  | inl answer =>
      change ContextualAlgebraSequencing.sequence _ _ _ =
        ContextualAlgebraSequencing.sequence _ _ _
      congr 1
      funext value
      cases value with
      | inl value => exact (Comp.den_weakenUnder third answer value η).symm
      | inr raised => rfl
  | inr raised => exact ContextualAlgebraSequencing.sequence_pure _ _ _

theorem lam_app {domain : VTy sig.Ground} {type : CTy sig.Ground}
    (body : Comp sig (domain :: context) type) (argument : Val sig context domain)
    (η : Env sig context) :
    (Comp.app (.lam body) argument).den η = (body.instantiate argument).den η :=
  HeadStep.den_eq (.appLam body argument) η

theorem lam_eta {domain : VTy sig.Ground} {type : CTy sig.Ground}
    (function : Comp sig context (.arrow domain type)) (η : Env sig context) :
    (Comp.lam (.app (function.rename (Ren.weaken domain)) (.var .zero))).den η =
      function.den η := by
  funext argument
  change (function.rename (Ren.weaken domain)).den (η.extend argument) argument = _
  rw [Comp.den_rename, Env.extend_weaken]

theorem split_pair {first second : VTy sig.Ground} {type : CTy sig.Ground}
    (left : Val sig context first) (right : Val sig context second)
    (body : Comp sig (second :: first :: context) type) (η : Env sig context) :
    (Comp.split (.pair left right) body).den η = (body.subst (Subst.double left right)).den η :=
  HeadStep.den_eq (.splitPair left right body) η

/-- Algebraicity of every effect operation through every evaluation frame is
the soundness of the corresponding head step; for example `choose`: -/
theorem choose_bind {answer : VTy sig.Ground} {type : CTy sig.Ground}
    (left right : Comp sig context (.ret answer)) (body : Comp sig (answer :: context) type)
    (η : Env sig context) :
    (Comp.bind (.choose left right) body).den η =
      (Comp.choose (.bind left body) (.bind right body)).den η :=
  HeadStep.den_eq (.bindChoose left right body) η

theorem raise_bind {answer : VTy sig.Ground} {type : CTy sig.Ground} (kind : sig.Kind)
    (payload : Val sig context (.ground sig.payloadSort))
    (body : Comp sig (answer :: context) type) (η : Env sig context) :
    (Comp.bind (.raise kind payload) body).den η = (Comp.raise kind payload).den η :=
  HeadStep.den_eq (.bindRaise kind payload body) η

/-- `M to x. N` is the handler for any one kind whose raise clause raises
that kind again with the same payload. -/
theorem bind_eq_handle_reraise {answer : VTy sig.Ground} {type : CTy sig.Ground}
    (first : Comp sig context (.ret answer)) (body : Comp sig (answer :: context) type)
    (kind : sig.Kind) (η : Env sig context) :
    (Comp.bind first body).den η =
      (Comp.handle first kind body (.raise kind (.var .zero))).den η := by
  change CTy.continue sig type (first.den η) _ _ = CTy.continue sig type (first.den η) _ _
  congr 1
  funext raised
  rcases raised with ⟨raisedKind, payload⟩
  by_cases same : raisedKind = kind
  · subst same
    simp only [if_true]
    rfl
  · simp only [same, if_false]

end Equations

/-! ## Qualified reuse and discarding -/

section Strategies

variable {context : List (VTy sig.Ground)}

/-- Duplicate variable zero: the substitution behind result reuse. -/
def Subst.dup {bound : VTy sig.Ground} : Subst sig (bound :: bound :: context) (bound :: context)
  | _, .zero => .var .zero
  | _, .succ .zero => .var .zero
  | _, .succ (.succ index) => .var (.succ index)

theorem Subst.den_dup {bound : VTy sig.Ground} (value : VTy.den sig bound)
    (η : Env sig context) :
    (Subst.dup (sig := sig) (context := context) (bound := bound)).den (η.extend value) =
      (η.extend value).extend value := by
  funext type index
  rcases index with _ | ⟨_ | index⟩ <;> rfl

/-- A program that only reads and then returns an answer (never raises). -/
inductive ReturnsOnly {Answer : Type} :
    Program (State sig) (Answer ⊕ Raised sig) (Request sig) → Prop where
  | pure (answer : Answer) : ReturnsOnly (.pure (.inl answer))
  | read (next : State sig → Program (State sig) (Answer ⊕ Raised sig) (Request sig)) :
      (∀ state, ReturnsOnly (next state)) → ReturnsOnly (.read next)

omit [DecidableEq sig.Kind] in
theorem ReturnsOnly.readOnly {Answer : Type}
    {program : Program (State sig) (Answer ⊕ Raised sig) (Request sig)}
    (returns : ReturnsOnly program) : ReadOnly program := by
  induction returns with
  | pure answer => exact .pure _
  | read next _ ih => exact .read next ih

omit [DecidableEq sig.Kind] in
theorem ReturnsOnly.bind {Answer : Type}
    {program : Program (State sig) (Answer ⊕ Raised sig) (Request sig)}
    (returns : ReturnsOnly program) (state : State sig) :
    ∃ answer : Answer, ∀ {Result : Type}
      (next : Answer ⊕ Raised sig → Program (State sig) Result (Request sig))
      (branch : BranchTrace),
      runWorldsAt (program.bind next) state branch =
        runWorldsAt (next (.inl answer)) state branch := by
  induction returns with
  | pure answer => exact ⟨answer, fun _ _ => rfl⟩
  | read next _ ih =>
      obtain ⟨answer, replay⟩ := ih state
      exact ⟨answer, fun continuation branch => replay continuation branch⟩

/-- **Reuse is licensed for every read-only returner, raising or not.** The
complete ordered world observation is preserved. -/
theorem reuse_of_readOnly {answer result : VTy sig.Ground}
    (first : Comp sig context (.ret answer))
    (qualified : ∀ η, ReadOnly (CTy.asProgram sig (first.den η)))
    (body : Comp sig (answer :: answer :: context) (.ret result))
    (η : Env sig context) (state : State sig) (branch : BranchTrace) :
    runWorldsAt (CTy.asProgram sig
        ((Comp.bind first (.bind (first.rename (Ren.weaken answer)) body)).den η)) state branch =
      runWorldsAt (CTy.asProgram sig
        ((Comp.bind first (body.subst Subst.dup)).den η)) state branch := by
  obtain ⟨selected, replay⟩ := readOnly_bind _ (qualified η) state
  change runWorldsAt (CTy.asProgram sig
      (CTy.continue sig (.ret result) (CTy.asProgram sig (first.den η)) _ _))
      state branch = runWorldsAt (CTy.asProgram sig
        (CTy.continue sig (.ret result) (CTy.asProgram sig (first.den η)) _ _)) state branch
  rw [continue_ret, continue_ret, replay, replay]
  cases selected with
  | inl value =>
      change runWorldsAt (CTy.asProgram sig (CTy.continue sig (.ret result)
          (CTy.asProgram sig ((first.rename (Ren.weaken answer)).den (η.extend value))) _ _))
          state branch =
        runWorldsAt (CTy.asProgram sig ((body.subst Subst.dup).den (η.extend value))) state branch
      rw [Comp.den_rename, Env.extend_weaken, continue_ret, replay, Comp.den_subst,
        Subst.den_dup]
      rfl
  | inr raised => rfl

/-- **Discarding is licensed for read-only returners that never raise.** -/
theorem discard_of_returnsOnly {answer result : VTy sig.Ground}
    (first : Comp sig context (.ret answer))
    (qualified : ∀ η, ReturnsOnly (CTy.asProgram sig (first.den η)))
    (body : Comp sig context (.ret result)) (η : Env sig context) (state : State sig)
    (branch : BranchTrace) :
    runWorldsAt (CTy.asProgram sig
        ((Comp.bind first (body.rename (Ren.weaken answer))).den η)) state branch =
      runWorldsAt (CTy.asProgram sig (body.den η)) state branch := by
  obtain ⟨selected, replay⟩ := (qualified η).bind state
  change runWorldsAt (CTy.asProgram sig
      (CTy.continue sig (.ret result) (CTy.asProgram sig (first.den η)) _ _)) state branch = _
  rw [continue_ret, replay]
  change runWorldsAt (CTy.asProgram sig
      ((body.rename (Ren.weaken answer)).den (η.extend selected))) state branch = _
  rw [Comp.den_rename, Env.extend_weaken]

end Strategies

/-! ## Examples over a small ground signature -/

namespace Examples

/-- Two ground sorts: symbols and numbers. -/
inductive Ground where
  | sym
  | num
  deriving DecidableEq

def Data : Ground → Type
  | .sym => String
  | .num => Nat

/-- One pure primitive: successor. -/
inductive Prim : Ground → Ground → Type where
  | succ : Prim .num .num

def evalPrim : {source target : Ground} → Prim source target → Data source → Data target
  | _, _, .succ, (value : Nat) => (value + 1 : Nat)

/-- One no-value kind suffices for the controls here. -/
abbrev demo : Signature where
  Ground := Ground
  Data := Data
  stateSort := Ground.num
  intentSort := Ground.sym
  payloadSort := Ground.sym
  Kind := Unit
  Prim := Prim
  evalPrim := evalPrim

abbrev symbol (name : String) {context : List (VTy demo.Ground)} :
    Val demo context (.ground Ground.sym) :=
  .const (sig := demo) Ground.sym (name : Data Ground.sym)

abbrev v0 {context : List (VTy demo.Ground)} {type : VTy demo.Ground} :
    Val demo (type :: context) type := .var .zero

abbrev v1 {context : List (VTy demo.Ground)} {type other : VTy demo.Ground} :
    Val demo (other :: type :: context) type := .var (.succ .zero)

abbrev symT : VTy demo.Ground := .ground Ground.sym

/-- A two-way choice. -/
def coin {context : List (VTy demo.Ground)} : Comp demo context (.ret symT) :=
  .choose (.ret (symbol "heads")) (.ret (symbol "tails"))

/-- The isolated-world answers of a closed returner from state zero. -/
def answers {answer : VTy demo.Ground} (code : Comp demo [] (.ret answer)) :
    List (VTy.den demo answer ⊕ Raised demo) :=
  (runWorlds (CTy.asProgram demo (code.den Env.empty)) (0 : Nat)).map WorldResult.answer

/-- Prime's `(let $c (coin) done)`: an eager `to` with an unused binding. -/
def eagerLet : Comp demo [] (.ret symT) := .bind coin (.ret (symbol "done"))

set_option backward.isDefEq.respectTransparency false in
theorem eager_let_two_occurrences :
    answers eagerLet = [.inl ("done" : String), .inl ("done" : String)] := rfl

/-- `(k 1 coin)` with `k` returning its first argument, arguments passed as
thunks: the unused thunk is never forced. -/
def keepFirst : Comp demo [] (.arrow (.thunk (.ret symT)) (.arrow (.thunk (.ret symT)) (.ret symT))) :=
  .lam (.lam (.force v1))

def thunkedArgument : Comp demo [] (.ret symT) :=
  .app (.app keepFirst (.thunk (.ret (symbol "one")))) (.thunk coin)

set_option backward.isDefEq.respectTransparency false in
theorem thunked_argument_one_occurrence :
    answers thunkedArgument = [.inl ("one" : String)] := rfl

/-- The call-by-value translation of the same call runs the argument first. -/
def eagerArgument : Comp demo [] (.ret symT) :=
  .bind coin (.app (.lam (.ret (symbol "one"))) v0)

set_option backward.isDefEq.respectTransparency false in
theorem eager_argument_two_occurrences :
    answers eagerArgument = [.inl ("one" : String), .inl ("one" : String)] := rfl

/-- `(twice coin)` with `(= (twice $x) (P $x $x))`, the argument forced at
each use (call by name): four pairs. -/
def reforcedArgument : Comp demo [] (.ret (.prod symT symT)) :=
  .app (.lam (.bind (.force v0) (.bind (.force v1) (.ret (.pair v1 v0))))) (.thunk coin)

set_option backward.isDefEq.respectTransparency false in
theorem reforced_argument_four_pairs :
    answers reforcedArgument =
      [.inl (("heads" : String), ("heads" : String)), .inl ("heads", "tails"),
       .inl ("tails", "heads"), .inl ("tails", "tails")] := rfl

/-- The same argument evaluated once and shared: two correlated pairs. -/
def sharedArgument : Comp demo [] (.ret (.prod symT symT)) :=
  .bind coin (.app (.lam (.ret (.pair v0 v0))) v0)

set_option backward.isDefEq.respectTransparency false in
theorem shared_argument_two_pairs :
    answers sharedArgument = [.inl (("heads" : String), ("heads" : String)), .inl ("tails", "tails")] :=
  rfl

/-- Two independent choices: four occurrences. -/
def independentChoice : Comp demo [] (.ret (.prod symT symT)) :=
  .bind coin (.bind coin (.ret (.pair v1 v0)))

/-- One reused choice: two occurrences. -/
def correlatedChoice : Comp demo [] (.ret (.prod symT symT)) :=
  .bind coin (.ret (.pair v0 v0))

set_option backward.isDefEq.respectTransparency false in
theorem independent_choice_four : (answers independentChoice).length = 4 := rfl

set_option backward.isDefEq.respectTransparency false in
theorem correlated_choice_two : (answers correlatedChoice).length = 2 := rfl

/-- Reuse is not licensed for a choice. -/
theorem choice_reuse_changes_answers :
    answers independentChoice ≠ answers correlatedChoice := by
  intro equal
  have := congrArg List.length equal
  exact absurd this (by decide)

/-- **A raise is copyable but not discardable.** -/
def raiseThenConstant : Comp demo [] (.ret symT) :=
  .bind (answer := symT) (.raise () (symbol "boom")) (.ret (symbol "after"))

set_option backward.isDefEq.respectTransparency false in
theorem raise_not_discardable :
    answers raiseThenConstant = [.inr ((), ("boom" : String))] ∧
      answers (.ret (symbol "after") : Comp demo [] (.ret symT)) = [.inl ("after" : String)] :=
  ⟨rfl, rfl⟩

theorem raise_readOnly :
    ReadOnly (CTy.asProgram demo (Comp.den (sig := demo)
      (Comp.raise () (symbol "boom") : Comp demo [] (.ret symT)) Env.empty)) := .pure _

/-- A state counter: read, write the successor, return the old value. -/
def tick : Comp demo [] (.ret (.ground Ground.num)) :=
  .read (.write (.prim Prim.succ v0) (.ret v0))

set_option backward.isDefEq.respectTransparency false in
theorem tick_worlds :
    (runWorlds (CTy.asProgram demo (tick.den Env.empty)) (0 : Nat)).map
        (fun world => (world.answer, world.state)) = [(.inl (0 : Nat), (1 : Nat))] := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The complete isolated worlds of the eager `let`: branch path, answer,
state and intents. -/
theorem eagerLet_worlds :
    (runWorlds (CTy.asProgram demo (eagerLet.den Env.empty)) (0 : Nat)).map
        (fun world => (world.branch, world.answer, world.state, world.intents)) =
      [([false], .inl ("done" : String), (0 : Nat), ([] : List String)),
       ([true], .inl ("done" : String), (0 : Nat), ([] : List String))] := rfl

/-- Two alternatives, each with its own deferred intent. -/
def intentChoice : Comp demo [] (.ret symT) :=
  .choose (.intent (symbol "left") (.ret (symbol "one")))
    (.intent (symbol "right") (.ret (symbol "two")))

set_option backward.isDefEq.respectTransparency false in
theorem intentChoice_worlds :
    (runWorlds (CTy.asProgram demo (intentChoice.den Env.empty)) (0 : Nat)).map
        (fun world => (world.branch, world.answer, world.intents)) =
      [([false], .inl ("one" : String), (["left"] : List String)),
       ([true], .inl ("two" : String), (["right"] : List String))] := rfl

/-- A handler catches the raising alternative and passes the other through. -/
def handledChoice : Comp demo [] (.ret symT) :=
  .handle (.choose (.raise () (symbol "boom")) (.ret (symbol "fine"))) ()
    (.ret (.var .zero)) (.ret (symbol "caught"))

set_option backward.isDefEq.respectTransparency false in
theorem handledChoice_answers :
    answers handledChoice = [.inl ("caught" : String), .inl ("fine" : String)] := rfl

/-- An operational unfolding of the eager `let`, built from the rewrites. -/
theorem eagerLet_unfolds :
    Unfolds eagerLet (.choose (.pure (.inl (symbol "done"))) (.pure (.inl (symbol "done")))) :=
  .step (.head (.bindChoose _ _ _))
    (.choose (.step (.head (.bindRet _ _)) (.ret _)) (.step (.head (.bindRet _ _)) (.ret _)))

theorem eagerLet_observed (state : Nat) :
    runWorlds (CTy.asProgram demo (eagerLet.den Env.empty)) state =
      (runWorlds (.choose (.pure (.inl (symbol "done"))) (.pure (.inl (symbol "done"))) :
          Program (State demo) (Val demo [] symT ⊕ Raised demo) (Request demo)) state).map
        (WorldResult.mapAnswer leafDen) :=
  eagerLet_unfolds.observe state

end Examples

#print axioms bind_ret
#print axioms bind_assoc
#print axioms lam_eta
#print axioms bind_eq_handle_reraise
#print axioms reuse_of_readOnly
#print axioms discard_of_returnsOnly
#print axioms Examples.eager_let_two_occurrences
#print axioms Examples.thunked_argument_one_occurrence
#print axioms Examples.reforced_argument_four_pairs
#print axioms Examples.shared_argument_two_pairs
#print axioms Examples.choice_reuse_changes_answers
#print axioms Examples.raise_not_discardable
#print axioms Examples.eagerLet_observed
#print axioms Examples.eagerLet_worlds
#print axioms Examples.intentChoice_worlds
#print axioms Examples.handledChoice_answers

end Mettapedia.TypeTheory.ContextualCBPV
