import Mettapedia.TypeTheory.ContextualCBPVSemantics
import Mettapedia.TypeTheory.ContextualDependentSequencing
import Mettapedia.GSLT.Core.Composition

/-!
# The operational reading of contextual CBPV and its agreement with programs

The operational reading is a rewrite system on syntax, the same rules the
module presentation authors:

* `HeadStep`: thunk/force, return/`to`, lambda/application and pair
  elimination by substitution; effect operations and `raise` move outward
  through the frames `M to x. N`, `M V` and `handle M k N H` (algebraicity);
  a handler meets returns and raises;
* `Step`: head steps inside the evaluation frames `[] to x. N`, `[] V`,
  `handle [] k N H`.

A closed returner is read operationally as an effect tree (`Unfolds`): steps
until an operation or a terminal is at the top, then the same for the
operation's continuations. A `read` continuation is opened with the current
state as a constant. Leaves are syntactic values or raised no-values.

**Agreement.** Every step preserves the denotation in the existing algebra
model (`Step.den_eq`). Hence every operational unfolding is the denotation
(`Unfolds.sound`), and the isolated-world observation of the two readings is
the same ordered list of worlds: branch path, answer, state and intents
(`Unfolds.observe`). The fragment is the closed returner computations that
have an operational unfolding; `ContextualCBPVNormalization` proves that
every closed returner of this recursion-free calculus has one
(`Comp.unfolds_exists`).

The rewrites are a GSLT (`operationalGSLT`), the denotation is an
`Elaboration` of it that identifies rewrite-related terms
(`programElaboration`), and compiling a run to its program with the
`runWorlds` observer is a certified `Realization` (`operationalRealization`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCBPV

open CategoryTheory
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualDependentSequencing

variable {sig : Signature}

/-! ## The algebra action on operation nodes -/

section Action

variable (X : Alg sig)

theorem action_choose (left right : Program (State sig) X.A (Request sig)) :
    X.a (Program.choose left right) =
      X.a (Program.choose (.pure (X.a left)) (.pure (X.a right))) :=
  ContextualAlgebraSequencing.action_bind X (Program.choose (.pure left) (.pure right))
    (fun program => program)

theorem action_read (next : State sig → Program (State sig) X.A (Request sig)) :
    X.a (Program.read next) = X.a (Program.read fun state => .pure (X.a (next state))) :=
  ContextualAlgebraSequencing.action_bind X (Program.read fun state => .pure (next state))
    (fun program => program)

theorem action_write (state : State sig) (next : Program (State sig) X.A (Request sig)) :
    X.a (Program.write state next) = X.a (Program.write state (.pure (X.a next))) :=
  ContextualAlgebraSequencing.action_bind X (Program.write state (.pure next))
    (fun program => program)

theorem action_intent (request : Request sig) (next : Program (State sig) X.A (Request sig)) :
    X.a (Program.intent request next) = X.a (Program.intent request (.pure (X.a next))) :=
  ContextualAlgebraSequencing.action_bind X (Program.intent request (.pure next))
    (fun program => program)

end Action

section Continue

variable (type : CTy sig.Ground) {Answer : Type}
variable (next : Answer → (CTy.alg sig type).A) (onRaise : Raised sig → (CTy.alg sig type).A)

theorem continue_pure (answer : Answer ⊕ Raised sig) :
    CTy.continue sig type (.pure answer) next onRaise = Sum.elim next onRaise answer :=
  ContextualAlgebraSequencing.sequence_pure _ _ _

theorem continue_choose (left right : Program (State sig) (Answer ⊕ Raised sig) (Request sig)) :
    CTy.continue sig type (.choose left right) next onRaise =
      (CTy.alg sig type).a (Program.choose (.pure (CTy.continue sig type left next onRaise))
        (.pure (CTy.continue sig type right next onRaise))) :=
  action_choose (CTy.alg sig type) _ _

theorem continue_read
    (body : State sig → Program (State sig) (Answer ⊕ Raised sig) (Request sig)) :
    CTy.continue sig type (.read body) next onRaise =
      (CTy.alg sig type).a
        (Program.read fun state => .pure (CTy.continue sig type (body state) next onRaise)) :=
  action_read (CTy.alg sig type) _

theorem continue_write (state : State sig)
    (body : Program (State sig) (Answer ⊕ Raised sig) (Request sig)) :
    CTy.continue sig type (.write state body) next onRaise =
      (CTy.alg sig type).a
        (Program.write state (.pure (CTy.continue sig type body next onRaise))) :=
  action_write (CTy.alg sig type) _ _

theorem continue_intent (request : Request sig)
    (body : Program (State sig) (Answer ⊕ Raised sig) (Request sig)) :
    CTy.continue sig type (.intent request body) next onRaise =
      (CTy.alg sig type).a
        (Program.intent request (.pure (CTy.continue sig type body next onRaise))) :=
  action_intent (CTy.alg sig type) _ _

end Continue

/-! ## Rewrites -/

/-- The root rewrites of the operational reading. -/
inductive HeadStep : {context : List (VTy sig.Ground)} → {type : CTy sig.Ground} →
    Comp sig context type → Comp sig context type → Prop where
  | forceThunk {context : List (VTy sig.Ground)} {type : CTy sig.Ground}
      (body : Comp sig context type) : HeadStep (.force (.thunk body)) body
  | bindRet {context : List (VTy sig.Ground)} {answer : VTy sig.Ground} {type : CTy sig.Ground}
      (value : Val sig context answer) (body : Comp sig (answer :: context) type) :
      HeadStep (.bind (.ret value) body) (body.instantiate value)
  | appLam {context : List (VTy sig.Ground)} {domain : VTy sig.Ground} {type : CTy sig.Ground}
      (body : Comp sig (domain :: context) type) (argument : Val sig context domain) :
      HeadStep (.app (.lam body) argument) (body.instantiate argument)
  | splitPair {context : List (VTy sig.Ground)} {first second : VTy sig.Ground}
      {type : CTy sig.Ground} (left : Val sig context first) (right : Val sig context second)
      (body : Comp sig (second :: first :: context) type) :
      HeadStep (.split (.pair left right) body) (body.subst (Subst.double left right))
  | bindChoose {context : List (VTy sig.Ground)} {answer : VTy sig.Ground}
      {type : CTy sig.Ground} (left right : Comp sig context (.ret answer))
      (body : Comp sig (answer :: context) type) :
      HeadStep (.bind (.choose left right) body) (.choose (.bind left body) (.bind right body))
  | bindRead {context : List (VTy sig.Ground)} {answer : VTy sig.Ground} {type : CTy sig.Ground}
      (first : Comp sig (.ground sig.stateSort :: context) (.ret answer))
      (body : Comp sig (answer :: context) type) :
      HeadStep (.bind (.read first) body) (.read (.bind first (Comp.weakenUnder body)))
  | bindWrite {context : List (VTy sig.Ground)} {answer : VTy sig.Ground}
      {type : CTy sig.Ground} (state : Val sig context (.ground sig.stateSort))
      (first : Comp sig context (.ret answer)) (body : Comp sig (answer :: context) type) :
      HeadStep (.bind (.write state first) body) (.write state (.bind first body))
  | bindIntent {context : List (VTy sig.Ground)} {answer : VTy sig.Ground}
      {type : CTy sig.Ground} (request : Val sig context (.ground sig.intentSort))
      (first : Comp sig context (.ret answer)) (body : Comp sig (answer :: context) type) :
      HeadStep (.bind (.intent request first) body) (.intent request (.bind first body))
  | bindRaise {context : List (VTy sig.Ground)} {answer : VTy sig.Ground}
      {type : CTy sig.Ground} (kind : sig.Kind)
      (payload : Val sig context (.ground sig.payloadSort))
      (body : Comp sig (answer :: context) type) :
      HeadStep (.bind (.raise kind payload) body) (.raise kind payload)
  | appChoose {context : List (VTy sig.Ground)} {domain : VTy sig.Ground}
      {type : CTy sig.Ground} (left right : Comp sig context (.arrow domain type))
      (argument : Val sig context domain) :
      HeadStep (.app (.choose left right) argument) (.choose (.app left argument) (.app right argument))
  | appRead {context : List (VTy sig.Ground)} {domain : VTy sig.Ground} {type : CTy sig.Ground}
      (function : Comp sig (.ground sig.stateSort :: context) (.arrow domain type))
      (argument : Val sig context domain) :
      HeadStep (.app (.read function) argument)
        (.read (.app function (argument.rename (Ren.weaken _))))
  | appWrite {context : List (VTy sig.Ground)} {domain : VTy sig.Ground}
      {type : CTy sig.Ground} (state : Val sig context (.ground sig.stateSort))
      (function : Comp sig context (.arrow domain type)) (argument : Val sig context domain) :
      HeadStep (.app (.write state function) argument) (.write state (.app function argument))
  | appIntent {context : List (VTy sig.Ground)} {domain : VTy sig.Ground}
      {type : CTy sig.Ground} (request : Val sig context (.ground sig.intentSort))
      (function : Comp sig context (.arrow domain type)) (argument : Val sig context domain) :
      HeadStep (.app (.intent request function) argument) (.intent request (.app function argument))
  | appRaise {context : List (VTy sig.Ground)} {domain : VTy sig.Ground}
      {type : CTy sig.Ground} (kind : sig.Kind)
      (payload : Val sig context (.ground sig.payloadSort)) (argument : Val sig context domain) :
      HeadStep (.app (.raise (type := .arrow domain type) kind payload) argument)
        (.raise kind payload)
  | handleRet {context : List (VTy sig.Ground)} {answer : VTy sig.Ground}
      {type : CTy sig.Ground} (value : Val sig context answer) (kind : sig.Kind)
      (onReturn : Comp sig (answer :: context) type)
      (onRaise : Comp sig (.ground sig.payloadSort :: context) type) :
      HeadStep (.handle (.ret value) kind onReturn onRaise) (onReturn.instantiate value)
  | handleCaught {context : List (VTy sig.Ground)} {answer : VTy sig.Ground}
      {type : CTy sig.Ground} (kind : sig.Kind)
      (payload : Val sig context (.ground sig.payloadSort))
      (onReturn : Comp sig (answer :: context) type)
      (onRaise : Comp sig (.ground sig.payloadSort :: context) type) :
      HeadStep (.handle (.raise kind payload) kind onReturn onRaise) (onRaise.instantiate payload)
  | handleOther {context : List (VTy sig.Ground)} {answer : VTy sig.Ground}
      {type : CTy sig.Ground} {raised kind : sig.Kind}
      (payload : Val sig context (.ground sig.payloadSort))
      (onReturn : Comp sig (answer :: context) type)
      (onRaise : Comp sig (.ground sig.payloadSort :: context) type) (different : raised ≠ kind) :
      HeadStep (.handle (.raise raised payload) kind onReturn onRaise) (.raise raised payload)
  | handleChoose {context : List (VTy sig.Ground)} {answer : VTy sig.Ground}
      {type : CTy sig.Ground} (left right : Comp sig context (.ret answer)) (kind : sig.Kind)
      (onReturn : Comp sig (answer :: context) type)
      (onRaise : Comp sig (.ground sig.payloadSort :: context) type) :
      HeadStep (.handle (.choose left right) kind onReturn onRaise)
        (.choose (.handle left kind onReturn onRaise) (.handle right kind onReturn onRaise))
  | handleRead {context : List (VTy sig.Ground)} {answer : VTy sig.Ground}
      {type : CTy sig.Ground} (first : Comp sig (.ground sig.stateSort :: context) (.ret answer))
      (kind : sig.Kind) (onReturn : Comp sig (answer :: context) type)
      (onRaise : Comp sig (.ground sig.payloadSort :: context) type) :
      HeadStep (.handle (.read first) kind onReturn onRaise)
        (.read (.handle first kind (Comp.weakenUnder onReturn) (Comp.weakenUnder onRaise)))
  | handleWrite {context : List (VTy sig.Ground)} {answer : VTy sig.Ground}
      {type : CTy sig.Ground} (state : Val sig context (.ground sig.stateSort))
      (first : Comp sig context (.ret answer)) (kind : sig.Kind)
      (onReturn : Comp sig (answer :: context) type)
      (onRaise : Comp sig (.ground sig.payloadSort :: context) type) :
      HeadStep (.handle (.write state first) kind onReturn onRaise)
        (.write state (.handle first kind onReturn onRaise))
  | handleIntent {context : List (VTy sig.Ground)} {answer : VTy sig.Ground}
      {type : CTy sig.Ground} (request : Val sig context (.ground sig.intentSort))
      (first : Comp sig context (.ret answer)) (kind : sig.Kind)
      (onReturn : Comp sig (answer :: context) type)
      (onRaise : Comp sig (.ground sig.payloadSort :: context) type) :
      HeadStep (.handle (.intent request first) kind onReturn onRaise)
        (.intent request (.handle first kind onReturn onRaise))

/-- A head step inside the evaluation frames `[] to x. N`, `[] V` and
`handle [] k N H`. -/
inductive Step : {context : List (VTy sig.Ground)} → {type : CTy sig.Ground} →
    Comp sig context type → Comp sig context type → Prop where
  | head {context : List (VTy sig.Ground)} {type : CTy sig.Ground}
      {source target : Comp sig context type} : HeadStep source target → Step source target
  | bindLeft {context : List (VTy sig.Ground)} {answer : VTy sig.Ground} {type : CTy sig.Ground}
      {source target : Comp sig context (.ret answer)} (body : Comp sig (answer :: context) type) :
      Step source target → Step (.bind source body) (.bind target body)
  | appLeft {context : List (VTy sig.Ground)} {domain : VTy sig.Ground} {type : CTy sig.Ground}
      {source target : Comp sig context (.arrow domain type)} (argument : Val sig context domain) :
      Step source target → Step (.app source argument) (.app target argument)
  | handleLeft {context : List (VTy sig.Ground)} {answer : VTy sig.Ground}
      {type : CTy sig.Ground} {source target : Comp sig context (.ret answer)} (kind : sig.Kind)
      (onReturn : Comp sig (answer :: context) type)
      (onRaise : Comp sig (.ground sig.payloadSort :: context) type) :
      Step source target →
        Step (.handle source kind onReturn onRaise) (.handle target kind onReturn onRaise)

/-! ## Every rewrite preserves the denotation -/

variable [DecidableEq sig.Kind]

theorem HeadStep.den_eq {context : List (VTy sig.Ground)} {type : CTy sig.Ground}
    {source target : Comp sig context type} (step : HeadStep source target)
    (η : Env sig context) : source.den η = target.den η := by
  cases step with
  | forceThunk body => rfl
  | bindRet value body =>
      rw [Comp.den_instantiate]
      exact continue_pure _ _ _ _
  | appLam body argument =>
      rw [Comp.den_instantiate]
      rfl
  | splitPair left right body =>
      rw [Comp.den_subst, Subst.den_double]
      rfl
  | bindChoose left right body =>
      exact continue_choose _ _ _ _ _
  | bindRead first body =>
      change CTy.continue sig _
          (Program.read fun state => CTy.asProgram sig (first.den (η.extend (VTy.ofData sig state))))
          _ _ =
        (CTy.alg sig _).a (Program.read fun state => .pure (CTy.continue sig _
          (CTy.asProgram sig (first.den (η.extend (VTy.ofData sig state))))
          (fun answer => (Comp.weakenUnder body).den
            ((η.extend (VTy.ofData sig state)).extend answer))
          (CTy.raiseAt sig _)))
      rw [continue_read]
      congr 2
      funext state
      congr 2
      funext answer
      exact (Comp.den_weakenUnder body (VTy.ofData sig state) answer η).symm
  | bindWrite state first body => exact continue_write _ _ _ _ _
  | bindIntent request first body => exact continue_intent _ _ _ _ _
  | bindRaise kind payload body => exact continue_pure _ _ _ _
  | appChoose left right argument => rfl
  | appRead function argument =>
      change (CTy.alg sig _).a (Program.read fun state =>
          .pure (Comp.den function (η.extend (VTy.ofData sig state)) (argument.den η))) =
        (CTy.alg sig _).a (Program.read fun state =>
          .pure (Comp.den function (η.extend (VTy.ofData sig state))
            (Val.den (argument.rename (Ren.weaken _)) (η.extend (VTy.ofData sig state)))))
      congr 2
      funext state
      rw [Val.den_rename, Env.extend_weaken]
  | appWrite state function argument => rfl
  | appIntent request function argument => rfl
  | appRaise kind payload argument => rfl
  | handleRet value kind onReturn onRaise =>
      rw [Comp.den_instantiate]
      exact continue_pure _ _ _ _
  | handleCaught kind payload onReturn onRaise =>
      rw [Comp.den_instantiate]
      refine (continue_pure _ _ _ _).trans ?_
      simp
  | handleOther payload onReturn onRaise different =>
      refine (continue_pure _ _ _ _).trans ?_
      simp [different]
      rfl
  | handleChoose left right kind onReturn onRaise => exact continue_choose _ _ _ _ _
  | handleRead first kind onReturn onRaise =>
      change CTy.continue sig _
          (Program.read fun state => CTy.asProgram sig (first.den (η.extend (VTy.ofData sig state))))
          _ _ =
        (CTy.alg sig _).a (Program.read fun state => .pure (CTy.continue sig _
          (CTy.asProgram sig (first.den (η.extend (VTy.ofData sig state))))
          (fun answer => (Comp.weakenUnder onReturn).den
            ((η.extend (VTy.ofData sig state)).extend answer))
          (fun raised => if raised.1 = kind then (Comp.weakenUnder onRaise).den
              ((η.extend (VTy.ofData sig state)).extend (VTy.ofData sig raised.2))
            else CTy.raiseAt sig _ raised)))
      rw [continue_read]
      congr 2
      funext state
      congr 2
      · funext answer
        exact (Comp.den_weakenUnder onReturn (VTy.ofData sig state) answer η).symm
      · funext raised
        split
        · exact (Comp.den_weakenUnder onRaise (VTy.ofData sig state)
            (VTy.ofData sig raised.2) η).symm
        · rfl
  | handleWrite state first kind onReturn onRaise => exact continue_write _ _ _ _ _
  | handleIntent request first kind onReturn onRaise => exact continue_intent _ _ _ _ _

theorem Step.den_eq {context : List (VTy sig.Ground)} {type : CTy sig.Ground}
    {source target : Comp sig context type} (step : Step source target) :
    ∀ η : Env sig context, source.den η = target.den η := by
  induction step with
  | head step => exact HeadStep.den_eq step
  | bindLeft body _ ih =>
      intro η
      simp only [Comp.den, ih η]
  | appLeft argument _ ih =>
      intro η
      simp only [Comp.den, ih η]
  | handleLeft kind onReturn onRaise _ ih =>
      intro η
      simp only [Comp.den, ih η]

/-! ## The operational effect tree of a closed returner -/

/-- The denotation of a closed value. -/
abbrev Val.closedDen {type : VTy sig.Ground} (value : Val sig [] type) : VTy.den sig type :=
  value.den Env.empty

/-- Operational unfolding of a closed returner into an effect tree with
syntactic answers. -/
inductive Unfolds {answer : VTy sig.Ground} :
    Comp sig [] (.ret answer) →
      Program (State sig) (Val sig [] answer ⊕ Raised sig) (Request sig) → Prop where
  | step {source target : Comp sig [] (.ret answer)}
      {tree : Program (State sig) (Val sig [] answer ⊕ Raised sig) (Request sig)} :
      Step source target → Unfolds target tree → Unfolds source tree
  | ret (value : Val sig [] answer) : Unfolds (.ret value) (.pure (.inl value))
  | raise (kind : sig.Kind) (payload : Val sig [] (.ground sig.payloadSort)) :
      Unfolds (.raise kind payload) (.pure (.inr (kind, VTy.toData sig payload.closedDen)))
  | choose {left right : Comp sig [] (.ret answer)}
      {leftTree rightTree : Program (State sig) (Val sig [] answer ⊕ Raised sig) (Request sig)} :
      Unfolds left leftTree → Unfolds right rightTree →
        Unfolds (.choose left right) (.choose leftTree rightTree)
  | read {body : Comp sig [.ground sig.stateSort] (.ret answer)}
      {trees : State sig → Program (State sig) (Val sig [] answer ⊕ Raised sig) (Request sig)} :
      (∀ state : State sig, Unfolds (body.instantiate (.const _ state)) (trees state)) →
        Unfolds (.read body) (.read trees)
  | write {state : Val sig [] (.ground sig.stateSort)} {next : Comp sig [] (.ret answer)}
      {tree : Program (State sig) (Val sig [] answer ⊕ Raised sig) (Request sig)} :
      Unfolds next tree → Unfolds (.write state next) (.write (VTy.toData sig state.closedDen) tree)
  | intent {request : Val sig [] (.ground sig.intentSort)} {next : Comp sig [] (.ret answer)}
      {tree : Program (State sig) (Val sig [] answer ⊕ Raised sig) (Request sig)} :
      Unfolds next tree →
        Unfolds (.intent request next) (.intent (VTy.toData sig request.closedDen) tree)

/-- Read the syntactic leaves of an operational tree as values. -/
def leafDen {answer : VTy sig.Ground} :
    Val sig [] answer ⊕ Raised sig → VTy.den sig answer ⊕ Raised sig :=
  Sum.map Val.closedDen id

/-- **Agreement.** The operational effect tree of a closed returner is its
denotation in the existing algebra model, leaf by leaf. -/
theorem Unfolds.sound {answer : VTy sig.Ground} {code : Comp sig [] (.ret answer)}
    {tree : Program (State sig) (Val sig [] answer ⊕ Raised sig) (Request sig)}
    (unfolds : Unfolds code tree) : Program.map leafDen tree = code.den Env.empty := by
  induction unfolds with
  | step step _ ih => exact ih.trans (Step.den_eq step Env.empty).symm
  | ret value => rfl
  | raise kind payload => rfl
  | choose _ _ leftIH rightIH =>
      change Program.choose (Program.map leafDen _) (Program.map leafDen _) = _
      rw [leftIH, rightIH]
      rfl
  | read _ ih =>
      change Program.read (fun state => Program.map leafDen _) = _
      simp only [ih, Comp.den_instantiate]
      rfl
  | write _ ih =>
      change Program.write _ (Program.map leafDen _) = _
      rw [ih]
      rfl
  | intent _ ih =>
      change Program.intent _ (Program.map leafDen _) = _
      rw [ih]
      rfl

/-- **Agreement of observations.** The isolated-world observation of the
operational tree, with leaves read as values, is the observation of the
denotation: the same ordered branch paths, answers, states and intents. -/
theorem Unfolds.observe {answer : VTy sig.Ground} {code : Comp sig [] (.ret answer)}
    {tree : Program (State sig) (Val sig [] answer ⊕ Raised sig) (Request sig)}
    (unfolds : Unfolds code tree) (state : State sig) :
    runWorlds (code.den Env.empty) state =
      (runWorlds tree state).map (WorldResult.mapAnswer leafDen) := by
  rw [← unfolds.sound]
  exact runWorldsAt_map leafDen tree state []

/-- Two operational unfoldings of one computation are observed alike. -/
theorem Unfolds.observe_unique {answer : VTy sig.Ground} {code : Comp sig [] (.ret answer)}
    {first second : Program (State sig) (Val sig [] answer ⊕ Raised sig) (Request sig)}
    (firstUnfolds : Unfolds code first) (secondUnfolds : Unfolds code second) :
    Program.map leafDen first = Program.map leafDen second :=
  firstUnfolds.sound.trans secondUnfolds.sound.symm

/-! ## GSLT, elaboration and realization -/

/-- Closed computations of any computation type. -/
abbrev Closed (sig : Signature) := Σ type : CTy sig.Ground, Comp sig [] type

/-- The rewrites on closed computations. -/
inductive ClosedStep : Closed sig → Closed sig → Prop where
  | intro {type : CTy sig.Ground} {source target : Comp sig [] type} :
      Step source target → ClosedStep ⟨type, source⟩ ⟨type, target⟩

/-- The operational reading as a GSLT: closed computations, syntactic
equality (de Bruijn syntax has no separate alpha equivalence), the rewrites. -/
def operationalGSLT (sig : Signature) : Mettapedia.GSLT.GSLT where
  Term := Closed sig
  equations := { r := Eq, iseqv := eq_equivalence }
  rewrites := ClosedStep
  rewrites_resp_left := by
    intro source other target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  rewrites_resp_right := by
    intro source target other step equal
    exact equal ▸ step

/-- **The program semantics is an elaboration of the operational GSLT**: it
cannot distinguish two closed computations related by a rewrite. -/
def programElaboration (sig : Signature) [DecidableEq sig.Kind] :
    Mettapedia.GSLT.GSLT.Elaboration (operationalGSLT sig)
      (Σ type : CTy sig.Ground, (CTy.alg sig type).A) where
  elaborate := fun closed => some ⟨closed.1, closed.2.den Env.empty⟩
  equation := by
    intro left right equal
    cases equal
    rfl
  rewrite := by
    intro left right step
    cases step with
    | intro step => simp only [Step.den_eq step Env.empty]

/-- A closed returner with an operational unfolding. -/
structure Run (sig : Signature) [DecidableEq sig.Kind] (answer : VTy sig.Ground) where
  code : Comp sig [] (.ret answer)
  tree : Program (State sig) (Val sig [] answer ⊕ Raised sig) (Request sig)
  unfolds : Unfolds code tree

/-- **Certified realization.** Compiling a run to the denotation and observing
it with `runWorlds` agrees exactly with observing the operational tree. -/
def operationalRealization (sig : Signature) [DecidableEq sig.Kind] :
    Mettapedia.GSLT.Realization (Run sig)
      (fun answer => Program (State sig) (VTy.den sig answer ⊕ Raised sig) (Request sig))
      (fun answer => State sig →
        List (WorldResult (State sig) (VTy.den sig answer ⊕ Raised sig) (Request sig))) where
  compile := fun _ run => run.code.den Env.empty
  observeSource := fun _ run state => (runWorlds run.tree state).map (WorldResult.mapAnswer leafDen)
  observeArtifact := fun _ program state => runWorlds program state
  adequate := by
    intro answer run
    funext state
    exact run.unfolds.observe state

#print axioms HeadStep.den_eq
#print axioms Step.den_eq
#print axioms Unfolds.sound
#print axioms Unfolds.observe
#print axioms programElaboration
#print axioms operationalRealization

end Mettapedia.TypeTheory.ContextualCBPV
