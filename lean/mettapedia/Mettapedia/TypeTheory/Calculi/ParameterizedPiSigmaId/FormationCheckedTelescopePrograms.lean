import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionPaths
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeArgumentChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTelescopeSpine

/-!
# Formed dependent programs and retained certificate return

The same argument-checking fold earns formation-sensitive substitutions when
its primitive evidence semantics is formation-sensitive. Source and target
context formation are retained separately; neither is inferred from matching.

Closing a formed telescope also requires universe joins. That capability is
an explicit theorem parameter, not another field of the language definition.
The cumulative tower supplies it by its actual maximum-level join rule.

Checked projections close to actual lambda programs, execute by directed beta
steps, and return the value certified by the retained input tree. The returned
tree can be rechecked in the unchanged target context. This is not compulsory
second checking, unrestricted reflection, or verification of the C loaders.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationCheckedTelescopePrograms

open FormationSensitive TelescopeAbstraction TelescopeArgumentChecking

variable {Head Evidence : Type} {R : Rules Head} {n m : Nat}

/-- A closed formed term weakens into any target context. Its declaration
and type remain closed under the actual renaming operation. -/
theorem liftClosed_typing {term type : Tm Head 0}
    (typed : Typing R .nil term type) (target : Ctx Head n) :
    Typing R target (liftClosed term) (liftClosed type) :=
  typed.renameTyping (ρ := Fin.elim0) (fun index => Fin.elim0 index)

/-- Closure forms all products in the original telescope order. -/
theorem close_formed
    (joins : ∀ {u v}, R.isUniverse u → R.isUniverse v →
      ∃ w, R.isUniverse w ∧ R.join u v w)
    {context : Ctx Head n} (contextFormation : ContextFormation R context)
    {type : Tm Head n} {u : Head}
    (formed : Typing R context type (.head u)) (isUniverse : R.isUniverse u) :
    ∃ v, R.isUniverse v ∧ Typing R .nil (closeType context type) (.head v) := by
  induction contextFormation generalizing u with
  | nil => exact ⟨u, isUniverse, formed⟩
  | @snoc n prior domain domainUniverse priorFormation domainFormation domainIsUniverse ih =>
      obtain ⟨v, isV, joined⟩ := joins domainIsUniverse isUniverse
      exact ih (.piForm domainFormation domainIsUniverse formed isUniverse joined) isV

/-- Every lambda introduction retains the formation of its actual product.
Raw lambda typing alone cannot establish this theorem. -/
theorem close_typed
    (universes : UniverseRegularity R)
    (joins : ∀ {u v}, R.isUniverse u → R.isUniverse v →
      ∃ w, R.isUniverse w ∧ R.join u v w)
    {context : Ctx Head n} (contextFormation : ContextFormation R context)
    {body type : Tm Head n} (typing : Typing R context body type) :
    Typing R .nil (closeTerm context body) (closeType context type) := by
  induction contextFormation with
  | nil => exact typing
  | @snoc n prior domain domainUniverse priorFormation domainFormation domainIsUniverse ih =>
      have current : ContextFormation R (.snoc prior domain) :=
        .snoc priorFormation domainFormation domainIsUniverse
      obtain ⟨v, isV, typeFormation⟩ := typing.regularity universes current
      obtain ⟨w, isW, joined⟩ := joins domainIsUniverse isV
      exact ih (.lamIntro
        (.piForm domainFormation domainIsUniverse typeFormation isV joined) isW typing)

/-- Accepted certificates earn the existing refined context morphism. -/
theorem checked_substitution
    {target : Ctx Head m}
    (check : Tm Head m → Tm Head m → Evidence → Bool)
    (checkSound : ∀ argument domain evidence,
      check argument domain evidence = true → Typing R target argument domain)
    {context : Ctx Head n} {sigma : Sub Head n m} {evidence : Fin n → Evidence}
    (accepted : checkArguments check context sigma evidence = true) :
    FormationSensitive.CtxMor R context target sigma := by
  intro index
  exact checkSound _ _ _
    ((checkArguments_eq_true_iff check context sigma evidence).1 accepted index)

/-- The very same checked argument assignment types the actual application. -/
theorem apply_typed
    {context : Ctx Head n} {target : Ctx Head m}
    {sigma : Sub Head n m} {type : Tm Head n} {function : Tm Head m}
    (typed : FormationSensitive.CtxMor R context target sigma)
    (functionTyping : Typing R target function (liftClosed (closeType context type))) :
    Typing R target (applyClosed context sigma function) (subst sigma type) := by
  induction context with
  | nil => simpa only [applyClosed, closeType, subst_empty] using functionTyping
  | snoc prior domain ih =>
      have earlier := ih typed.dropNewest functionTyping
      have newest := typed 0
      simp only [Ctx.lookup_snoc_zero, subst_prior] at newest
      simpa only [applyClosed, subst, subst_open] using (Typing.appElim earlier newest)

/-- The formed closed abstraction can be placed in any target context by
the existing empty-source substitution, with no new declaration or carrier. -/
theorem close_into_target
    (universes : UniverseRegularity R)
    (joins : ∀ {u v}, R.isUniverse u → R.isUniverse v →
      ∃ w, R.isUniverse w ∧ R.join u v w)
    {context : Ctx Head n} {body type : Tm Head n}
    (source : Judgment R context body type) {target : Ctx Head m} :
    Typing R target (liftClosed (closeTerm context body))
      (liftClosed (closeType context type)) := by
  have emptyTyped : FormationSensitive.CtxMor R (.nil : Ctx Head 0) target
      (renSub Fin.elim0) := by
    intro index
    exact Fin.elim0 index
  simpa only [subst_renSub, liftClosed] using
    (close_typed universes joins source.context source.typing).substitute emptyTyped

/-- Formed source evidence closes, applies, and computes without changing
the body, its displayed type, or the supplied simultaneous substitution. -/
theorem checked_program
    (universes : UniverseRegularity R)
    (joins : ∀ {u v}, R.isUniverse u → R.isUniverse v →
      ∃ w, R.isUniverse w ∧ R.join u v w)
    {target : Ctx Head m} (targetFormation : ContextFormation R target)
    (check : Tm Head m → Tm Head m → Evidence → Bool)
    (checkSound : ∀ argument domain evidence,
      check argument domain evidence = true → Typing R target argument domain)
    {context : Ctx Head n} {sigma : Sub Head n m} {evidence : Fin n → Evidence}
    {body type : Tm Head n} (source : Judgment R context body type)
    (accepted : checkArguments check context sigma evidence = true) :
    Judgment R target
        (applyClosed context sigma (liftClosed (closeTerm context body)))
        (subst sigma type) ∧
      Judgment R target (subst sigma body) (subst sigma type) ∧
      BetaSteps (applyClosed context sigma (liftClosed (closeTerm context body)))
        (subst sigma body) := by
  have typed := checked_substitution check checkSound accepted
  have lifted := close_into_target universes joins source (target := target)
  exact ⟨⟨targetFormation, apply_typed typed lifted⟩,
    source.substitute targetFormation typed, applyClosed_beta context sigma body⟩

/-- Math-to-program-to-math for arbitrary dependent projections: the
returned value has the exact type and certificate of the chosen argument. -/
theorem checked_projection_loop
    (universes : UniverseRegularity R)
    (joins : ∀ {u v}, R.isUniverse u → R.isUniverse v →
      ∃ w, R.isUniverse w ∧ R.join u v w)
    {context : Ctx Head n} (sourceFormation : ContextFormation R context)
    {target : Ctx Head m} (targetFormation : ContextFormation R target)
    (check : Tm Head m → Tm Head m → Evidence → Bool)
    (checkSound : ∀ argument domain evidence,
      check argument domain evidence = true → Typing R target argument domain)
    {sigma : Sub Head n m} {evidence : Fin n → Evidence}
    (accepted : checkArguments check context sigma evidence = true) (index : Fin n) :
    Judgment R target
        (applyClosed context sigma (liftClosed (closeTerm context (.var index))))
        (subst sigma (Ctx.lookup context index)) ∧
      Judgment R target (sigma index) (subst sigma (Ctx.lookup context index)) ∧
      BetaSteps
        (applyClosed context sigma (liftClosed (closeTerm context (.var index))))
        (sigma index) ∧
      check (sigma index) (subst sigma (Ctx.lookup context index)) (evidence index) = true := by
  have source : Judgment R context (.var index) (Ctx.lookup context index) :=
    ⟨sourceFormation, .var index⟩
  obtain ⟨program, result, execution⟩ :=
    checked_program universes joins targetFormation check checkSound source accepted
  exact ⟨program, result, execution,
    (checkArguments_eq_true_iff check context sigma evidence).1 accepted index⟩

/-- Feed an actually typed program result into the next invocation. Its
typing is earned by the first invocation, not assumed from a raw certificate
for an unreduced term. The same original tree certifies the final value. -/
theorem checked_return_then_consume
    (universes : UniverseRegularity R)
    (joins : ∀ {u v}, R.isUniverse u → R.isUniverse v →
      ∃ w, R.isUniverse w ∧ R.join u v w)
    {prior : Ctx Head n} {domain : Tm Head n}
    (sourceFormation : ContextFormation R (.snoc prior domain))
    {target : Ctx Head m} (targetFormation : ContextFormation R target)
    (check : Tm Head m → Tm Head m → Evidence → Bool)
    (checkSound : ∀ argument domain evidence,
      check argument domain evidence = true → Typing R target argument domain)
    {sigma : Sub Head (n + 1) m} {evidence : Fin (n + 1) → Evidence}
    (accepted : checkArguments check (.snoc prior domain) sigma evidence = true) :
    let function := liftClosed (closeTerm (.snoc prior domain) (.var 0))
    let returned := applyClosed (.snoc prior domain) sigma function
    let feedback := consSub returned (fun index => sigma index.succ)
    Judgment R target (applyClosed (.snoc prior domain) feedback function)
        (subst sigma (Ctx.lookup (.snoc prior domain) 0)) ∧
      BetaSteps (applyClosed (.snoc prior domain) feedback function) (sigma 0) ∧
      check (sigma 0) (subst sigma (Ctx.lookup (.snoc prior domain) 0)) (evidence 0) = true := by
  dsimp only
  obtain ⟨first, _, firstSteps, retained⟩ :=
    checked_projection_loop universes joins sourceFormation targetFormation check checkSound accepted 0
  have initial := checked_substitution check checkSound accepted
  have returnedTyping : Typing R target
      (applyClosed (.snoc prior domain) sigma
        (liftClosed (closeTerm (.snoc prior domain) (.var 0))))
      (subst (fun index => sigma index.succ) domain) := by
    simpa only [Ctx.lookup_snoc_zero, subst_prior] using first.typing
  have feedback := initial.dropNewest.extend returnedTyping
  have function := close_into_target universes joins
    (⟨sourceFormation, Typing.var 0⟩ : Judgment R (.snoc prior domain) (.var 0)
      (Ctx.lookup (.snoc prior domain) 0)) (target := target)
  have second := apply_typed feedback function
  have secondSteps := applyClosed_beta (.snoc prior domain)
    (consSub
      (applyClosed (.snoc prior domain) sigma
        (liftClosed (closeTerm (.snoc prior domain) (.var 0))))
      (fun index => sigma index.succ)) (.var 0)
  refine ⟨⟨targetFormation, ?_⟩, secondSteps.trans firstSteps, retained⟩
  simpa only [Ctx.lookup_snoc_zero, subst_prior, consSub_succ] using second

open StructuralConversionCode

/-- Emit the existing structural conversion code for applying one closed
telescope. Every step is beta, possibly under the remaining applications.
No authored root code or head equation is used, so the code may be
embedded in any root-code family. -/
def applicationCodeIn {RootCode : Nat → Type} : {n : Nat} → (context : Ctx Head n) → Sub Head n m →
    Tm Head n → Code Head RootCode m
  | _, .nil, _, term => .refl (liftClosed term)
  | _, .snoc prior _, sigma, term =>
      .trans
        (Code.mapContext (fun function => .app function (sigma 0))
          (fun step => .congAppFun step (sigma 0))
          (applicationCodeIn prior (fun index => sigma index.succ) (.lam term)))
        (.single (.betaPi (subst (liftSub (fun index => sigma index.succ)) term) (sigma 0)))

theorem applicationCodeIn_checked [DecidableEq Head] {RootCode : Nat → Type}
    (headEq : Head → Head → Prop) [DecidableRel headEq]
    (decode : {scope : Nat} → RootCode scope → Option (Tm Head scope × Tm Head scope))
    (context : Ctx Head n) (sigma : Sub Head n m) (term : Tm Head n) :
    (applicationCodeIn context sigma term).check headEq decode
      (applyClosed context sigma (liftClosed (closeTerm context term)))
      (subst sigma term) = true := by
  induction context with
  | nil =>
      simpa only [applicationCodeIn, closeTerm, applyClosed, subst_empty] using
        Code.check_refl headEq decode (liftClosed term : Tm Head m)
  | snoc prior domain ih =>
      have earlier := ih (sigma := fun index => sigma index.succ) (term := .lam term)
      have underApplication := Code.check_mapContext headEq decode
        (fun function => .app function (sigma 0)) (fun step => .congAppFun step (sigma 0))
        (fun _ => rfl) earlier
      have beta : Code.check headEq decode
          (.single (.betaPi (subst (liftSub (fun index => sigma index.succ)) term) (sigma 0)))
          (.app (.lam (subst (liftSub (fun index => sigma index.succ)) term)) (sigma 0))
          (subst sigma term) = true := by
        simp only [Code.check, Code.decode, StepCode.decode, subst_open, decide_true]
      simpa only [applicationCodeIn, closeTerm, applyClosed, subst] using
        Code.check_trans headEq decode underApplication beta

def applicationCode (context : Ctx Head n) (sigma : Sub Head n m) (term : Tm Head n) :
    Code Head (fun _ => Empty) m := applicationCodeIn context sigma term

abbrev noRoot : {n : Nat} → Empty → Option (Tm Head n × Tm Head n) :=
  (RootDecoder.ofEmpty (RootComputation.empty : RootComputation Head) rfl).decode

theorem applicationCode_checked [DecidableEq Head]
    (context : Ctx Head n) (sigma : Sub Head n m) (term : Tm Head n) :
    (applicationCode context sigma term).check (fun _ _ => False) noRoot
      (applyClosed context sigma (liftClosed (closeTerm context term)))
      (subst sigma term) = true :=
  applicationCodeIn_checked (fun _ _ => False) noRoot context sigma term

/-- This counts selected beta occurrences. It does not count term copying,
decoder comparisons, or the machine instructions implementing those tasks. -/
theorem applicationCodeIn_stepCount {RootCode : Nat → Type}
    (context : Ctx Head n) (sigma : Sub Head n m) (term : Tm Head n) :
    (applicationCodeIn (RootCode := RootCode) context sigma term).stepCount = n := by
  induction context with
  | nil => rfl
  | snoc prior domain ih =>
      simp only [applicationCodeIn, Code.stepCount, Code.stepCount_mapContext, ih]

theorem applicationCode_stepCount
    (context : Ctx Head n) (sigma : Sub Head n m) (term : Tm Head n) :
    (applicationCode context sigma term).stepCount = n :=
  applicationCodeIn_stepCount context sigma term

/-- Lift a supplied function conversion under the actual argument spine.
Argument order is the telescope order, including repeated arguments. -/
def applyFunctionCode {RootCode : Nat → Type} :
    {n : Nat} → Ctx Head n → Sub Head n m → Code Head RootCode m → Code Head RootCode m
  | _, .nil, _, code => code
  | _, .snoc prior _, sigma, code =>
      Code.mapContext (fun function => .app function (sigma 0))
        (fun step => .congAppFun step (sigma 0))
        (applyFunctionCode prior (fun index => sigma index.succ) code)

theorem applyFunctionCode_checked [DecidableEq Head] {RootCode : Nat → Type}
    (headEq : Head → Head → Prop) [DecidableRel headEq]
    (decode : {scope : Nat} → RootCode scope → Option (Tm Head scope × Tm Head scope))
    (context : Ctx Head n) (sigma : Sub Head n m) (code : Code Head RootCode m)
    {first second : Tm Head m} (accepted : code.check headEq decode first second = true) :
    (applyFunctionCode context sigma code).check headEq decode
      (applyClosed context sigma first) (applyClosed context sigma second) = true := by
  induction context with
  | nil => exact accepted
  | snoc prior domain ih =>
      exact Code.check_mapContext headEq decode
        (fun function => .app function (sigma 0)) (fun step => .congAppFun step (sigma 0))
        (fun _ => rfl) (ih (fun index => sigma index.succ))

theorem applyFunctionCode_stepCount {RootCode : Nat → Type}
    (context : Ctx Head n) (sigma : Sub Head n m) (code : Code Head RootCode m) :
    (applyFunctionCode context sigma code).stepCount = code.stepCount := by
  induction context with
  | nil => rfl
  | snoc prior domain ih => simp only [applyFunctionCode, Code.stepCount_mapContext, ih]

#print axioms applicationCodeIn_checked
#print axioms applicationCode_checked
#print axioms applicationCode_stepCount

#print axioms close_formed
#print axioms close_typed
#print axioms checked_substitution
#print axioms apply_typed
#print axioms close_into_target
#print axioms checked_program
#print axioms checked_projection_loop
#print axioms checked_return_then_consume

end FormationCheckedTelescopePrograms
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationCheckedTelescopePrograms

open FormationSensitive TelescopeAbstraction
variable {Head : Type} {n m : Nat}

/-- Each literal input position is passed through its selected closed map. -/
def adaptedArguments (adapters : Fin n → Tm Head 0) : Sub Head n n :=
  fun index => .app (liftClosed (adapters index)) (.var index)

/-- Compose the actual constructor with the finite adapter vector, then
abstract its original input telescope through the existing closure operation. -/
def adaptClosed (input output : Ctx Head n) (adapters : Fin n → Tm Head 0)
    (function : Tm Head 0) : Tm Head 0 :=
  closeTerm input (applyClosed output (adaptedArguments adapters) (liftClosed function))

private theorem apply_closedArrow {rules : Rules Head} {context : Ctx Head n}
    {domain codomain : Tm Head 0} {function argument : Tm Head n}
    (functionTyped : Typing rules context function (liftClosed (.pi domain (liftClosed codomain))))
    (argumentTyped : Typing rules context argument (liftClosed domain)) :
    Typing rules context (.app function argument) (liftClosed codomain) := by
  change Typing rules context function
    (.pi (liftClosed domain) (rename (liftRen Fin.elim0) (liftClosed codomain))) at functionTyped
  rw [rename_liftClosed] at functionTyped
  simpa only [inst0, subst_liftClosed] using (Typing.appElim functionTyped argumentTyped)

/-- Literal primitive map types earn the actual context morphism used by
application; their endpoints remain tied to both original telescopes. -/
theorem adaptedArguments_typed {rules : Rules Head} (input output : Ctx Head n)
    (domains codomains : Fin n → Tm Head 0) (adapters : Fin n → Tm Head 0)
    (inputRead : ∀ index, Ctx.lookup input index = liftClosed (domains index))
    (outputRead : ∀ index, Ctx.lookup output index = liftClosed (codomains index))
    (primitive : ∀ index, Typing rules .nil (adapters index)
      (.pi (domains index) (liftClosed (codomains index)))) :
    FormationSensitive.CtxMor rules output input (adaptedArguments adapters) := by
  intro index
  have adapter := liftClosed_typing (primitive index) input
  have value : Typing rules input (.var index) (liftClosed (domains index)) :=
    (inputRead index) ▸ Typing.var index
  have applied := apply_closedArrow adapter value
  simpa only [adaptedArguments, outputRead, subst_liftClosed] using applied

/-- The composed operator is a formed closed program, derived from its
individual adapters and the original constructor's declared type. -/
theorem adaptClosed_typing {rules : Rules Head}
    (universes : UniverseRegularity rules)
    (joins : ∀ {u v}, rules.isUniverse u → rules.isUniverse v →
      ∃ w, rules.isUniverse w ∧ rules.join u v w)
    (input output : Ctx Head n) (inputFormed : ContextFormation rules input)
    (domains codomains : Fin n → Tm Head 0) (adapters : Fin n → Tm Head 0)
    (inputRead : ∀ index, Ctx.lookup input index = liftClosed (domains index))
    (outputRead : ∀ index, Ctx.lookup output index = liftClosed (codomains index))
    (primitive : ∀ index, Typing rules .nil (adapters index)
      (.pi (domains index) (liftClosed (codomains index))))
    {function result : Tm Head 0}
    (functionTyped : Typing rules .nil function (closeType output (liftClosed result))) :
    Typing rules .nil (adaptClosed input output adapters function)
      (closeType input (liftClosed result)) := by
  have arguments := adaptedArguments_typed input output domains codomains adapters
    inputRead outputRead primitive
  have application := apply_typed arguments (liftClosed_typing functionTyped input)
  simp only [subst_liftClosed] at application
  exact close_typed universes joins inputFormed application

/-- The existing telescope certificate records the administrative applications
of the adapted program without a second evaluator or recursive certificate fold. -/
def adaptClosedCode (input output : Ctx Head n) (adapters : Fin n → Tm Head 0)
    (function : Tm Head 0) (values : Sub Head n m) :=
  applicationCode input values
    (applyClosed output (adaptedArguments adapters) (liftClosed function))

theorem adaptedArguments_substitute (adapters : Fin n → Tm Head 0)
    (values : Sub Head n m) :
    subComp values (adaptedArguments adapters) =
      fun index => .app (liftClosed (adapters index)) (values index) := by
  funext index
  simp only [subComp, adaptedArguments, subst, subst_liftClosed]

theorem adaptClosedCode_checked [DecidableEq Head]
    (input output : Ctx Head n) (adapters : Fin n → Tm Head 0)
    (function : Tm Head 0) (values : Sub Head n m) :
    (adaptClosedCode input output adapters function values).check (fun _ _ => False) noRoot
      (applyClosed input values (liftClosed (adaptClosed input output adapters function)))
      (applyClosed output (fun index => .app (liftClosed (adapters index)) (values index))
        (liftClosed function)) = true := by
  have checked := applicationCode_checked input values
    (applyClosed output (adaptedArguments adapters) (liftClosed function))
  simpa only [adaptClosedCode, adaptClosed, applyClosed_subst, adaptedArguments_substitute,
    subst_liftClosed] using checked

theorem adaptClosedCode_stepCount (input output : Ctx Head n)
    (adapters : Fin n → Tm Head 0) (function : Tm Head 0) (values : Sub Head n m) :
    (adaptClosedCode input output adapters function values).stepCount = n :=
  applicationCode_stepCount input values _

end FormationCheckedTelescopePrograms
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
