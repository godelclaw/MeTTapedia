import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.BindingSignatureEmbedding
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.EmptyRootConversion
import Mettapedia.OSLF.Syntax.FreeBindingTerms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionConstantExpansion

/-!
# Binding signatures interpreted by closed native programs

This interpretation uses the existing free binding-term algebra. A source sort
may denote a compound native type; a source constructor may denote a derived
closed program. The original named-declaration compiler is its proved special
case. Formation follows from local type formation and each primitive image's
actual typing. Renaming and simultaneous substitution preserve every binding
spine and ambient position.

Derived abstraction and instantiation programs carry explicit finite beta
certificates and directed executions. The instantiation endpoint is the compiled
source instance itself. Contextual metavariable programs reuse the original
schema compiler and earn formation before replay; simultaneous substitution
retains checked paths to the same source value. Original certificate admission
precedes constant expansion. Literal fresh-constructor images additionally
reflect full native conversion in a root-free presentation. Derived closed
operator images and resource bounds require separate comparisons.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding
namespace ClosedOperators

open Mettapedia.OSLF
open Binding.FreeBindingTerms

variable {S : Binding.Signature} {Head : Type}

abbrev Carrier (Head : Type) (gamma : Binding.Ctx S) (_sort : S.Srt) := Tm Head gamma.length

/-- Constructor interpretations may be derived closed native programs. They
need not be opaque constants named by the source constructor. -/
abbrev Images (S : Binding.Signature) (Head : Type) :=
  {sort : S.Srt} → S.Op sort → Tm Head 0

def applyArguments : {gamma : Binding.Ctx S} → {arity : List (List S.Srt × S.Srt)} →
    Tm Head gamma.length → FamilyArgs S (Carrier Head) arity gamma → Tm Head gamma.length
  | _, _, head, .nil => head
  | _, _, head, .cons (bs := bound) body rest =>
      applyArguments (.app head (abstract bound body)) rest

def algebra (images : Images S Head) : Binding.FreeBindingTerms.Algebra S where
  Carrier := Carrier Head
  injectVar := fun position => .var (Binding.varIdx position)
  operation := fun operator arguments => applyArguments (liftClosed (images operator)) arguments

/-- Reuse the existing initial raw binding fold. The source and all of its
binding telescopes are unchanged. -/
def compile (images : Images S Head) {gamma : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term S gamma sort) : Tm Head gamma.length := fold (algebra images) term

def compileArguments (images : Images S Head) {gamma : Binding.Ctx S}
    {arity : List (List S.Srt × S.Srt)} (head : Tm Head gamma.length)
    (arguments : Binding.Args S arity gamma) : Tm Head gamma.length :=
  applyArguments head (foldArgs (algebra images) arguments)

theorem compile_var (images : Images S Head) {gamma : Binding.Ctx S} {sort : S.Srt}
    (position : Binding.Var gamma sort) : compile images (.var position) = .var (Binding.varIdx position) := rfl

theorem compile_op (images : Images S Head) {gamma : Binding.Ctx S} {sort : S.Srt}
    (operator : S.Op sort) (arguments : Binding.Args S (S.arity operator) gamma) :
    compile images (.op operator arguments) = compileArguments images (liftClosed (images operator)) arguments := rfl

theorem compileArguments_nil (images : Images S Head) {gamma : Binding.Ctx S}
    (head : Tm Head gamma.length) : compileArguments images head .nil = head := rfl

theorem compileArguments_cons (images : Images S Head) {gamma : Binding.Ctx S}
    {bound : List S.Srt} {sort : S.Srt} {rest : List (List S.Srt × S.Srt)}
    (head : Tm Head gamma.length) (body : Binding.Term S (bound ++ gamma) sort)
    (arguments : Binding.Args S rest gamma) :
    compileArguments images head (.cons body arguments) =
      compileArguments images (.app head (abstract bound (compile images body))) arguments := rfl

mutual
/-- Literal named constructors are the existing compiler's actual special case. -/
theorem compile_named (names : Names S) : ∀ {gamma : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term S gamma sort),
    compile (fun operator => Tm.const (names.operator operator)) term = encode (Head := Head) names term
  | _, _, .var _ => rfl
  | _, _, .op operator arguments => by
      rw [compile_op]
      exact compileArguments_named names (.const (names.operator operator)) arguments

theorem compileArguments_named (names : Names S) :
    ∀ {gamma : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
      (head : Tm Head gamma.length) (arguments : Binding.Args S arity gamma),
    compileArguments (fun operator => Tm.const (names.operator operator)) head arguments =
      BindingSignatureEmbedding.applyArguments names head arguments
  | _, _, _, .nil => rfl
  | _, _, head, .cons (bs := bound) body rest => by
      rw [compileArguments_cons, compile_named names body]
      exact compileArguments_named names (.app head (abstract bound (encode names body))) rest
end

mutual
/-- A derived closed operator image is stable under source renaming, including
renaming below all of its declared binders. -/
theorem compile_rename (images : Images S Head) :
    ∀ {gamma delta : Binding.Ctx S} {sort : S.Srt}
      (action : Binding.Ren S gamma delta) (term : Binding.Term S gamma sort),
      rename (encodeRen action) (compile images term) = compile images (Binding.rename action term)
  | _, _, _, action, .var position => by
      simp only [compile_var, Binding.rename, rename, encodeRen_variable]
  | _, _, _, action, .op operator arguments => by
      simp only [compile_op, Binding.rename]
      simpa only [rename_liftClosed] using
        compileArguments_rename images action (liftClosed (images operator)) arguments

theorem compileArguments_rename (images : Images S Head) :
    ∀ {gamma delta : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
      (action : Binding.Ren S gamma delta) (head : Tm Head gamma.length)
      (arguments : Binding.Args S arity gamma),
      rename (encodeRen action) (compileArguments images head arguments) =
        compileArguments images (rename (encodeRen action) head) (Binding.renameArgs action arguments)
  | _, _, _, _, _, .nil => rfl
  | _, _, _, action, head, .cons (bs := bound) body rest => by
      simp only [compileArguments_cons, Binding.renameArgs,
        compileArguments_rename images action, rename, rename_abstract,
        ← encodeRen_lift action bound, compile_rename images]
end

/-- Translate the actual source simultaneous assignment, retaining positions. -/
def compileSub (images : Images S Head) :
    {gamma delta : Binding.Ctx S} → Binding.Sub S gamma delta → Sub Head gamma.length delta.length
  | [], _, _, index => Fin.elim0 index
  | sort :: _, _, action, index =>
      Fin.cases (compile images (action sort .zero))
        (compileSub images (fun other position => action other (.succ position))) index

theorem compileSub_variable (images : Images S Head) :
    ∀ {gamma delta : Binding.Ctx S} (action : Binding.Sub S gamma delta)
      {sort : S.Srt} (position : Binding.Var gamma sort),
      compileSub images action (Binding.varIdx position) = compile images (action sort position)
  | _, _, _, _, .zero => rfl
  | _, _, action, _, .succ position =>
      compileSub_variable images (fun sort index => action sort (.succ index)) position

theorem compileSub_lift (images : Images S Head) {gamma delta : Binding.Ctx S}
    (action : Binding.Sub S gamma delta) (bound : List S.Srt) :
    compileSub images (Binding.liftSub action bound) = liftSubSpine (compileSub images action) bound := by
  induction bound with
  | nil => rfl
  | cons sort bound ih =>
      funext index
      refine Fin.cases ?_ (fun prior => ?_) index
      · rfl
      · let position := Binding.varOfIdx (S := S) (bound ++ gamma) prior
        have source := compileSub_variable images
          (Binding.liftSub action (sort :: bound)) (Binding.Var.succ position)
        have target := compileSub_variable images (Binding.liftSub action bound) position
        have atPosition : Binding.varIdx position = prior := Binding.varIdx_varOfIdx _ _
        simp only [Binding.varIdx, Binding.liftSub, atPosition] at source
        rw [Binding.weaken, ← compile_rename, encodeRen_weaken] at source
        rw [atPosition, ih] at target
        exact source.trans (congrArg (rename wk) target.symm)

mutual
/-- The derived operator interpretation commutes with actual simultaneous
source substitution, rather than only with capture-free fixtures. -/
theorem compile_substitution (images : Images S Head) :
    ∀ {gamma delta : Binding.Ctx S} {sort : S.Srt}
      (action : Binding.Sub S gamma delta) (term : Binding.Term S gamma sort),
      subst (compileSub images action) (compile images term) = compile images (Binding.bind action term)
  | _, _, _, action, .var position => by
      simp only [compile_var, Binding.bind, subst, compileSub_variable]
  | _, _, _, action, .op operator arguments => by
      simp only [compile_op, Binding.bind]
      simpa only [subst_liftClosed] using
        compileArguments_substitution images action (liftClosed (images operator)) arguments

theorem compileArguments_substitution (images : Images S Head) :
    ∀ {gamma delta : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
      (action : Binding.Sub S gamma delta) (head : Tm Head gamma.length)
      (arguments : Binding.Args S arity gamma),
      subst (compileSub images action) (compileArguments images head arguments) =
        compileArguments images (subst (compileSub images action) head) (Binding.bindArgs action arguments)
  | _, _, _, _, _, .nil => rfl
  | _, _, _, action, head, .cons (bs := bound) body rest => by
      simp only [compileArguments_cons, Binding.bindArgs,
        compileArguments_substitution images action, subst, subst_abstract,
        ← compileSub_lift images action bound, compile_substitution images]
end

theorem compileSub_named (names : Names S) :
    ∀ {gamma delta : Binding.Ctx S} (action : Binding.Sub S gamma delta),
      compileSub (fun operator => Tm.const (names.operator operator)) action =
        encodeSub (Head := Head) names action
  | [], _, _ => rfl
  | sort :: gamma, delta, action => by
      funext index
      refine Fin.cases ?_ (fun prior => ?_) index
      · exact compile_named names (action sort .zero)
      · exact congrFun (compileSub_named names (fun other position => action other (.succ position))) prior

abbrev Types (S : Binding.Signature) (Head : Type) := S.Srt → Tm Head 0

def typeContext (types : Types S Head) : (gamma : Binding.Ctx S) → Ctx Head gamma.length
  | [] => .nil
  | sort :: rest => .snoc (typeContext types rest) (liftClosed (types sort))

def spineType (types : Types S Head) : List S.Srt → Tm Head 0 → Tm Head 0
  | [], result => result
  | sort :: rest, result => spineType types rest (closedArrow (types sort) result)

/-- Closing the actual source-sort telescope gives its native function
spine, in the same lexical argument order. -/
theorem closeType_spine (types : Types S Head) (bound : Binding.Ctx S) (result : Tm Head 0) :
    TelescopeAbstraction.closeType (typeContext types bound) (liftClosed result) =
      spineType types bound result := by
  induction bound generalizing result with
  | nil => exact TelescopeAbstraction.liftClosed_zero result
  | cons sort rest ih =>
      change TelescopeAbstraction.closeType (typeContext types rest)
        (.pi (liftClosed (types sort)) (liftClosed result)) =
          spineType types rest (closedArrow (types sort) result)
      rw [← liftClosed_closedArrow]
      exact ih _

def bindingType (types : Types S Head) (bound : List S.Srt) (sort : S.Srt) : Tm Head 0 :=
  spineType types bound (types sort)

def argumentsType (types : Types S Head) : List (List S.Srt × S.Srt) → Tm Head 0 → Tm Head 0
  | [], result => result
  | (bound, sort) :: rest, result => closedArrow (bindingType types bound sort) (argumentsType types rest result)

def operatorType (types : Types S Head) {sort : S.Srt} (operator : S.Op sort) : Tm Head 0 :=
  argumentsType types (S.arity operator) (types sort)

/-- Local sort interpretations are actual formed closed native types, including
compound types. Their formation does not require infinitely many sort names. -/
structure Formation (types : Types S Head) (rules : Rules Head) where
  typeUniverse : Head
  joined : Head
  universeIs : rules.isUniverse typeUniverse
  joinSelf : rules.join typeUniverse typeUniverse joined
  collapseSelf : rules.cumulative joined typeUniverse
  typeFormed : ∀ sort, FormationSensitive.Typing rules .nil (types sort) (.head typeUniverse)

/-- Each primitive constructor image earns its own native type. Arbitrary
source-term preservation is proved below, rather than stored in this record. -/
structure Realization (types : Types S Head) (images : Images S Head) (rules : Rules Head)
    extends Formation types rules where
  imageTyped : ∀ {sort} (operator : S.Op sort),
    FormationSensitive.Typing rules .nil (images operator) (operatorType types operator)

namespace Formation

open FormationSensitive

variable {types : Types S Head} {rules : Rules Head}

theorem closedArrow_formed (formed : Formation types rules) {domain codomain : Tm Head 0}
    (domainFormed : Typing rules .nil domain (.head formed.typeUniverse))
    (codomainFormed : Typing rules .nil codomain (.head formed.typeUniverse)) :
    Typing rules .nil (closedArrow domain codomain) (.head formed.typeUniverse) :=
  .cumul (.piForm domainFormed formed.universeIs
    (FormationCheckedTelescopePrograms.liftClosed_typing codomainFormed (.snoc .nil domain)) formed.universeIs formed.joinSelf) formed.collapseSelf

theorem spineType_formed (formed : Formation types rules) (bound : List S.Srt)
    {result : Tm Head 0} (resultFormed : Typing rules .nil result (.head formed.typeUniverse)) :
    Typing rules .nil (spineType types bound result) (.head formed.typeUniverse) := by
  induction bound generalizing result with
  | nil => exact resultFormed
  | cons sort rest ih => exact ih (formed.closedArrow_formed (formed.typeFormed sort) resultFormed)

theorem bindingType_formed (formed : Formation types rules) (bound : List S.Srt) (sort : S.Srt) :
    Typing rules .nil (bindingType types bound sort) (.head formed.typeUniverse) :=
  formed.spineType_formed bound (formed.typeFormed sort)

theorem argumentsType_formed (formed : Formation types rules) (arity : List (List S.Srt × S.Srt))
    {result : Tm Head 0} (resultFormed : Typing rules .nil result (.head formed.typeUniverse)) :
    Typing rules .nil (argumentsType types arity result) (.head formed.typeUniverse) := by
  induction arity with
  | nil => exact resultFormed
  | cons argument rest ih => exact formed.closedArrow_formed (formed.bindingType_formed _ _) ih

theorem typeContext_formed (formed : Formation types rules) (gamma : Binding.Ctx S) :
    ContextFormation rules (typeContext types gamma) := by
  induction gamma with
  | nil => exact .nil
  | cons sort rest ih =>
      exact .snoc ih (FormationCheckedTelescopePrograms.liftClosed_typing (formed.typeFormed sort) (typeContext types rest)) formed.universeIs

theorem typeContext_lookup (types : Types S Head) :
    ∀ {gamma : Binding.Ctx S} {sort : S.Srt} (position : Binding.Var gamma sort),
      Ctx.lookup (typeContext types gamma) (Binding.varIdx position) = liftClosed (types sort)
  | _, _, .zero => by
      exact rename_liftClosed wk _
  | _, _, .succ position => by
      simp only [typeContext, Binding.varIdx, Ctx.lookup_snoc_succ, typeContext_lookup, rename_liftClosed]

theorem abstract_typing (formed : Formation types rules) {gamma : Binding.Ctx S}
    (bound : List S.Srt) {result : Tm Head 0}
    (resultFormed : Typing rules .nil result (.head formed.typeUniverse))
    (body : Tm Head (bound ++ gamma).length)
    (typed : Typing rules (typeContext types (bound ++ gamma)) body (liftClosed result)) :
    Typing rules (typeContext types gamma) (abstract bound body) (liftClosed (spineType types bound result)) := by
  induction bound generalizing result with
  | nil => exact typed
  | cons sort rest ih =>
      have functionType := formed.closedArrow_formed (formed.typeFormed sort) resultFormed
      have functionFormed := FormationCheckedTelescopePrograms.liftClosed_typing functionType (typeContext types (rest ++ gamma))
      rw [liftClosed_closedArrow] at functionFormed
      have function := Typing.lamIntro functionFormed formed.universeIs typed
      apply ih functionType (.lam body)
      simpa only [liftClosed_closedArrow] using function

end Formation

namespace Realization

open FormationSensitive

variable {types : Types S Head} {images : Images S Head} {rules : Rules Head}

mutual
theorem compile_typing (realization : Realization types images rules) :
    ∀ {gamma : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S gamma sort),
      Typing rules (typeContext types gamma) (compile images term) (liftClosed (types sort))
  | _, _, .var position => by
      simpa only [compile_var, Formation.typeContext_lookup] using
        (Typing.var (R := rules) (Γ := typeContext types _) (Binding.varIdx position))
  | gamma, sort, .op operator arguments => by
      rw [compile_op]
      exact compileArguments_typing realization arguments
        (realization.typeFormed sort) _
        ((realization.imageTyped operator).renameTyping (Δ := typeContext types gamma)
          (ρ := Fin.elim0) (fun index => Fin.elim0 index))

theorem compileArguments_typing (realization : Realization types images rules) :
    ∀ {gamma : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
      (arguments : Binding.Args S arity gamma) {result : Tm Head 0},
      Typing rules .nil result (.head realization.typeUniverse) →
      ∀ (head : Tm Head gamma.length),
      Typing rules (typeContext types gamma) head (liftClosed (argumentsType types arity result)) →
      Typing rules (typeContext types gamma) (compileArguments images head arguments) (liftClosed result)
  | _, _, .nil, _, _, _, typed => typed
  | _, _, .cons (bs := bound) (s := sort) body rest, result, resultFormed, head, typed => by
      have bodyTyped := realization.toFormation.abstract_typing bound (realization.typeFormed sort)
        (compile images body) (compile_typing realization body)
      have functionTyped := typed
      change Typing rules _ head (liftClosed (closedArrow _ _)) at functionTyped
      rw [liftClosed_closedArrow] at functionTyped
      have applied := Typing.appElim functionTyped bodyTyped
      apply compileArguments_typing realization rest resultFormed
      simpa only [inst0, subst_liftClosed, compile] using applied
end

theorem compile_judgment (realization : Realization types images rules)
    {gamma : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S gamma sort) :
    Judgment rules (typeContext types gamma) (compile images term) (liftClosed (types sort)) :=
  ⟨realization.toFormation.typeContext_formed gamma, realization.compile_typing term⟩

end Realization

/-! ## Compatibility with declared literal heads -/

abbrev namedTypes (names : Names S) : Types S Head := fun sort => sortType names sort

abbrev namedImages (names : Names S) : Images S Head := fun operator => .const (names.operator operator)

theorem typeContext_named (names : Names S) (gamma : Binding.Ctx S) :
    typeContext (namedTypes (Head := Head) names) gamma = context names gamma := by
  induction gamma with
  | nil => rfl
  | cons sort rest ih => simp only [typeContext, context, ih, namedTypes, sortType, liftClosed, rename]

theorem spineType_named (names : Names S) (bound : List S.Srt) (result : Tm Head 0) :
    spineType (namedTypes names) bound result = telescopeType names bound result := by
  induction bound generalizing result with
  | nil => rfl
  | cons sort rest ih => exact ih (closedArrow (sortType names sort) result)

theorem bindingType_named (names : Names S) (bound : List S.Srt) (sort : S.Srt) :
    bindingType (namedTypes (Head := Head) names) bound sort =
      BindingSignatureEmbedding.bindingType names bound sort :=
  spineType_named names bound (sortType names sort)

theorem argumentsType_named (names : Names S) (arity : List (List S.Srt × S.Srt)) (result : Tm Head 0) :
    argumentsType (namedTypes names) arity result =
      BindingSignatureEmbedding.argumentsType names arity result := by
  induction arity with
  | nil => rfl
  | cons argument rest ih => simp only [argumentsType, BindingSignatureEmbedding.argumentsType,
      bindingType_named, ih]

theorem operatorType_named (names : Names S) {sort : S.Srt} (operator : S.Op sort) :
    operatorType (namedTypes (Head := Head) names) operator =
      BindingSignatureEmbedding.operatorType names operator :=
  argumentsType_named names (S.arity operator) (sortType names sort)

/-- The established literal-declaration interpretation supplies the general
closed-type interpretation through its actual lookup-derived typing. -/
def Formation.ofNamed {names : Names S} {rules : Rules Head}
    (realization : SortRealization names rules) : Formation (namedTypes names) rules where
  typeUniverse := realization.typeUniverse
  joined := realization.joined
  universeIs := realization.universeIs
  joinSelf := realization.joinSelf
  collapseSelf := realization.collapseSelf
  typeFormed := fun sort => realization.sortType_formed .nil sort

def Realization.ofNamed {names : Names S} {rules : Rules Head}
    (realization : BindingSignatureEmbedding.Realization names rules) :
    Realization (namedTypes names) (namedImages names) rules where
  toFormation := Formation.ofNamed realization.toSortRealization
  imageTyped := fun operator => by
    rw [operatorType_named]
    simpa only [TelescopeAbstraction.liftClosed_zero, namedImages] using
      (FormationSensitive.Typing.const (Γ := .nil) (realization.operatorLookup operator)
        (realization.toSortRealization.operatorType_formed operator) realization.universeIs)

/-! ## Actual one-hole substitution -/

theorem compileSub_extend (images : Images S Head) {gamma : Binding.Ctx S} {domain : S.Srt}
    (argument : Binding.Term S gamma domain) :
    compileSub images (Binding.extend argument) = subst0 (compile images argument) := by
  funext index
  refine Fin.cases rfl (fun prior => ?_) index
  have law := compileSub_variable images (Binding.extend argument)
    (Binding.Var.succ (Binding.varOfIdx (S := S) gamma prior))
  simpa only [Binding.varIdx, Binding.varIdx_varOfIdx, Binding.extend, compile_var, subst0_succ] using law

/-- The compiled source instance is exactly the native capture-avoiding beta
substitution, including variables below arbitrary nested source binders. -/
theorem compile_inst (images : Images S Head) {gamma : Binding.Ctx S} {domain result : S.Srt}
    (body : Binding.Term S (domain :: gamma) result) (argument : Binding.Term S gamma domain) :
    inst0 (compile images argument) (compile images body) = compile images (Binding.inst body argument) := by
  simpa only [inst0, compileSub_extend, Binding.inst] using
    compile_substitution images (Binding.extend argument) body

/-! ## Derived abstraction and instantiation programs -/

namespace Derived

/-- A constructor image can be a program rather than a declaration. At an
arrow carrier this one program implements abstraction introduction and the
curried instantiation operator; its arguments supply the body and value. -/
def identity : Tm Head 0 := .lam (.var 0)

theorem identity_typing {types : Types S Head} {rules : Rules Head}
    (formed : Formation types rules) {domain : Tm Head 0}
    (domainFormed : FormationSensitive.Typing rules .nil domain (.head formed.typeUniverse)) :
    FormationSensitive.Typing rules .nil (identity (Head := Head)) (closedArrow domain domain) := by
  have arrow := formed.closedArrow_formed domainFormed domainFormed
  refine .lamIntro arrow formed.universeIs ?_
  have lifted : rename (wk : Ren 0 1) domain = liftClosed domain :=
    rename_ext (fun index => Fin.elim0 index) domain
  simpa only [Ctx.lookup_snoc_zero, lifted] using
    (FormationSensitive.Typing.var (R := rules) (Γ := .snoc .nil domain) 0)

open StructuralConversionCode

variable {RootCode : Nat → Type}

/-- The administrative introduction step is explicit finite evidence. -/
def introductionCode {n : Nat} (body : Tm Head (n + 1)) : Code Head RootCode n :=
  .single (.betaPi (.var 0) (.lam body))

/-- First expose the supplied abstraction, then perform its actual
capture-avoiding substitution. The intermediate term is checked literally. -/
def substitutionCode {n : Nat} (body : Tm Head (n + 1)) (argument : Tm Head n) :
    Code Head RootCode n :=
  .trans (.single (.congAppFun (.betaPi (.var 0) (.lam body)) argument))
    (.single (.betaPi body argument))

variable [DecidableEq Head] (headEq : Head → Head → Prop) [DecidableRel headEq]
    (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))

theorem introductionCode_checked {n : Nat} (body : Tm Head (n + 1)) :
    (introductionCode (RootCode := RootCode) body).check headEq decodeRoot
      (.app (liftClosed identity) (.lam body)) (.lam body) = true := by
  simp only [Code.check, Code.decode, introductionCode, StepCode.decode,
    inst0_var_zero, identity, liftClosed, rename, liftRen]
  exact decide_eq_true rfl

theorem substitutionCode_checked {n : Nat} (body : Tm Head (n + 1)) (argument : Tm Head n) :
    (substitutionCode (RootCode := RootCode) body argument).check headEq decodeRoot
      (.app (.app (liftClosed identity) (.lam body)) argument) (inst0 argument body) = true := by
  simp only [Code.check, Code.decode, substitutionCode, StepCode.decode,
    inst0_var_zero, identity, liftClosed, rename, liftRen, mapEndpoints,
    Option.map_some, joinEndpoints, ↓reduceIte]
  exact decide_eq_true rfl

omit [DecidableEq Head] in
/-- Selected beta-step counts are distinct from code payload and execution
cost; the second code additionally retains an application position. -/
theorem introductionCode_stepCount {n : Nat} (body : Tm Head (n + 1)) :
    (introductionCode (RootCode := RootCode) body).stepCount = 1 := rfl

omit [DecidableEq Head] in
theorem substitutionCode_stepCount {n : Nat} (body : Tm Head (n + 1)) (argument : Tm Head n) :
    (substitutionCode (RootCode := RootCode) body argument).stepCount = 2 := rfl

/-- The evidence is checked against the compiled source instance, rather than
an independently supplied target endpoint. -/
theorem compiledSubstitution_checked (images : Images S Head) {gamma : Binding.Ctx S}
    {domain result : S.Srt} (body : Binding.Term S (domain :: gamma) result)
    (argument : Binding.Term S gamma domain) :
    (substitutionCode (RootCode := RootCode) (compile images body) (compile images argument)).check
      headEq decodeRoot (.app (.app (liftClosed identity) (.lam (compile images body)))
        (compile images argument)) (compile images (Binding.inst body argument)) = true := by
  rw [← compile_inst images body argument]
  exact substitutionCode_checked headEq decodeRoot _ _

omit [DecidableEq Head] in
/-- These are directed native beta runs, independent of every head policy
and authored root equation. -/
theorem introduction_steps {n : Nat} (body : Tm Head (n + 1)) :
    TelescopeAbstraction.BetaSteps (.app (liftClosed identity) (.lam body)) (.lam body) := by
  change TelescopeAbstraction.BetaSteps (.app (.lam (.var 0)) (.lam body)) (.lam body)
  simpa only [inst0_var_zero] using
    (Relation.ReflTransGen.single
      (StepCore.betaPi (root := (RootComputation.empty : RootComputation Head))
        (headEq := fun _ _ => False) (.var 0) (.lam body)))

omit [DecidableEq Head] in
theorem substitution_steps {n : Nat} (body : Tm Head (n + 1)) (argument : Tm Head n) :
    TelescopeAbstraction.BetaSteps
      (.app (.app (liftClosed identity) (.lam body)) argument) (inst0 argument body) := by
  have exposed := (introduction_steps body).lift (fun function : Tm Head n => Tm.app function argument)
    (fun _ _ step => StepCore.congAppFun step)
  exact exposed.tail (StepCore.betaPi body argument)

omit [DecidableEq Head] in
theorem compiledSubstitution_steps (images : Images S Head) {gamma : Binding.Ctx S}
    {domain result : S.Srt} (body : Binding.Term S (domain :: gamma) result)
    (argument : Binding.Term S gamma domain) :
    TelescopeAbstraction.BetaSteps
      (.app (.app (liftClosed identity) (.lam (compile images body))) (compile images argument))
      (compile images (Binding.inst body argument)) := by
  rw [← compile_inst images body argument]
  exact substitution_steps _ _

end Derived

end ClosedOperators
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding.ClosedOperators

open Mettapedia.OSLF
open ConstantExpansion

variable {S : Binding.Signature} {Head : Type}

/-- An argument's whole original binder spine commutes with simultaneous
closed constant interpretation. -/
theorem expand_abstract (constants : Bodies Head) {gamma : Binding.Ctx S}
    (bound : List S.Srt) (body : Tm Head (bound ++ gamma).length) :
    expand constants (abstract bound body) = abstract bound (expand constants body) := by
  induction bound with
  | nil => rfl
  | cons sort rest ih => exact ih (.lam body)

mutual
/-- Only the primitive operator images are supplied. The complete interpretation
is compared with the existing independently recursive named encoder. -/
theorem expand_encode (constants : Bodies Head) (names : Names S) (images : Images S Head)
    (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
      constants (names.operator operator) = images operator) :
    ∀ {gamma : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S gamma sort),
      expand constants (encode names term) = compile images term
  | _, _, .var _ => rfl
  | _, _, .op operator arguments => by
      rw [encode, compile_op]
      have compiled := expand_applyArguments constants names images operators
        (.const (names.operator operator)) arguments
      simpa only [expand, operators] using compiled

theorem expand_applyArguments (constants : Bodies Head) (names : Names S) (images : Images S Head)
    (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
      constants (names.operator operator) = images operator) :
    ∀ {gamma : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
      (head : Tm Head gamma.length) (arguments : Binding.Args S arity gamma),
      expand constants (BindingSignatureEmbedding.applyArguments names head arguments) =
        compileArguments images (expand constants head) arguments
  | _, _, _, .nil => rfl
  | _, _, head, .cons (bs := bound) body rest => by
      rw [BindingSignatureEmbedding.applyArguments, compileArguments_cons,
        expand_applyArguments constants names images operators]
      simp only [expand, expand_abstract, expand_encode constants names images operators]
end

namespace Schema

variable {metas : List (Binding.MetaArity S)}

def program (constants : Bodies Head) (names : Names S) {ambient : Binding.Ctx S}
    (bodies : Binding.ContextualAssignment S metas ambient)
    {source target : Binding.Ctx S} {sort : S.Srt}
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    (term : Binding.Term (Binding.withMetas S metas) source sort) : Tm Head target.length :=
  expand constants (BindingSignatureEmbedding.Schema.compile names bodies environment valuation term)

def evidence (constants : Bodies Head) (names : Names S) {ambient : Binding.Ctx S}
    (bodies : Binding.ContextualAssignment S metas ambient)
    {source target : Binding.Ctx S} {sort : S.Srt}
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    (term : Binding.Term (Binding.withMetas S metas) source sort) :
    StructuralConversionCode.Code Head (fun _ => Empty) target.length :=
  (BindingSignatureEmbedding.Schema.compileEvidence names bodies environment valuation term).expandConstants
    constants (fun code => code)

/-- The actual emitted expanded certificate ends at the original contextual
schema instance interpreted by the closed-operator fold. The named schema
compiler and its evidence algorithm are reused unchanged. -/
theorem evidence_checked [DecidableEq Head] (constants : Bodies Head) (names : Names S)
    (images : Images S Head)
    (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
      constants (names.operator operator) = images operator)
    {ambient : Binding.Ctx S} (bodies : Binding.ContextualAssignment S metas ambient)
    {source target : Binding.Ctx S} {sort : S.Srt}
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    (term : Binding.Term (Binding.withMetas S metas) source sort) :
    (evidence constants names bodies environment valuation term).check
      (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
      (program constants names bodies environment valuation term)
      (ClosedOperators.compile images
        (Binding.ContextualAssignment.instantiate bodies environment valuation term)) = true := by
  have original := BindingSignatureEmbedding.Schema.compileEvidence_checked
    (Head := Head) names bodies environment valuation term
  have expanded := StructuralConversionCode.Code.check_expandConstants
    constants (fun code : Empty => code) (fun _ _ => False)
    FormationCheckedTelescopePrograms.noRoot FormationCheckedTelescopePrograms.noRoot
    (fun code => nomatch code) original
  rw [expand_encode constants names images operators] at expanded
  exact expanded

end Schema

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding.ClosedOperators

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding


private abbrev schemaArguments {S : Mettapedia.OSLF.Binding.Signature} {Value : Type}
    {ambient : Mettapedia.OSLF.Binding.Ctx S}
    (dependencies : Mettapedia.OSLF.Binding.Ctx S)
    (arguments : Fin dependencies.length → Value) (environment : Fin ambient.length → Value) :=
  Schema.concatSub dependencies arguments environment

namespace ClosedOperators

open Mettapedia.OSLF ConstantExpansion FormationSensitive TelescopeAbstraction

variable {S : Binding.Signature} {Head : Type} {types : Types S Head} {images : Images S Head} {rules : Rules Head}

/-- The generated term closes a telescope's variable positions. Its domains
are used by formation, while this syntactic closure depends on its shape. -/
theorem expand_closeTerm (constants : Bodies Head) {n : Nat} (source target : Ctx Head n)
    (body : Tm Head n) :
    expand constants (closeTerm source body) = closeTerm target (expand constants body) := by
  induction source with
  | nil => cases target; rfl
  | snoc prior domain ih => cases target with
    | snoc target other => exact ih target (.lam body)

theorem expand_applyClosed (constants : Bodies Head) {n m : Nat} (source target : Ctx Head n)
    (values : Sub Head n m) (function : Tm Head m) :
    expand constants (applyClosed source values function) =
      applyClosed target (fun index => expand constants (values index)) (expand constants function) := by
  induction source with
  | nil => cases target; rfl
  | snoc prior domain ih => cases target with
    | snoc target other =>
      simp only [applyClosed, expand]
      exact congrArg (fun function => Tm.app function (expand constants (values 0)))
        (ih target (fun index => values index.succ))

theorem expand_encodeSub (constants : Bodies Head) (names : Names S) (images : Images S Head)
    (operators : ∀ {sort : S.Srt} (operator : S.Op sort), constants (names.operator operator) = images operator) :
    ∀ {gamma target : Binding.Ctx S} (values : Binding.Sub S gamma target),
    (fun index => expand constants (encodeSub names values index)) = compileSub images values
  | [], _, _ => by funext index; exact Fin.elim0 index
  | sort :: rest, _, values => by
      funext index
      refine Fin.cases ?_ (fun prior => ?_) index
      · exact expand_encode constants names images operators (values sort .zero)
      · exact congrFun (expand_encodeSub constants names images operators
          (fun sort position => values sort (.succ position))) prior

namespace Formation

/-- The actual closed type meanings form the source telescope abstraction.
No virtual polymorphic identity constant is assumed to be declared. -/
theorem closeTerm_typing (formed : Formation types rules)
    {gamma : Binding.Ctx S} {result : Tm Head 0}
    (resultFormed : Typing rules .nil result (.head formed.typeUniverse))
    (body : Tm Head gamma.length)
    (typed : Typing rules (typeContext types gamma) body (liftClosed result)) :
    Typing rules .nil (closeTerm (typeContext types gamma) body)
      (closeType (typeContext types gamma) (liftClosed result)) := by
  induction gamma generalizing result with
  | nil => simpa only [typeContext, closeTerm, closeType] using typed
  | cons sort rest ih =>
      have functionFormed := formed.closedArrow_formed (formed.typeFormed sort) resultFormed
      have lifted := functionFormed.renameTyping
        (Δ := typeContext types rest) (ρ := Fin.elim0) (fun index => Fin.elim0 index)
      change Typing rules (typeContext types rest)
        (liftClosed (closedArrow (types sort) result)) (.head formed.typeUniverse) at lifted
      rw [liftClosed_closedArrow] at lifted
      have functionTyped := Typing.lamIntro lifted formed.universeIs typed
      have closed := ih functionFormed (.lam body)
        (by simpa only [liftClosed_closedArrow] using functionTyped)
      rw [liftClosed_closedArrow] at closed
      simpa only [typeContext, closeTerm, closeType] using closed

end Formation

namespace Realization

theorem compileSub_typed (realization : Realization types images rules)
    {gamma target : Binding.Ctx S} (values : Binding.Sub S gamma target) :
    FormationSensitive.CtxMor rules (typeContext types gamma) (typeContext types target) (compileSub images values) := by
  intro index
  let position := Binding.varOfIdx (S := S) gamma index
  have actual := realization.compile_typing (values _ position)
  have positionIndex : Binding.varIdx position = index := Binding.varIdx_varOfIdx _ _
  have valueEquation := compileSub_variable images values position
  have lookupEquation := Formation.typeContext_lookup (Head := Head) types position
  rw [positionIndex] at valueEquation lookupEquation
  simpa only [valueEquation, lookupEquation, subst_liftClosed] using actual

theorem applyClosed_typing (realization : Realization types images rules)
    {gamma : Binding.Ctx S} {sort : S.Srt} (body : Binding.Term S gamma sort)
    {m : Nat} {target : Ctx Head m} (values : Sub Head gamma.length m)
    (valuesTyped : FormationSensitive.CtxMor rules (typeContext types gamma) target values) :
    Typing rules target
      (applyClosed (typeContext types gamma) values
        (liftClosed (closeTerm (typeContext types gamma) (compile images body))))
      (liftClosed (types sort)) := by
  have closed := realization.toFormation.closeTerm_typing (realization.typeFormed sort)
    _ (realization.compile_typing body)
  have lifted := closed.renameTyping (Δ := target) (ρ := Fin.elim0) (fun index => Fin.elim0 index)
  have applied := FormationCheckedTelescopePrograms.apply_typed
    (context := typeContext types gamma) (type := liftClosed (types sort)) valuesTyped lifted
  change Typing rules target
    (applyClosed (typeContext types gamma) values
      (liftClosed (closeTerm (typeContext types gamma) (compile images body))))
    (subst values (liftClosed (types sort))) at applied
  rw [subst_liftClosed] at applied
  exact applied

end Realization

namespace Schema

private theorem expandedConcat_typed (constants : Bodies Head)
    {ambient target : Binding.Ctx S} (dependencies : Binding.Ctx S)
    {arguments : Sub Head dependencies.length target.length}
    {environment : Sub Head ambient.length target.length}
    (argumentsTyped : FormationSensitive.CtxMor rules
      (typeContext types dependencies) (typeContext types target)
      (fun index => expand constants (arguments index)))
    (environmentTyped : FormationSensitive.CtxMor rules
      (typeContext types ambient) (typeContext types target)
      (fun index => expand constants (environment index))) :
    FormationSensitive.CtxMor rules (typeContext types (dependencies ++ ambient)) (typeContext types target)
      (fun index => expand constants
        (schemaArguments dependencies arguments environment index)) := by
  induction dependencies with
  | nil => exact environmentTyped
  | cons sort dependencies ih =>
      have prior := ih argumentsTyped.dropNewest
      have newest := argumentsTyped 0
      simp only [typeContext, Ctx.lookup_snoc_zero, rename_liftClosed, subst_liftClosed] at newest
      have combination :
          (fun index => expand constants
            (schemaArguments (sort :: dependencies) arguments environment index)) =
          consSub (expand constants (arguments 0))
            (fun index => expand constants
              (schemaArguments dependencies (fun i => arguments i.succ) environment index)) := by
        funext index
        exact Fin.cases rfl (fun _ => rfl) index
      rw [combination]
      exact prior.extend (by simpa only [subst_liftClosed] using newest)


variable {metas : List (Binding.MetaArity S)}

/-- Expand the shared schema traversal with a literal table of closed
native body functions. Dependency and ambient argument positions are still
read from the original source metavariable arities. -/
abbrev programWithPrograms (constants : Bodies Head) (names : Names S)
    {ambient source target : Binding.Ctx S} {sort : S.Srt}
    (programs : Fin metas.length → Tm Head 0)
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    (term : Binding.Term (Binding.withMetas S metas) source sort) : Tm Head target.length :=
  expand constants (BindingSignatureEmbedding.Schema.compileWithPrograms names programs environment valuation term)

/-- Formation of the actual source body functions is earned from the source
binding-signature interpretation, rather than supplied for a whole schema. -/
private theorem bodyPrograms_typed (realization : Realization types images rules)
    (constants : Bodies Head) (names : Names S)
    (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
      constants (names.operator operator) = images operator)
    {ambient : Binding.Ctx S} (bodies : Binding.ContextualAssignment S metas ambient)
    (index : Fin metas.length) :
    Typing rules .nil (expand constants (BindingSignatureEmbedding.Schema.bodyPrograms names bodies index))
      (closeType (typeContext types ((metas.get index).1 ++ ambient))
        (liftClosed (types (metas.get index).2))) := by
  rw [BindingSignatureEmbedding.Schema.bodyPrograms,
    expand_closeTerm constants _ (typeContext types ((metas.get index).1 ++ ambient)),
    expand_encode constants names images operators]
  exact realization.toFormation.closeTerm_typing (realization.typeFormed _)
    _ (realization.compile_typing (bodies index))

mutual
  theorem programWithPrograms_typing (realization : Realization types images rules)
      (constants : Bodies Head) (names : Names S)
      (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
        constants (names.operator operator) = images operator)
      {ambient : Binding.Ctx S} (programs : Fin metas.length → Tm Head 0)
      (programsTyped : ∀ index, Typing rules .nil (expand constants (programs index))
        (closeType (typeContext types ((metas.get index).1 ++ ambient))
          (liftClosed (types (metas.get index).2)))) :
      ∀ {source target : Binding.Ctx S} {sort : S.Srt}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (term : Binding.Term (Binding.withMetas S metas) source sort),
        Typing rules (typeContext types target)
          (programWithPrograms constants names programs environment valuation term) (liftClosed (types sort))
    | _, _, _, _, valuation, .var position => by
        simpa only [programWithPrograms, BindingSignatureEmbedding.Schema.compileWithPrograms,
          expand_encode constants names images operators] using
          realization.compile_typing (valuation _ position)
    | _, target, sort, environment, valuation, .op (.inl operator) arguments => by
        have constructor := (realization.imageTyped operator).renameTyping
          (Δ := typeContext types target) (ρ := Fin.elim0) (fun index => Fin.elim0 index)
        have compiled := argumentsWithPrograms_typing realization constants names operators programs programsTyped
          environment valuation arguments (realization.typeFormed sort)
            (head := .const (names.operator operator)) (by
              simpa only [expand, operators, operatorType, liftClosed] using constructor)
        simpa only [programWithPrograms, BindingSignatureEmbedding.Schema.compileWithPrograms, operatorType,
          expand, operators] using compiled
    | _, target, _, environment, valuation, .op (.inr (.mk index)) arguments => by
        have dependencies := metaArgumentsWithPrograms_typing realization constants names operators programs programsTyped
          environment valuation (metas.get index).1 arguments
        have environmentTyped : FormationSensitive.CtxMor rules
            (typeContext types ambient) (typeContext types target)
            (fun index => expand constants (encodeSub names environment index)) := by
          rw [expand_encodeSub constants names images operators]
          exact realization.compileSub_typed environment
        have combined := expandedConcat_typed constants (metas.get index).1
          dependencies environmentTyped
        have closed := (programsTyped index).renameTyping
          (Δ := typeContext types target) (ρ := Fin.elim0) (fun index => Fin.elim0 index)
        have applied := FormationCheckedTelescopePrograms.apply_typed
          (context := typeContext types ((metas.get index).1 ++ ambient))
          (type := liftClosed (types (metas.get index).2)) combined closed
        rw [subst_liftClosed] at applied
        change Typing rules _ (applyClosed _ _ (liftClosed (expand constants (programs index)))) _ at applied
        simpa only [programWithPrograms, BindingSignatureEmbedding.Schema.compileWithPrograms,
          expand_applyClosed constants _ (typeContext types ((metas.get index).1 ++ ambient)),
          expand_liftClosed, schemaArguments] using applied

  termination_by _ _ _ _ _ term => 2 * Binding.termSize term
  decreasing_by all_goals simp only [Binding.termSize]; all_goals omega

  theorem argumentsWithPrograms_typing (realization : Realization types images rules)
      (constants : Bodies Head) (names : Names S)
      (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
        constants (names.operator operator) = images operator)
      {ambient : Binding.Ctx S} (programs : Fin metas.length → Tm Head 0)
      (programsTyped : ∀ index, Typing rules .nil (expand constants (programs index))
        (closeType (typeContext types ((metas.get index).1 ++ ambient))
          (liftClosed (types (metas.get index).2)))) :
      ∀ {source target : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (arguments : Binding.Args (Binding.withMetas S metas) arity source),
        ∀ {result : Tm Head 0}, Typing rules .nil result (.head realization.typeUniverse) →
        ∀ {head : Tm Head target.length},
        Typing rules (typeContext types target) (expand constants head)
          (liftClosed (argumentsType types arity result)) →
        Typing rules (typeContext types target)
          (expand constants (BindingSignatureEmbedding.Schema.compileArgumentsWithPrograms names programs
            environment valuation head arguments)) (liftClosed result)
    | _, _, _, _, _, .nil, _, _, _, typed => by
        simpa only [BindingSignatureEmbedding.Schema.compileArgumentsWithPrograms, argumentsType] using typed
    | _, _, _, environment, valuation, .cons (bs := bound) (s := sort) body rest,
        result, formed, head, typed => by
        have bodyTyped := realization.toFormation.abstract_typing bound (realization.typeFormed sort)
          (programWithPrograms constants names programs
            (Binding.ContextualAssignment.weakenSub (S := S) bound environment)
            (Binding.liftSub (S := S) valuation bound) body)
          (programWithPrograms_typing realization constants names operators programs programsTyped _ _ body)
        have functionTyped := typed
        change Typing rules _ (expand constants head) (liftClosed (closedArrow _ _)) at functionTyped
        rw [liftClosed_closedArrow] at functionTyped
        have applied := Typing.appElim functionTyped bodyTyped
        simp only [inst0, subst_liftClosed] at applied
        have compiled := argumentsWithPrograms_typing realization constants names operators programs programsTyped
          environment valuation rest formed
          (head := .app head (abstract bound (BindingSignatureEmbedding.Schema.compileWithPrograms names programs
            (Binding.ContextualAssignment.weakenSub (S := S) bound environment)
            (Binding.liftSub (S := S) valuation bound) body))) (by
            simpa only [expand, expand_abstract, programWithPrograms] using applied)
        simpa only [BindingSignatureEmbedding.Schema.compileArgumentsWithPrograms] using compiled
  termination_by _ _ _ _ _ arguments _ _ _ _ => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega

  theorem metaArgumentsWithPrograms_typing (realization : Realization types images rules)
      (constants : Bodies Head) (names : Names S)
      (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
        constants (names.operator operator) = images operator)
      {ambient : Binding.Ctx S} (programs : Fin metas.length → Tm Head 0)
      (programsTyped : ∀ index, Typing rules .nil (expand constants (programs index))
        (closeType (typeContext types ((metas.get index).1 ++ ambient))
          (liftClosed (types (metas.get index).2)))) :
      ∀ {source target : Binding.Ctx S}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (dependencies : List S.Srt)
        (arguments : Binding.Args (Binding.withMetas S metas)
          (dependencies.map fun sort => ([], sort)) source),
        FormationSensitive.CtxMor rules (typeContext types dependencies) (typeContext types target)
          (fun index => expand constants
            (BindingSignatureEmbedding.Schema.compileMetaArgumentsWithPrograms names programs
              environment valuation dependencies arguments index))
    | _, _, _, _, [], .nil => by intro index; exact Fin.elim0 index
    | _, _, environment, valuation, sort :: dependencies, .cons body rest => by
        have previous := metaArgumentsWithPrograms_typing realization constants names operators programs programsTyped
          environment valuation dependencies rest
        have newest := programWithPrograms_typing realization constants names operators programs programsTyped
          (Binding.ContextualAssignment.weakenSub (S := S) [] environment)
          (Binding.liftSub (S := S) valuation []) body
        have combination :
            (fun index => expand constants
              (BindingSignatureEmbedding.Schema.compileMetaArgumentsWithPrograms names programs
                environment valuation (sort :: dependencies) (.cons body rest) index)) =
            consSub (programWithPrograms constants names programs
                (Binding.ContextualAssignment.weakenSub (S := S) [] environment)
                (Binding.liftSub (S := S) valuation []) body)
              (fun index => expand constants
                (BindingSignatureEmbedding.Schema.compileMetaArgumentsWithPrograms names programs
                  environment valuation dependencies rest index)) := by
          funext index
          refine Fin.cases ?_ (fun prior => ?_) index
          · simp only [BindingSignatureEmbedding.Schema.compileMetaArgumentsWithPrograms, Fin.cases_zero, consSub, programWithPrograms]
          · simp only [BindingSignatureEmbedding.Schema.compileMetaArgumentsWithPrograms, Fin.cases_succ, consSub]
        rw [combination]
        apply previous.extend
        simpa only [subst_liftClosed, List.nil_append] using newest
  termination_by _ _ _ _ _ arguments => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega
end

theorem program_typing (realization : Realization types images rules)
      (constants : Bodies Head) (names : Names S)
      (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
        constants (names.operator operator) = images operator)
      {ambient : Binding.Ctx S} (bodies : Binding.ContextualAssignment S metas ambient) :
      ∀ {source target : Binding.Ctx S} {sort : S.Srt}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (term : Binding.Term (Binding.withMetas S metas) source sort),
        Typing rules (typeContext types target)
          (program constants names bodies environment valuation term) (liftClosed (types sort)) :=
  programWithPrograms_typing realization constants names operators
    (BindingSignatureEmbedding.Schema.bodyPrograms names bodies)
    (bodyPrograms_typed realization constants names operators bodies)

theorem compileArguments_typing (realization : Realization types images rules)
      (constants : Bodies Head) (names : Names S)
      (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
        constants (names.operator operator) = images operator)
      {ambient : Binding.Ctx S} (bodies : Binding.ContextualAssignment S metas ambient) :
      ∀ {source target : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (arguments : Binding.Args (Binding.withMetas S metas) arity source),
        ∀ {result : Tm Head 0}, Typing rules .nil result (.head realization.typeUniverse) →
        ∀ {head : Tm Head target.length},
        Typing rules (typeContext types target) (expand constants head)
          (liftClosed (argumentsType types arity result)) →
        Typing rules (typeContext types target)
          (expand constants (BindingSignatureEmbedding.Schema.compileArguments names bodies
            environment valuation head arguments)) (liftClosed result) :=
  argumentsWithPrograms_typing realization constants names operators
    (BindingSignatureEmbedding.Schema.bodyPrograms names bodies)
    (bodyPrograms_typed realization constants names operators bodies)

theorem compileMetaArguments_typing (realization : Realization types images rules)
      (constants : Bodies Head) (names : Names S)
      (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
        constants (names.operator operator) = images operator)
      {ambient : Binding.Ctx S} (bodies : Binding.ContextualAssignment S metas ambient) :
      ∀ {source target : Binding.Ctx S}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (dependencies : List S.Srt)
        (arguments : Binding.Args (Binding.withMetas S metas)
          (dependencies.map fun sort => ([], sort)) source),
        FormationSensitive.CtxMor rules (typeContext types dependencies) (typeContext types target)
          (fun index => expand constants
            (BindingSignatureEmbedding.Schema.compileMetaArguments names bodies
              environment valuation dependencies arguments index)) :=
  metaArgumentsWithPrograms_typing realization constants names operators
    (BindingSignatureEmbedding.Schema.bodyPrograms names bodies)
    (bodyPrograms_typed realization constants names operators bodies)

/-- Formation is earned for the emitted program before its checked computation.
Primitive operator bodies may be arbitrary closed, well-typed native programs. -/
theorem program_judgment (realization : Realization types images rules)
    (constants : Bodies Head) (names : Names S)
    (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
      constants (names.operator operator) = images operator)
    {ambient source target : Binding.Ctx S}
    (bodies : Binding.ContextualAssignment S metas ambient)
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    {sort : S.Srt} (term : Binding.Term (Binding.withMetas S metas) source sort) :
    Judgment rules (typeContext types target)
      (program constants names bodies environment valuation term) (liftClosed (types sort)) :=
  ⟨realization.toFormation.typeContext_formed target,
    program_typing realization constants names operators bodies environment valuation term⟩


/-- Reuse substitution of the original emitted replay, then interpret its
retained constants. The bodies and every source occurrence stay fixed. -/
def reindexedEvidence (constants : Bodies Head) (names : Names S)
    {ambient source target destination : Binding.Ctx S}
    (bodies : Binding.ContextualAssignment S metas ambient)
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    {sort : S.Srt} (term : Binding.Term (Binding.withMetas S metas) source sort)
    (action : Binding.Sub S target destination) :
    StructuralConversionCode.Code Head (fun _ => Empty) destination.length :=
  (BindingSignatureEmbedding.Schema.reindexedEvidence names bodies environment valuation term action).expandConstants
    constants (fun code => code)

theorem reindexedEvidence_checked [DecidableEq Head]
    (constants : Bodies Head) (names : Names S)
    (images : Images S Head)
    (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
      constants (names.operator operator) = images operator)
    {ambient source target destination : Binding.Ctx S}
    (bodies : Binding.ContextualAssignment S metas ambient)
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    {sort : S.Srt} (term : Binding.Term (Binding.withMetas S metas) source sort)
    (action : Binding.Sub S target destination) :
    (reindexedEvidence constants names bodies environment valuation term action).check
      (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
      (subst (compileSub images action) (program constants names bodies environment valuation term))
      (ClosedOperators.compile images (Binding.ContextualAssignment.instantiate bodies
        (fun sort position => Binding.bind action (environment sort position))
        (fun sort position => Binding.bind action (valuation sort position)) term)) = true := by
  have original := BindingSignatureEmbedding.Schema.reindexedEvidence_checked
    (Head := Head) names bodies environment valuation term action
  have expanded := StructuralConversionCode.Code.check_expandConstants
    constants (fun code : Empty => code) (fun _ _ => False)
    FormationCheckedTelescopePrograms.noRoot FormationCheckedTelescopePrograms.noRoot
    (fun code => nomatch code) original
  simpa only [reindexedEvidence, program, expand_subst,
    expand_encodeSub constants names images operators,
    expand_encode constants names images operators] using expanded

/-- Recompilation and substitution of the original emitted program have
checked paths to one independently specified source instance. Raw compiler
outputs need not be definitionally equal. -/
theorem substitution_common_value [DecidableEq Head]
    (constants : Bodies Head) (names : Names S)
    (images : Images S Head)
    (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
      constants (names.operator operator) = images operator)
    {ambient source target destination : Binding.Ctx S}
    (bodies : Binding.ContextualAssignment S metas ambient)
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    {sort : S.Srt} (term : Binding.Term (Binding.withMetas S metas) source sort)
    (action : Binding.Sub S target destination) :
    let nextEnvironment := fun sort position => Binding.bind action (environment sort position)
    let nextValuation := fun sort position => Binding.bind action (valuation sort position)
    let result := ClosedOperators.compile images
      (Binding.ContextualAssignment.instantiate bodies nextEnvironment nextValuation term)
    (reindexedEvidence constants names bodies environment valuation term action).check
      (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
      (subst (compileSub images action) (program constants names bodies environment valuation term)) result = true ∧
    (evidence constants names bodies nextEnvironment nextValuation term).check
      (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
      (program constants names bodies nextEnvironment nextValuation term) result = true :=
  ⟨reindexedEvidence_checked constants names images operators bodies environment valuation term action,
    evidence_checked constants names images operators bodies _ _ term⟩

end Schema

end ClosedOperators
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding

open Mettapedia.OSLF ConstantExpansion

namespace ClosedOperators.Schema

variable {S : Binding.Signature} {Head : Type} {metas : List (Binding.MetaArity S)}

/-- Agreement on primitive operator images extends to the original source
terms by the existing free binding-term fold. -/
theorem expand_encode_eq_of_operators (first last : Bodies Head) (names : Names S)
    (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
      first (names.operator operator) = last (names.operator operator))
    {context : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term S context sort) :
    expand first (encode names term) = expand last (encode names term) := by
  rw [expand_encode first names (fun operator => first (names.operator operator)) (fun _ => rfl),
    expand_encode last names (fun operator => first (names.operator operator)) (fun operator => (operators operator).symm)]

mutual
  /-- A schema program depends on the actual operator images and native body
  function values. Agreement on those primitives earns the whole program law. -/
  theorem programWithPrograms_congr (first last : Bodies Head) (names : Names S)
      (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
        first (names.operator operator) = last (names.operator operator))
      {ambient : Binding.Ctx S} (firstPrograms lastPrograms : Fin metas.length → Tm Head 0)
      (programs : ∀ index, expand first (firstPrograms index) = expand last (lastPrograms index)) :
      ∀ {source target : Binding.Ctx S} {sort : S.Srt}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (term : Binding.Term (Binding.withMetas S metas) source sort),
        programWithPrograms first names firstPrograms environment valuation term =
          programWithPrograms last names lastPrograms environment valuation term
    | _, _, _, _, valuation, .var position => by
        simpa only [programWithPrograms, Schema.compileWithPrograms] using
          expand_encode_eq_of_operators first last names operators (valuation _ position)
    | _, _, _, environment, valuation, .op (.inl operator) arguments => by
        simpa only [programWithPrograms, Schema.compileWithPrograms] using
          argumentsWithPrograms_congr first last names operators firstPrograms lastPrograms programs
            environment valuation (.const (names.operator operator)) (.const (names.operator operator))
            arguments (by simp only [expand, operators])
    | _, _, _, environment, valuation, .op (.inr (.mk index)) arguments => by
        have dependencies := metaArgumentsWithPrograms_congr first last names operators
          firstPrograms lastPrograms programs environment valuation (metas.get index).1 arguments
        have ambientAgreement :
            (fun index => expand first (encodeSub names environment index)) =
              (fun index => expand last (encodeSub names environment index)) := by
          funext index
          have read := encodeSub_variable (Head := Head) names environment (Binding.varOfIdx (S := S) ambient index)
          rw [Binding.varIdx_varOfIdx] at read
          rw [read]
          exact expand_encode_eq_of_operators first last names operators _
        simp only [programWithPrograms, Schema.compileWithPrograms,
          expand_applyClosed first _ (context names ((metas.get index).1 ++ ambient)),
          expand_applyClosed last _ (context names ((metas.get index).1 ++ ambient)),
          expand_liftClosed, BindingSignatureEmbedding.Schema.concatSub_map, dependencies, ambientAgreement, programs]
  termination_by _ _ _ _ _ term => 2 * Binding.termSize term
  decreasing_by all_goals simp only [Binding.termSize]; all_goals omega

  theorem argumentsWithPrograms_congr (first last : Bodies Head) (names : Names S)
      (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
        first (names.operator operator) = last (names.operator operator))
      {ambient : Binding.Ctx S} (firstPrograms lastPrograms : Fin metas.length → Tm Head 0)
      (programs : ∀ index, expand first (firstPrograms index) = expand last (lastPrograms index)) :
      ∀ {source target : Binding.Ctx S} {arity : List (List S.Srt × S.Srt)}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (firstHead lastHead : Tm Head target.length)
        (arguments : Binding.Args (Binding.withMetas S metas) arity source),
        expand first firstHead = expand last lastHead →
        expand first (Schema.compileArgumentsWithPrograms names firstPrograms environment valuation firstHead arguments) =
          expand last (Schema.compileArgumentsWithPrograms names lastPrograms environment valuation lastHead arguments)
    | _, _, _, _, _, _, _, .nil, agreement => by
        simpa only [Schema.compileArgumentsWithPrograms] using agreement
    | _, _, _, environment, valuation, firstHead, lastHead,
        .cons (bs := bound) body rest, agreement => by
        have bodyAgreement := programWithPrograms_congr first last names operators firstPrograms
          lastPrograms programs (Binding.ContextualAssignment.weakenSub (S := S) bound environment)
          (Binding.liftSub (S := S) valuation bound) body
        have application := congrArg₂ Tm.app agreement (congrArg (abstract (S := S) bound) bodyAgreement)
        simpa only [Schema.compileArgumentsWithPrograms] using
          argumentsWithPrograms_congr first last names operators firstPrograms lastPrograms programs
            environment valuation
            (.app firstHead (abstract (S := S) bound (Schema.compileWithPrograms names firstPrograms
              (Binding.ContextualAssignment.weakenSub (S := S) bound environment)
              (Binding.liftSub (S := S) valuation bound) body)))
            (.app lastHead (abstract (S := S) bound (Schema.compileWithPrograms names lastPrograms
              (Binding.ContextualAssignment.weakenSub (S := S) bound environment)
              (Binding.liftSub (S := S) valuation bound) body)))
            rest (by simpa only [expand, expand_abstract, programWithPrograms] using application)
  termination_by _ _ _ _ _ _ _ arguments _ => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega

  theorem metaArgumentsWithPrograms_congr (first last : Bodies Head) (names : Names S)
      (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
        first (names.operator operator) = last (names.operator operator))
      {ambient : Binding.Ctx S} (firstPrograms lastPrograms : Fin metas.length → Tm Head 0)
      (programs : ∀ index, expand first (firstPrograms index) = expand last (lastPrograms index)) :
      ∀ {source target : Binding.Ctx S}
        (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
        (dependencies : List S.Srt)
        (arguments : Binding.Args (Binding.withMetas S metas)
          (dependencies.map fun sort => ([], sort)) source),
        (fun index => expand first (Schema.compileMetaArgumentsWithPrograms names firstPrograms
          environment valuation dependencies arguments index)) =
        (fun index => expand last (Schema.compileMetaArgumentsWithPrograms names lastPrograms
          environment valuation dependencies arguments index))
    | _, _, _, _, [], .nil => by funext index; exact Fin.elim0 index
    | _, _, environment, valuation, _ :: dependencies, .cons body rest => by
        funext index
        refine Fin.cases ?_ (fun prior => ?_) index
        · simpa only [Schema.compileMetaArgumentsWithPrograms, Fin.cases_zero, programWithPrograms] using
            programWithPrograms_congr first last names operators firstPrograms lastPrograms programs
              (Binding.ContextualAssignment.weakenSub (S := S) [] environment)
              (Binding.liftSub (S := S) valuation []) body
        · simpa only [Schema.compileMetaArgumentsWithPrograms, Fin.cases_succ] using
            congrFun (metaArgumentsWithPrograms_congr first last names operators firstPrograms lastPrograms
              programs environment valuation dependencies rest) prior
  termination_by _ _ _ _ _ arguments => 2 * Binding.argsSize arguments + 1
  decreasing_by
    all_goals simp only [Binding.argsSize]
    all_goals first | omega | have positive := Binding.termSize_pos body; omega
end

/-- Supplying native body functions through a closed primitive interpretation
agrees with compiling those actual functions. The hypotheses concern primitive
operator images and individual body values, not a whole schema compiler. -/
theorem programWithPrograms_specialize (constants action : Bodies Head) (names : Names S)
    (operators : ∀ {sort : S.Srt} (operator : S.Op sort),
      expand action (constants (names.operator operator)) = constants (names.operator operator))
    {ambient source target : Binding.Ctx S} {sort : S.Srt}
    (templates actual : Fin metas.length → Tm Head 0)
    (values : ∀ index, expand action (expand constants (templates index)) = expand constants (actual index))
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    (term : Binding.Term (Binding.withMetas S metas) source sort) :
    expand action (programWithPrograms constants names templates environment valuation term) =
      programWithPrograms constants names actual environment valuation term := by
  change expand action (expand constants _) = _
  rw [expand_comp]
  apply programWithPrograms_congr (fun name => expand action (constants name)) constants names operators
  intro index
  rw [← expand_comp]
  exact values index

end ClosedOperators.Schema
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding


namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding.ClosedOperators

open Mettapedia.OSLF TelescopeAbstraction FormationSensitive ConstantExpansion

variable {S : Binding.Signature} {Head : Type} {types : Types S Head}
  {images : Images S Head} {rules : Rules Head}

theorem spineType_append (types : Types S Head) (dependencies ambient : Binding.Ctx S) (result : Tm Head 0) :
    spineType types (dependencies ++ ambient) result =
      spineType types ambient (spineType types dependencies result) := by
  induction dependencies generalizing result with
  | nil => rfl
  | cons sort dependencies ih => simpa only [List.cons_append, spineType] using ih (closedArrow (types sort) result)

namespace Schema

theorem fixedTemplate_typing (realization : Realization types images rules)
    (constants : Bodies Head) (names : Names S)
    (operators : ∀ {sort : S.Srt} (operator : S.Op sort), constants (names.operator operator) = images operator)
    {M : List (Binding.MetaArity S)} (templates : Fin M.length → Tm Head 0)
    (templateTyped : ∀ index, Typing rules .nil (expand constants (templates index))
      (bindingType types (M.get index).1 (M.get index).2))
    {source : Binding.Ctx S} {sort : S.Srt} (term : Binding.Term (Binding.withMetas S M) source sort) :
    Typing rules (typeContext types source)
      (expand constants (BindingSignatureEmbedding.Schema.fixedTemplate names templates term))
      (liftClosed (types sort)) := by
  apply programWithPrograms_typing realization constants names operators templates
    (ambient := []) ?_ BindingSignatureEmbedding.Schema.emptyEnvironment (fun _ position => .var position) term
  intro index
  simpa only [List.append_nil, closeType_spine, bindingType] using templateTyped index

theorem ambientFunctions_typing (realization : Realization types images rules)
    (constants : Bodies Head) (names : Names S)
    (operators : ∀ {sort : S.Srt} (operator : S.Op sort), constants (names.operator operator) = images operator)
    {M : List (Binding.MetaArity S)} {ambient target : Binding.Ctx S}
    (bodies : Binding.ContextualAssignment S M ambient) (environment : Binding.Sub S ambient target)
    (index : Fin M.length) :
    Typing rules (typeContext types target)
      (expand constants (BindingSignatureEmbedding.Schema.ambientFunctions names
        (BindingSignatureEmbedding.Schema.bodyPrograms names bodies) environment index))
      (liftClosed (bindingType types (M.get index).1 (M.get index).2)) := by
  let result := bindingType types (M.get index).1 (M.get index).2
  have closed := realization.toFormation.closeTerm_typing (realization.typeFormed _)
    _ (realization.compile_typing (bodies index))
  rw [closeType_spine, spineType_append] at closed
  have lifted := FormationCheckedTelescopePrograms.liftClosed_typing closed (typeContext types target)
  have functionTyped : Typing rules (typeContext types target)
      (liftClosed (closeTerm (typeContext types ((M.get index).1 ++ ambient)) (compile images (bodies index))))
      (liftClosed (closeType (typeContext types ambient) (liftClosed result))) := by
    simpa only [closeType_spine, result, bindingType] using lifted
  have applied := FormationCheckedTelescopePrograms.apply_typed
    (context := typeContext types ambient) (type := liftClosed result)
    (realization.compileSub_typed environment) functionTyped
  simpa only [BindingSignatureEmbedding.Schema.ambientFunctions, BindingSignatureEmbedding.Schema.bodyPrograms,
    expand_applyClosed constants _ (typeContext types ambient), expand_liftClosed,
    expand_encodeSub constants names images operators, expand_closeTerm constants _ (typeContext types ((M.get index).1 ++ ambient)),
    expand_encode constants names images operators, subst_liftClosed, result] using applied

/-- The fixed native template's specialization keeps the original derived
operator interpretation and the original source-body compiler as its endpoint. -/
theorem fixedTemplate_specialize {M : List (Binding.MetaArity S)}
    (constants : Bodies Head) (names : Names S) (metavariableNames : Fin M.length → DeclName)
    (positions : DeclName → Option (Fin M.length))
    (operatorPositions : ∀ {sort : S.Srt} (operator : S.Op sort), positions (names.operator operator) = none)
    (metavariablePositions : ∀ index, positions (metavariableNames index) = some index)
    {ambient source target : Binding.Ctx S} (bodies : Binding.ContextualAssignment S M ambient)
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    {sort : S.Srt} (term : Binding.Term (Binding.withMetas S M) source sort) :
    expand constants (ConstantSubstitution.interpret
      (ConstantSubstitution.specializedValues positions (BindingSignatureEmbedding.Schema.ambientFunctions names
        (BindingSignatureEmbedding.Schema.bodyPrograms names bodies) environment))
      (encodeSub names valuation) (BindingSignatureEmbedding.Schema.fixedTemplate names
        (fun index => .const (metavariableNames index)) term)) =
      program constants names bodies environment valuation term :=
  congrArg (expand constants) (BindingSignatureEmbedding.Schema.fixedTemplate_specialize
    names metavariableNames positions operatorPositions metavariablePositions bodies environment valuation term)

theorem fixedTemplate_evidence_checked [DecidableEq Head] {M : List (Binding.MetaArity S)}
    (constants : Bodies Head) (names : Names S) (images : Images S Head)
    (operators : ∀ {sort : S.Srt} (operator : S.Op sort), constants (names.operator operator) = images operator)
    (metavariableNames : Fin M.length → DeclName) (positions : DeclName → Option (Fin M.length))
    (operatorPositions : ∀ {sort : S.Srt} (operator : S.Op sort), positions (names.operator operator) = none)
    (metavariablePositions : ∀ index, positions (metavariableNames index) = some index)
    {ambient source target : Binding.Ctx S} (bodies : Binding.ContextualAssignment S M ambient)
    (environment : Binding.Sub S ambient target) (valuation : Binding.Sub S source target)
    {sort : S.Srt} (term : Binding.Term (Binding.withMetas S M) source sort) :
    (evidence constants names bodies environment valuation term).check (fun _ _ => False)
      FormationCheckedTelescopePrograms.noRoot
      (expand constants (ConstantSubstitution.interpret
        (ConstantSubstitution.specializedValues positions (BindingSignatureEmbedding.Schema.ambientFunctions names
          (BindingSignatureEmbedding.Schema.bodyPrograms names bodies) environment))
        (encodeSub names valuation) (BindingSignatureEmbedding.Schema.fixedTemplate names
          (fun index => .const (metavariableNames index)) term)))
      (compile images (Binding.ContextualAssignment.instantiate bodies environment valuation term)) = true := by
  rw [fixedTemplate_specialize constants names metavariableNames positions operatorPositions metavariablePositions]
  exact evidence_checked constants names images operators bodies environment valuation term

#print axioms ambientFunctions_typing
#print axioms fixedTemplate_typing

end Schema
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding.ClosedOperators

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding

open Mettapedia.OSLF ConstantSubstitution

variable {S : Binding.Signature} {Head : Type}

/-- Literal fresh constructors are normal forms. Full native conversion may
visit non-image intermediates; Church--Rosser still reflects source equality
when the installed computation has no declared roots. Derived operator
interpretations and additional source equations require their own comparison. -/
theorem encode_conversion_reflects_equality (names : Names S)
    (operators : ∀ {sort : S.Srt}, Function.Injective (names.operator (sort := sort)))
    (rules : Rules Head) (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq)
    {source : Binding.Ctx S} {sort : S.Srt} {first last : Binding.Term S source sort}
    (conversion : Conv rules.headEq (encode names first) (encode names last) rules.computation) :
    first = last := by
  have rootFree : RootFree rules.computation := by
    intro scope left right step
    rw [empty] at step
    exact step
  obtain ⟨common, firstPath, lastPath⟩ := EmptyRootConversion.churchRosser rules empty symmetric conversion
  have normalPath : ∀ {common : Tm Head source.length} (term : Binding.Term S source sort)
      (path : Relation.ReflTransGen (StepCore rules.computation rules.headEq) (encode names term) common),
      common = encode names term := by
    intro current term path
    induction path with
    | refl => rfl
    | tail path step ih => rw [ih] at step; exact False.elim (encode_noStep names rootFree term step)
  exact encode_injective_of_operator_names names @operators first last
    ((normalPath first firstPath).symm.trans (normalPath last lastPath))

theorem encode_conversion_iff_eq (names : Names S)
    (operators : ∀ {sort : S.Srt}, Function.Injective (names.operator (sort := sort)))
    (rules : Rules Head) (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq)
    {source : Binding.Ctx S} {sort : S.Srt} (first last : Binding.Term S source sort) :
    Conv rules.headEq (encode names first) (encode names last) rules.computation ↔ first = last := by
  constructor
  · exact encode_conversion_reflects_equality names @operators rules empty symmetric
  · intro equal; cases equal; exact .refl _

theorem encoded_checked_iff_eq [DecidableEq Head] (names : Names S)
    (operators : ∀ {sort : S.Srt}, Function.Injective (names.operator (sort := sort)))
    (rules : Rules Head) [DecidableRel rules.headEq] (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq)
    {source : Binding.Ctx S} {sort : S.Srt} (first last : Binding.Term S source sort) :
    (∃ code : StructuralConversionCode.Code Head (fun _ => Empty) source.length,
      code.check rules.headEq FormationCheckedTelescopePrograms.noRoot (encode names first) (encode names last) = true) ↔
        first = last := by
  constructor
  · rintro ⟨code, checked⟩
    exact encode_conversion_reflects_equality names @operators rules empty symmetric
      (StructuralConversionCode.Code.check_sound (StructuralConversionCode.RootDecoder.ofEmpty rules.computation empty) checked)
  · intro equal
    cases equal
    exact ⟨.refl _, StructuralConversionCode.Code.check_refl rules.headEq FormationCheckedTelescopePrograms.noRoot _⟩

theorem encode_conversion_iff_eq_of_rootFree (names : Names S)
    (operators : ∀ {sort : S.Srt}, Function.Injective (names.operator (sort := sort)))
    (rules : Rules Head) (empty : RootFree rules.computation) (symmetric : Std.Symm rules.headEq)
    {source : Binding.Ctx S} {sort : S.Srt} (first last : Binding.Term S source sort) :
    Conv rules.headEq (encode names first) (encode names last) rules.computation ↔ first = last :=
  encode_conversion_iff_eq names @operators rules empty.eq_empty symmetric first last


end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.BindingSignatureEmbedding
