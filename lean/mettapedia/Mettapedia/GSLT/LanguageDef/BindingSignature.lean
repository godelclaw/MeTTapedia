import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.OSLF.Syntax.BindingSignature

/-!
# Binding syntax derived from a language definition

Constructor operators retain their membership in the authored `LanguageDef`.
Binding arities are determined by its existing parameter typing convention:
an abstraction binds its domain, while a multiple abstraction ranges over the
finite repetitions of its domain. No second constructor inventory is authored.

The structural lambda, substitution, and collection forms are precisely the
representation forms of `WellSorted.HasType`. Collection operators here have
no schema rest; declared metavariables and their sequence substitutions belong
to the separate metavariable extension, not to object operator names.

Erasure is proved against the existing typing judgment. This module does not
yet derive conditional rule instantiation or its executable matcher.
-/

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.WellSorted

set_option autoImplicit false

/-- The binding argument specified by one authored parameter. The constructors
follow `parameterType?`, including its established same-sort shorthand. -/
inductive ParameterScope : TermParam → List TypeExpr → TypeExpr → Type where
  | simple (name : String) (type : TypeExpr) :
      ParameterScope (.simple name type) [] type
  | abstraction (binder : Option String) (name : String)
      (domain codomain : TypeExpr) :
      ParameterScope (.abstractionNamed binder name (.arrow domain codomain))
        [domain] codomain
  | abstractionBase (binder : Option String) (name sort : String) :
      ParameterScope (.abstractionNamed binder name (.base sort))
        [.base sort] (.base sort)
  | multiAbstraction (binders : List String) (name : String)
      (domain codomain : TypeExpr) (count : Nat) :
      ParameterScope
        (.multiAbstractionNamed binders name (.arrow (.multiBinder domain) codomain))
        (List.replicate count domain) codomain
  | multiAbstractionBase (binders : List String) (name sort : String) (count : Nat) :
      ParameterScope (.multiAbstractionNamed binders name (.base sort))
        (List.replicate count (.base sort)) (.base sort)

/-- Parameter order and every binding prefix come from the authored list. -/
inductive ParameterScopes : List TermParam → List (List TypeExpr × TypeExpr) → Type where
  | nil : ParameterScopes [] []
  | cons {parameter : TermParam} {parameters : List TermParam}
      {binders : List TypeExpr} {bodyType : TypeExpr}
      {arity : List (List TypeExpr × TypeExpr)} :
      ParameterScope parameter binders bodyType → ParameterScopes parameters arity →
      ParameterScopes (parameter :: parameters) ((binders, bodyType) :: arity)

/-- Reinsert the representation binder removed by an intrinsic binding arity. -/
def ParameterScope.wrap {parameter : TermParam} {binders : List TypeExpr}
    {bodyType : TypeExpr} (scope : ParameterScope parameter binders bodyType)
    (body : Pattern) : Pattern :=
  match scope with
  | .simple _ _ => body
  | .abstraction _ _ _ _ => .lambda none body
  | .abstractionBase _ _ _ => .lambda none body
  | .multiAbstraction _ _ _ _ count => .multiLambda count [] body
  | .multiAbstractionBase _ _ _ count => .multiLambda count [] body

theorem ParameterScope.wrap_typed
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {parameter : TermParam} {binders : List TypeExpr} {bodyType : TypeExpr}
    (scope : ParameterScope parameter binders bodyType) {body : Pattern}
    (typed : HasType language free (binders ++ bound) body bodyType) :
    ∃ expected, MatchesParameterRepresentation parameter (scope.wrap body) ∧
      parameterType? parameter = some expected ∧
      HasType language free bound (scope.wrap body) expected := by
  cases scope with
  | simple name type => exact ⟨_, trivial, rfl, typed⟩
  | abstraction binder name domain codomain =>
      exact ⟨_, trivial, rfl, HasType.lambda typed⟩
  | abstractionBase binder name sort =>
      exact ⟨.arrow (.base sort) (.base sort), trivial, rfl, HasType.lambda typed⟩
  | multiAbstraction binders name domain codomain count =>
      exact ⟨_, trivial, rfl,
        HasType.multiLambda typed⟩
  | multiAbstractionBase binders name sort count =>
      exact ⟨.arrow (.multiBinder (.base sort)) (.base sort), trivial, rfl,
        HasType.multiLambda typed⟩

/-- Object operators derived from constructor membership and the existing
structural representation forms. Binding counts index the multiple-binder
family; they do not restrict the general parameter declaration. -/
inductive Operator (language : LanguageDef) : TypeExpr → Type where
  | constructor (rule : GrammarRule) (member : rule ∈ language.terms)
      (ordinary : ¬ UsesBareCollection rule)
      {arity : List (List TypeExpr × TypeExpr)}
      (parameters : ParameterScopes rule.params arity) :
      Operator language (.base rule.category)
  | collectionConstructor (rule : GrammarRule) (member : rule ∈ language.terms)
      (parameterName : String) (kind : CollType) (elementType : TypeExpr)
      (shape : rule.bareParams = [.simple parameterName (.collection kind elementType)])
      (count : Nat) : Operator language (.base rule.category)
  | lambda (domain codomain : TypeExpr) : Operator language (.arrow domain codomain)
  | multiLambda (domain codomain : TypeExpr) (count : Nat) :
      Operator language (.arrow (.multiBinder domain) codomain)
  | subst (domain codomain : TypeExpr) : Operator language codomain
  | collection (kind : CollType) (elementType : TypeExpr) (count : Nat) :
      Operator language (.collection kind elementType)

/-- The intrinsic signature of the authored constructor declarations and their
typed representation forms. Sorts are the existing `TypeExpr` carrier. -/
abbrev signatureOf (language : LanguageDef) : Signature where
  Srt := TypeExpr
  Op := Operator language
  arity := fun {_} operator => match operator with
    | .constructor _ _ _ (arity := arity) _ => arity
    | .collectionConstructor _ _ _ _ elementType _ count =>
        List.replicate count ([], elementType)
    | .lambda domain codomain => [([domain], codomain)]
    | .multiLambda domain codomain count => [(List.replicate count domain, codomain)]
    | .subst domain codomain => [([domain], codomain), ([], domain)]
    | .collection _ elementType count => List.replicate count ([], elementType)

/-- A variable's index ignores its sort, while retaining its context position. -/
def variableIndex {SortType : Type} : {bound : List SortType} → {sort : SortType} →
    Var bound sort → Nat
  | _, _, .zero => 0
  | _, _, .succ position => variableIndex position + 1

theorem variableIndex_lookup {SortType : Type} :
    ∀ {bound : List SortType} {sort : SortType} (position : Var bound sort),
      bound[variableIndex position]? = some sort
  | _, _, .zero => rfl
  | _, _, .succ position => variableIndex_lookup position

mutual
def erase {language : LanguageDef} : {bound : List TypeExpr} → {type : TypeExpr} →
    Term (signatureOf language) bound type → Pattern
  | _, _, .var position => .bvar (variableIndex position)
  | _, _, .op operator arguments =>
      match operator with
      | .constructor rule _ _ parameters =>
          .apply rule.label (eraseConstructorArguments parameters arguments)
      | .collectionConstructor _ _ _ kind _ _ _ =>
          .collection kind (eraseArguments arguments) none
      | .lambda _ _ =>
          match arguments with
          | .cons body .nil => .lambda none (erase body)
      | .multiLambda _ _ count =>
          match arguments with
          | .cons body .nil => .multiLambda count [] (erase body)
      | .subst _ _ =>
          match arguments with
          | .cons body (.cons replacement .nil) => .subst (erase body) (erase replacement)
      | .collection kind _ _ => .collection kind (eraseArguments arguments) none

def eraseArguments {language : LanguageDef} :
    {arity : List (List TypeExpr × TypeExpr)} → {bound : List TypeExpr} →
    Args (signatureOf language) arity bound → List Pattern
  | _, _, .nil => []
  | _, _, .cons head tail => erase head :: eraseArguments tail

def eraseConstructorArguments {language : LanguageDef} :
    {parameters : List TermParam} → {arity : List (List TypeExpr × TypeExpr)} →
    {bound : List TypeExpr} → ParameterScopes parameters arity →
    Args (signatureOf language) arity bound → List Pattern
  | _, _, _, .nil, .nil => []
  | _, _, _, .cons scope scopes, .cons head tail =>
      scope.wrap (erase head) :: eraseConstructorArguments scopes tail
end

theorem elements_typed_of_replicate
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {elementType : TypeExpr} : ∀ {count : Nat} {elements : List Pattern},
      List.Forall₂
        (fun (slot : List TypeExpr × TypeExpr) element =>
          HasType language free (slot.1 ++ bound) element slot.2)
        (List.replicate count ([], elementType)) elements →
      ElementsHaveType language free bound elements elementType
  | 0, _, .nil => .nil _ _
  | _ + 1, _, .cons head tail =>
      .cons head (elements_typed_of_replicate tail)

mutual
/-- Every erased intrinsic term satisfies the original language's typing
judgment in the same ordered context. -/
theorem erase_typed {language : LanguageDef} :
    ∀ {bound : List TypeExpr} {type : TypeExpr}
      (term : Term (signatureOf language) bound type),
      HasType language FreeTypeContext.empty bound (erase term) type
  | _, _, .var position => .bvar (variableIndex_lookup position)
  | _, _, .op (.constructor _ member ordinary parameters) arguments =>
      .constructor member ordinary (eraseConstructorArguments_typed parameters arguments)
  | _, _, .op (.collectionConstructor _ member _ _ _ shape _) arguments =>
      .collectionConstructor member shape
        (elements_typed_of_replicate (eraseArguments_typed arguments))
  | _, _, .op (.lambda _ _) arguments =>
      match arguments with
      | .cons body .nil => .lambda (erase_typed body)
  | _, _, .op (.multiLambda _ _ _) arguments =>
      match arguments with
      | .cons body .nil => .multiLambda (erase_typed body)
  | _, _, .op (.subst _ _) arguments =>
      match arguments with
      | .cons body (.cons replacement .nil) =>
          .subst (erase_typed body) (erase_typed replacement)
  | _, _, .op (.collection _ _ _) arguments =>
      .collection (elements_typed_of_replicate (eraseArguments_typed arguments))

theorem eraseArguments_typed {language : LanguageDef} :
    ∀ {arity : List (List TypeExpr × TypeExpr)} {bound : List TypeExpr}
      (arguments : Args (signatureOf language) arity bound),
      List.Forall₂
        (fun slot argument =>
          HasType language FreeTypeContext.empty (slot.1 ++ bound) argument slot.2)
        arity (eraseArguments arguments)
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (erase_typed head) (eraseArguments_typed tail)

theorem eraseConstructorArguments_typed {language : LanguageDef} :
    ∀ {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)}
      {bound : List TypeExpr} (scopes : ParameterScopes parameters arity)
      (arguments : Args (signatureOf language) arity bound),
      ArgumentsHaveTypes language FreeTypeContext.empty bound
        (eraseConstructorArguments scopes arguments) parameters
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons scope scopes, .cons head tail => by
      obtain ⟨expected, representation, expectedType, typed⟩ :=
        scope.wrap_typed (erase_typed head)
      exact .cons representation expectedType typed
        (eraseConstructorArguments_typed scopes tail)
end

theorem erase_wellScoped {language : LanguageDef} {bound : List TypeExpr}
    {type : TypeExpr} (term : Term (signatureOf language) bound type) :
    (erase term).isWellScopedAt bound.length = true :=
  (erase_typed term).isWellScopedAt

theorem ParameterScope.heq_of_binders_eq {parameter : TermParam}
    {firstBinders secondBinders : List TypeExpr} {firstType secondType : TypeExpr}
    (first : ParameterScope parameter firstBinders firstType)
    (second : ParameterScope parameter secondBinders secondType)
    (same : firstBinders = secondBinders) : HEq first second := by
  cases first <;> cases second
  all_goals first
    | exact HEq.rfl
    | have counts := congrArg List.length same
      simp only [List.length_replicate] at counts
      cases counts
      exact HEq.rfl

instance {parameter : TermParam} {binders : List TypeExpr} {type : TypeExpr} :
    Subsingleton (ParameterScope parameter binders type) :=
  ⟨fun first second => eq_of_heq (ParameterScope.heq_of_binders_eq first second rfl)⟩

instance {parameter : TermParam} {binders : List TypeExpr} {type : TypeExpr} :
    DecidableEq (ParameterScope parameter binders type) := fun first second =>
  .isTrue (Subsingleton.elim first second)

instance {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)} :
    Subsingleton (ParameterScopes parameters arity) where
  allEq first := by
    induction first with
    | nil => intro second; cases second; rfl
    | cons head tail ih =>
        intro second
        cases second with
        | cons other rest =>
            have heads := Subsingleton.elim head other
            have tails := ih rest
            cases heads
            cases tails
            rfl

instance {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)} :
    DecidableEq (ParameterScopes parameters arity) := fun first second =>
  .isTrue (Subsingleton.elim first second)

/-- A structural comparison projection; it retains all constructor metadata and
actual binding arities. No raw erasure or semantic equality is consulted. -/
private def operatorKey {language : LanguageDef} : {sort : TypeExpr} → Operator language sort →
    ((GrammarRule × List (List TypeExpr × TypeExpr)) ⊕
      (GrammarRule × String × CollType × TypeExpr × Nat)) ⊕
      (((TypeExpr × TypeExpr) ⊕ (TypeExpr × TypeExpr × Nat)) ⊕
        ((TypeExpr × TypeExpr) ⊕ (CollType × TypeExpr × Nat)))
  | _, .constructor rule _ _ (arity := arity) _ => .inl (.inl (rule, arity))
  | _, .collectionConstructor rule _ parameter kind element _ count =>
      .inl (.inr (rule, parameter, kind, element, count))
  | _, .lambda domain codomain => .inr (.inl (.inl (domain, codomain)))
  | _, .multiLambda domain codomain count => .inr (.inl (.inr (domain, codomain, count)))
  | _, .subst domain codomain => .inr (.inr (.inl (domain, codomain)))
  | _, .collection kind element count => .inr (.inr (.inr (kind, element, count)))

private theorem operatorKey_heq {language : LanguageDef} {firstSort secondSort : TypeExpr}
    (first : Operator language firstSort) (second : Operator language secondSort)
    (same : operatorKey first = operatorKey second) : HEq first second := by
  cases first <;> cases second <;>
    simp only [operatorKey, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
      Prod.mk.injEq] at same
  case constructor.constructor firstRow firstMember firstOrdinary firstArity firstScopes
      secondRow secondMember secondOrdinary secondArity secondScopes =>
    rcases same with ⟨rfl, rfl⟩
    have scopes := Subsingleton.elim firstScopes secondScopes
    cases scopes
    rfl
  case collectionConstructor.collectionConstructor =>
    rcases same with ⟨rfl, rfl, rfl, rfl, rfl⟩
    rfl
  case lambda.lambda => rcases same with ⟨rfl, rfl⟩; rfl
  case multiLambda.multiLambda => rcases same with ⟨rfl, rfl, rfl⟩; rfl
  case subst.subst => rcases same with ⟨rfl, rfl⟩; rfl
  case collection.collection => rcases same with ⟨rfl, rfl, rfl⟩; rfl

instance {language : LanguageDef} {sort : TypeExpr} : DecidableEq (Operator language sort) := by
  letI : DecidableEq (GrammarRule × List (List TypeExpr × TypeExpr)) := inferInstance
  letI : DecidableEq (GrammarRule × String × CollType × TypeExpr × Nat) := inferInstance
  letI : DecidableEq (TypeExpr × TypeExpr) := inferInstance
  letI : DecidableEq (TypeExpr × TypeExpr × Nat) := inferInstance
  letI : DecidableEq (CollType × TypeExpr × Nat) := inferInstance
  letI : DecidableEq ((GrammarRule × List (List TypeExpr × TypeExpr)) ⊕
    (GrammarRule × String × CollType × TypeExpr × Nat)) := inferInstance
  letI : DecidableEq ((TypeExpr × TypeExpr) ⊕ (TypeExpr × TypeExpr × Nat)) := inferInstance
  letI : DecidableEq ((TypeExpr × TypeExpr) ⊕ (CollType × TypeExpr × Nat)) := inferInstance
  exact fun first second => if same : operatorKey first = operatorKey second then
    .isTrue (eq_of_heq (operatorKey_heq first second same))
  else .isFalse (fun equal => same (congrArg operatorKey equal))

end Mettapedia.GSLT.LanguageDef.BindingSyntax


set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem variableIndex_exists_of_lookup {SortType : Type} :
    ∀ (bound : List SortType) (index : Nat) (sort : SortType),
      bound[index]? = some sort → ∃ position : Var bound sort, variableIndex position = index
  | [], index, _, lookup => by cases index <;> cases lookup
  | head :: tail, 0, sort, lookup => by
      cases Option.some.inj lookup
      exact ⟨.zero, rfl⟩
  | _ :: tail, index + 1, sort, lookup => by
      obtain ⟨position, same⟩ := variableIndex_exists_of_lookup tail index sort lookup
      exact ⟨.succ position, congrArg (· + 1) same⟩

mutual
/-- Independent authored typing and object formation supply an intrinsic
term with the exact original source erasure. No type-inference search is
assumed; ambiguous constructor declarations retain the supplied witness. -/
theorem typedObject_exists {language : LanguageDef} {bound : List TypeExpr}
    {source : Pattern} {sort : TypeExpr}
    (typed : HasType language FreeTypeContext.empty bound source sort)
    (canonical : source.hasCanonicalBinderMetadata = true)
    (object : isObjectPattern source = true) :
    ∃ term : Term (signatureOf language) bound sort, erase term = source := by
  cases typed with
  | bvar lookup =>
      obtain ⟨position, same⟩ := variableIndex_exists_of_lookup _ _ _ lookup
      exact ⟨.var position, congrArg Pattern.bvar same⟩
  | fvar lookup => cases lookup
  | constructor member ordinary arguments =>
      obtain ⟨arity, scopes, values, readback⟩ :=
        typedObjectArguments_exists arguments canonical object
      exact ⟨.op (.constructor _ member ordinary scopes) values,
        congrArg (Pattern.apply _) readback⟩
  | @lambda bound binder body domain codomain bodyTyped =>
      cases binder with
      | some name => simp [Pattern.hasCanonicalBinderMetadata] at canonical
      | none =>
          have bodyCanonical : body.hasCanonicalBinderMetadata = true := by
            simpa [Pattern.hasCanonicalBinderMetadata] using canonical
          obtain ⟨value, readback⟩ := typedObject_exists bodyTyped bodyCanonical object
          exact ⟨.op (.lambda domain codomain) (.cons value .nil), congrArg (Pattern.lambda none) readback⟩
  | @multiLambda bound count names body domain codomain bodyTyped =>
      cases names with
      | cons name names => simp [Pattern.hasCanonicalBinderMetadata] at canonical
      | nil =>
          have bodyCanonical : body.hasCanonicalBinderMetadata = true := by
            simpa [Pattern.hasCanonicalBinderMetadata] using canonical
          obtain ⟨value, readback⟩ := typedObject_exists bodyTyped bodyCanonical object
          exact ⟨.op (.multiLambda domain codomain count) (.cons value .nil),
            congrArg (Pattern.multiLambda count []) readback⟩
  | subst bodyTyped replacementTyped => cases object
  | @collection bound kind elements rest elementType elementsTyped =>
      cases rest with
      | some name => simp [isObjectPattern] at object
      | none =>
          have elementsObject : isObjectPatternList elements = true := by
            simpa only [isObjectPattern, Option.isNone_none, Bool.true_and] using object
          obtain ⟨values, readback⟩ := typedObjectElements_exists elementsTyped canonical elementsObject
          exact ⟨.op (.collection kind elementType elements.length) values,
            congrArg (fun values => Pattern.collection kind values none) readback⟩
  | @collectionConstructor bound declaration name kind elements rest elementType member shape elementsTyped =>
      cases rest with
      | some name => simp [isObjectPattern] at object
      | none =>
          have elementsObject : isObjectPatternList elements = true := by
            simpa only [isObjectPattern, Option.isNone_none, Bool.true_and] using object
          obtain ⟨values, readback⟩ := typedObjectElements_exists elementsTyped canonical elementsObject
          exact ⟨.op (.collectionConstructor declaration member name kind elementType shape elements.length) values,
            congrArg (fun values => Pattern.collection kind values none) readback⟩
termination_by sizeOf source

theorem typedObjectArguments_exists {language : LanguageDef} {bound : List TypeExpr}
    {sources : List Pattern} {parameters : List TermParam}
    (typed : ArgumentsHaveTypes language FreeTypeContext.empty bound sources parameters)
    (canonical : Pattern.hasCanonicalBinderMetadataList sources = true)
    (object : isObjectPatternList sources = true) :
    ∃ (arity : List (List TypeExpr × TypeExpr)) (scopes : ParameterScopes parameters arity)
      (arguments : Args (signatureOf language) arity bound),
      eraseConstructorArguments scopes arguments = sources := by
  cases typed with
  | nil => exact ⟨[], .nil, .nil, rfl⟩
  | @cons bound source sources parameter parameters expected representation expectedType headTyped tailTyped =>
      have canonicalParts := (Bool.and_eq_true_iff).mp canonical
      have objectParts := (Bool.and_eq_true_iff).mp object
      obtain ⟨arity, scopes, rest, restRead⟩ :=
        typedObjectArguments_exists tailTyped canonicalParts.2 objectParts.2
      cases parameter with
      | simple name type =>
          cases Option.some.inj expectedType
          obtain ⟨value, readback⟩ := typedObject_exists headTyped canonicalParts.1 objectParts.1
          exact ⟨([], expected) :: arity, .cons (.simple name expected) scopes,
            .cons value rest, congrArg₂ List.cons readback restRead⟩
      | abstractionNamed binder name type =>
          obtain ⟨body, rfl⟩ :=
            (matchesParameterRepresentation_abstractionNamed_iff binder name type source).mp representation
          cases type with
          | base sort =>
              cases Option.some.inj expectedType
              cases headTyped with
              | lambda bodyTyped =>
                  have bodyCanonical : body.hasCanonicalBinderMetadata = true := by
                    simpa [Pattern.hasCanonicalBinderMetadata] using canonicalParts.1
                  obtain ⟨value, readback⟩ := typedObject_exists bodyTyped bodyCanonical objectParts.1
                  exact ⟨([.base sort], .base sort) :: arity,
                    .cons (.abstractionBase binder name sort) scopes, .cons value rest,
                    congrArg₂ List.cons (congrArg (Pattern.lambda none) readback) restRead⟩
          | arrow domain codomain =>
              cases Option.some.inj expectedType
              cases headTyped with
              | lambda bodyTyped =>
                  have bodyCanonical : body.hasCanonicalBinderMetadata = true := by
                    simpa [Pattern.hasCanonicalBinderMetadata] using canonicalParts.1
                  obtain ⟨value, readback⟩ := typedObject_exists bodyTyped bodyCanonical objectParts.1
                  exact ⟨([domain], codomain) :: arity,
                    .cons (.abstraction binder name domain codomain) scopes, .cons value rest,
                    congrArg₂ List.cons (congrArg (Pattern.lambda none) readback) restRead⟩
          | multiBinder domain => cases expectedType
          | collection kind type => cases expectedType
      | multiAbstractionNamed names name type =>
          obtain ⟨count, body, rfl⟩ :=
            (matchesParameterRepresentation_multiAbstractionNamed_iff names name type source).mp representation
          cases type with
          | base sort =>
              cases Option.some.inj expectedType
              cases headTyped with
              | multiLambda bodyTyped =>
                  have bodyCanonical : body.hasCanonicalBinderMetadata = true := by
                    simpa [Pattern.hasCanonicalBinderMetadata] using canonicalParts.1
                  obtain ⟨value, readback⟩ := typedObject_exists bodyTyped bodyCanonical objectParts.1
                  exact ⟨(List.replicate count (.base sort), .base sort) :: arity,
                    .cons (.multiAbstractionBase names name sort count) scopes, .cons value rest,
                    congrArg₂ List.cons (congrArg (Pattern.multiLambda count []) readback) restRead⟩
          | arrow domain codomain =>
              cases domain with
              | multiBinder domain =>
                  cases Option.some.inj expectedType
                  cases headTyped with
                  | multiLambda bodyTyped =>
                      have bodyCanonical : body.hasCanonicalBinderMetadata = true := by
                        simpa [Pattern.hasCanonicalBinderMetadata] using canonicalParts.1
                      obtain ⟨value, readback⟩ := typedObject_exists bodyTyped bodyCanonical objectParts.1
                      exact ⟨(List.replicate count domain, codomain) :: arity,
                        .cons (.multiAbstraction names name domain codomain count) scopes, .cons value rest,
                        congrArg₂ List.cons (congrArg (Pattern.multiLambda count []) readback) restRead⟩
              | base _ => cases expectedType
              | arrow _ _ => cases expectedType
              | collection _ _ => cases expectedType
          | multiBinder domain => cases expectedType
          | collection kind type => cases expectedType
termination_by sizeOf sources

theorem typedObjectElements_exists {language : LanguageDef} {bound : List TypeExpr}
    {sources : List Pattern} {sort : TypeExpr}
    (typed : ElementsHaveType language FreeTypeContext.empty bound sources sort)
    (canonical : Pattern.hasCanonicalBinderMetadataList sources = true)
    (object : isObjectPatternList sources = true) :
    ∃ arguments : Args (signatureOf language) (List.replicate sources.length ([], sort)) bound,
      eraseArguments arguments = sources := by
  cases typed with
  | nil => exact ⟨.nil, rfl⟩
  | cons headTyped tailTyped =>
      have canonicalParts := (Bool.and_eq_true_iff).mp canonical
      have objectParts := (Bool.and_eq_true_iff).mp object
      obtain ⟨value, headRead⟩ := typedObject_exists headTyped canonicalParts.1 objectParts.1
      obtain ⟨rest, tailRead⟩ := typedObjectElements_exists tailTyped canonicalParts.2 objectParts.2
      exact ⟨.cons value rest, congrArg₂ List.cons headRead tailRead⟩
termination_by sizeOf sources
end

/-- On the independently stated canonical object profile, exact intrinsic
representability is precisely the original authored sorting judgment. -/
theorem typedObject_iff_represented {language : LanguageDef} {bound : List TypeExpr}
    {source : Pattern} {sort : TypeExpr}
    (canonical : source.hasCanonicalBinderMetadata = true)
    (object : isObjectPattern source = true) :
    HasType language FreeTypeContext.empty bound source sort ↔
      ∃ term : Term (signatureOf language) bound sort, erase term = source := by
  constructor
  · exact fun typed => typedObject_exists typed canonical object
  · rintro ⟨term, rfl⟩
    exact erase_typed term
end Mettapedia.GSLT.LanguageDef.BindingSyntax

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.SourceReadback

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.WellSorted
set_option autoImplicit false
variable {language : LanguageDef}

/-- Read the body of the actual declared binding slot. A simple slot retains
its whole source value; binding slots require their established wrapper. -/
def readBody? {parameter : TermParam} {binders : List TypeExpr} {type : TypeExpr}
    (scope : ParameterScope parameter binders type) (source : Pattern) : Option Pattern :=
  match scope with
  | .simple _ _ => some source
  | .abstraction _ _ _ _ | .abstractionBase _ _ _ =>
      match source with
      | .lambda none body => some body
      | _ => none
  | .multiAbstraction _ _ _ _ count | .multiAbstractionBase _ _ _ count =>
      match source with
      | .multiLambda actual [] body => if count == actual then some body else none
      | _ => none

theorem readBody_eq_wrap {parameter : TermParam} {binders : List TypeExpr} {type : TypeExpr}
    (scope : ParameterScope parameter binders type) {source body : Pattern}
    (readback : readBody? scope source = some body) : source = scope.wrap body := by
  cases scope with
  | simple => exact Option.some.inj readback
  | abstraction | abstractionBase =>
      cases source <;> simp only [readBody?,reduceCtorEq] at readback
      case lambda display pattern =>
        cases display <;> simp only [reduceCtorEq] at readback
        case none => cases readback; rfl
  | multiAbstraction _ _ _ _ count | multiAbstractionBase _ _ _ count =>
      cases source <;> simp only [readBody?,reduceCtorEq] at readback
      case multiLambda actual displays pattern =>
        cases displays <;> simp only [reduceCtorEq] at readback
        case nil =>
          split at readback
          next same =>
            have countSame : count = actual := beq_iff_eq.mp same
            cases countSame
            cases Option.some.inj readback
            rfl
          next => cases readback

mutual
/-- Compare a checked intrinsic term with its submitted source presentation.
Display names and collection tails retain precisely the freedom of HasType;
binding parameter wrappers follow their actual ParameterScope. -/
def check : {bound : List TypeExpr} → {type : TypeExpr} →
    Term (signatureOf language) bound type → Pattern → Bool
  | _,_,.var position,source =>
      match source with
      | .bvar index => variableIndex position == index
      | _ => false
  | _,_,.op operator arguments,source =>
      match operator with
      | .constructor rule _ _ scopes =>
          match source with
          | .apply head patterns => (rule.label == head) && checkConstructorArguments scopes arguments patterns
          | _ => false
      | .collectionConstructor _ _ _ kind _ _ _ =>
          match source with
          | .collection actual patterns _ => (kind == actual) && checkArguments arguments patterns
          | _ => false
      | .lambda _ _ =>
          match arguments with
          | .cons body .nil =>
              match source with
              | .lambda _ pattern => check body pattern
              | _ => false
      | .multiLambda _ _ count =>
          match arguments with
          | .cons body .nil =>
              match source with
              | .multiLambda actual _ pattern => (count == actual) && check body pattern
              | _ => false
      | .subst _ _ =>
          match arguments with
          | .cons body (.cons replacement .nil) =>
              match source with
              | .subst pattern argument => check body pattern && check replacement argument
              | _ => false
      | .collection kind _ _ =>
          match source with
          | .collection actual patterns _ => (kind == actual) && checkArguments arguments patterns
          | _ => false

/-- Readback preserves every argument position and its actual binding prefix. -/
def checkArguments : {arity : List (List TypeExpr × TypeExpr)} → {bound : List TypeExpr} →
    Args (signatureOf language) arity bound → List Pattern → Bool
  | _,_,.nil,sources => sources.isEmpty
  | _,_,.cons head tail,sources =>
      match sources with
      | [] => false
      | source::sources => check head source && checkArguments tail sources

def checkConstructorArguments : {parameters : List TermParam} →
    {arity : List (List TypeExpr × TypeExpr)} → {bound : List TypeExpr} →
    ParameterScopes parameters arity → Args (signatureOf language) arity bound → List Pattern → Bool
  | _,_,_,.nil,.nil,sources => sources.isEmpty
  | _,_,_,.cons scope scopes,.cons head tail,sources =>
      match sources with
      | [] => false
      | source::sources =>
          match readBody? scope source with
          | none => false
          | some body => check head body && checkConstructorArguments scopes tail sources
end

mutual
/-- Successful readback reconstructs the original complete source typing
judgment, including substitution and submitted display/tail metadata. -/
theorem typed : ∀ {bound : List TypeExpr} {type : TypeExpr}
    (term : Term (signatureOf language) bound type) (source : Pattern),
    check term source = true → HasType language FreeTypeContext.empty bound source type
  | _,_,.var position,source,accepted => by
      cases source <;> simp only [check,Bool.false_eq_true] at accepted
      case bvar index =>
        have same : variableIndex position = index := beq_iff_eq.mp accepted
        exact .bvar (same ▸ variableIndex_lookup position)
  | _,_,.op (.constructor rule member ordinary scopes) arguments,source,accepted => by
      cases source <;> simp only [check,Bool.false_eq_true] at accepted
      case apply label patterns =>
        obtain ⟨same,children⟩ := Bool.and_eq_true_iff.mp accepted
        have labelSame : rule.label = label := beq_iff_eq.mp same
        subst label
        exact .constructor member ordinary (constructorArgumentsTyped scopes arguments patterns children)
  | _,_,.op (.collectionConstructor rule member parameter kind elementType shape count) arguments,source,accepted => by
      cases source <;> simp only [check,Bool.false_eq_true] at accepted
      case collection actual patterns rest =>
        obtain ⟨same,children⟩ := Bool.and_eq_true_iff.mp accepted
        have kindSame : kind = actual := beq_iff_eq.mp same
        cases kindSame
        exact .collectionConstructor member shape (elements_typed_of_replicate (argumentsTyped arguments patterns children))
  | _,_,.op (.lambda _ _) arguments,source,accepted =>
      match arguments with
      | .cons body .nil => by
          cases source <;> simp only [check,Bool.false_eq_true] at accepted
          case lambda display pattern => exact .lambda (typed body pattern accepted)
  | _,_,.op (.multiLambda _ _ count) arguments,source,accepted =>
      match arguments with
      | .cons body .nil => by
          cases source <;> simp only [check,Bool.false_eq_true] at accepted
          case multiLambda actual displays pattern =>
            obtain ⟨same,child⟩ := Bool.and_eq_true_iff.mp accepted
            have countSame : count = actual := beq_iff_eq.mp same
            cases countSame
            exact .multiLambda (typed body pattern child)
  | _,_,.op (.subst _ _) arguments,source,accepted =>
      match arguments with
      | .cons body (.cons replacement .nil) => by
          cases source <;> simp only [check,Bool.false_eq_true] at accepted
          case subst pattern argument =>
            obtain ⟨first,second⟩ := Bool.and_eq_true_iff.mp accepted
            exact .subst (typed body pattern first) (typed replacement argument second)
  | _,_,.op (.collection kind _ _) arguments,source,accepted => by
      cases source <;> simp only [check,Bool.false_eq_true] at accepted
      case collection actual patterns rest =>
        obtain ⟨same,children⟩ := Bool.and_eq_true_iff.mp accepted
        have kindSame : kind = actual := beq_iff_eq.mp same
        cases kindSame
        exact .collection (elements_typed_of_replicate (argumentsTyped arguments patterns children))

theorem argumentsTyped : ∀ {arity : List (List TypeExpr × TypeExpr)} {bound : List TypeExpr}
    (arguments : Args (signatureOf language) arity bound) (sources : List Pattern),
    checkArguments arguments sources = true →
      List.Forall₂ (fun slot source => HasType language FreeTypeContext.empty (slot.1 ++ bound) source slot.2)
        arity sources
  | _,_,.nil,sources,accepted => by
      cases sources with
      | nil => exact .nil
      | cons => cases accepted
  | _,_,.cons head tail,sources,accepted => by
      cases sources with
      | nil => cases accepted
      | cons source sources =>
          obtain ⟨first,rest⟩ := Bool.and_eq_true_iff.mp accepted
          exact .cons (typed head source first) (argumentsTyped tail sources rest)

theorem constructorArgumentsTyped : ∀ {parameters : List TermParam}
    {arity : List (List TypeExpr × TypeExpr)} {bound : List TypeExpr}
    (scopes : ParameterScopes parameters arity)
    (arguments : Args (signatureOf language) arity bound) (sources : List Pattern),
    checkConstructorArguments scopes arguments sources = true →
      ArgumentsHaveTypes language FreeTypeContext.empty bound sources parameters
  | _,_,_,.nil,.nil,sources,accepted => by
      cases sources with
      | nil => exact .nil
      | cons => cases accepted
  | _,_,_,.cons scope scopes,.cons head tail,sources,accepted => by
      cases sources with
      | nil => cases accepted
      | cons source sources =>
          simp only [checkConstructorArguments] at accepted
          cases readback : readBody? scope source with
          | none => simp only [readback,Bool.false_eq_true] at accepted
          | some body =>
              rw [readback] at accepted
              obtain ⟨first,rest⟩ := Bool.and_eq_true_iff.mp accepted
              obtain ⟨expected,representation,typeSame,bodyTyped⟩ := scope.wrap_typed (typed head body first)
              have sourceSame := readBody_eq_wrap scope readback
              rw [← sourceSame] at representation bodyTyped
              exact .cons representation typeSame bodyTyped (constructorArgumentsTyped scopes tail sources rest)
end


mutual
/-- Every original closed typing derivation has a checked intrinsic receipt.
No canonical-display, object-only or closed-tail restriction is imposed. -/
theorem typed_exists {bound : List TypeExpr} {source : Pattern} {sort : TypeExpr}
    (typed : HasType language FreeTypeContext.empty bound source sort) :
    ∃ term : Term (signatureOf language) bound sort, check term source = true := by
  cases typed with
  | bvar lookup =>
      obtain ⟨position,same⟩ := variableIndex_exists_of_lookup _ _ _ lookup
      exact ⟨.var position,by simp only [check,same,beq_self_eq_true]⟩
  | fvar lookup => cases lookup
  | constructor member ordinary arguments =>
      obtain ⟨arity,scopes,values,readback⟩ := arguments_exists arguments
      exact ⟨.op (.constructor _ member ordinary scopes) values,by
        simpa only [check,beq_self_eq_true,Bool.true_and] using readback⟩
  | @lambda bound display body domain codomain bodyTyped =>
      obtain ⟨value,readback⟩ := typed_exists bodyTyped
      exact ⟨.op (.lambda domain codomain) (.cons value .nil),readback⟩
  | @multiLambda bound count displays body domain codomain bodyTyped =>
      obtain ⟨value,readback⟩ := typed_exists bodyTyped
      exact ⟨.op (.multiLambda domain codomain count) (.cons value .nil),by
        simpa only [check,beq_self_eq_true,Bool.true_and] using readback⟩
  | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
      obtain ⟨value,bodyReadback⟩ := typed_exists bodyTyped
      obtain ⟨argument,replacementReadback⟩ := typed_exists replacementTyped
      exact ⟨.op (.subst domain sort) (.cons value (.cons argument .nil)),by
        simp only [check,bodyReadback,replacementReadback,Bool.and_self]⟩
  | @collection bound kind elements rest elementType elementsTyped =>
      obtain ⟨values,readback⟩ := elements_exists elementsTyped
      exact ⟨.op (.collection kind elementType elements.length) values,by
        simpa only [check,beq_self_eq_true,Bool.true_and] using readback⟩
  | @collectionConstructor bound declaration paramName kind elements rest elementType member shape elementsTyped =>
      obtain ⟨values,readback⟩ := elements_exists elementsTyped
      exact ⟨.op (.collectionConstructor declaration member paramName kind elementType shape elements.length) values,by
        simpa only [check,beq_self_eq_true,Bool.true_and] using readback⟩
termination_by sizeOf source

/-- Every declared argument spine supplies its actual binding scopes and
intrinsic argument terms, in the original parameter order. -/
theorem arguments_exists {bound : List TypeExpr} {sources : List Pattern}
    {parameters : List TermParam}
    (typed : ArgumentsHaveTypes language FreeTypeContext.empty bound sources parameters) :
    ∃ (arity : List (List TypeExpr × TypeExpr)) (scopes : ParameterScopes parameters arity)
      (arguments : Args (signatureOf language) arity bound),
      checkConstructorArguments scopes arguments sources = true := by
  cases typed with
  | nil => exact ⟨[],.nil,.nil,rfl⟩
  | @cons bound source sources parameter parameters expected representation expectedType headTyped tailTyped =>
      obtain ⟨arity,scopes,rest,restRead⟩ := arguments_exists tailTyped
      cases parameter with
      | simple paramName type =>
          cases Option.some.inj expectedType
          obtain ⟨value,readback⟩ := typed_exists headTyped
          exact ⟨([],expected)::arity,.cons (.simple paramName expected) scopes,.cons value rest,by
            simp only [checkConstructorArguments,readBody?,readback,restRead,Bool.and_self]⟩
      | abstractionNamed binder paramName type =>
          obtain ⟨body,rfl⟩ :=
            (matchesParameterRepresentation_abstractionNamed_iff binder paramName type source).mp representation
          cases type with
          | base category =>
              cases Option.some.inj expectedType
              cases headTyped with
              | lambda bodyTyped =>
                  obtain ⟨value,readback⟩ := typed_exists bodyTyped
                  exact ⟨([.base category],.base category)::arity,
                    .cons (.abstractionBase binder paramName category) scopes,.cons value rest,by
                      simp only [checkConstructorArguments,readBody?,readback,restRead,Bool.and_self]⟩
          | arrow domain codomain =>
              cases Option.some.inj expectedType
              cases headTyped with
              | lambda bodyTyped =>
                  obtain ⟨value,readback⟩ := typed_exists bodyTyped
                  exact ⟨([domain],codomain)::arity,
                    .cons (.abstraction binder paramName domain codomain) scopes,.cons value rest,by
                      simp only [checkConstructorArguments,readBody?,readback,restRead,Bool.and_self]⟩
          | multiBinder domain => cases expectedType
          | collection kind type => cases expectedType
      | multiAbstractionNamed displays paramName type =>
          obtain ⟨count,body,rfl⟩ :=
            (matchesParameterRepresentation_multiAbstractionNamed_iff displays paramName type source).mp representation
          cases type with
          | base category =>
              cases Option.some.inj expectedType
              cases headTyped with
              | multiLambda bodyTyped =>
                  obtain ⟨value,readback⟩ := typed_exists bodyTyped
                  exact ⟨(List.replicate count (.base category),.base category)::arity,
                    .cons (.multiAbstractionBase displays paramName category count) scopes,.cons value rest,by
                      simp only [checkConstructorArguments,readBody?,beq_self_eq_true,ite_true,
                        readback,restRead,Bool.and_self]⟩
          | arrow domain codomain =>
              cases domain with
              | multiBinder domain =>
                  cases Option.some.inj expectedType
                  cases headTyped with
                  | multiLambda bodyTyped =>
                      obtain ⟨value,readback⟩ := typed_exists bodyTyped
                      exact ⟨(List.replicate count domain,codomain)::arity,
                        .cons (.multiAbstraction displays paramName domain codomain count) scopes,.cons value rest,by
                          simp only [checkConstructorArguments,readBody?,beq_self_eq_true,ite_true,
                            readback,restRead,Bool.and_self]⟩
              | base _ => cases expectedType
              | arrow _ _ => cases expectedType
              | collection _ _ => cases expectedType
          | multiBinder domain => cases expectedType
          | collection kind type => cases expectedType
termination_by sizeOf sources

theorem elements_exists {bound : List TypeExpr} {sources : List Pattern} {sort : TypeExpr}
    (typed : ElementsHaveType language FreeTypeContext.empty bound sources sort) :
    ∃ arguments : Args (signatureOf language) (List.replicate sources.length ([],sort)) bound,
      checkArguments arguments sources = true := by
  cases typed with
  | nil => exact ⟨.nil,rfl⟩
  | cons headTyped tailTyped =>
      obtain ⟨value,headRead⟩ := typed_exists headTyped
      obtain ⟨rest,tailRead⟩ := elements_exists tailTyped
      exact ⟨.cons value rest,by simp only [checkArguments,headRead,tailRead,Bool.and_self]⟩
termination_by sizeOf sources
end

/-- The checked receipt covers exactly the original complete closed typing
judgment, rather than an object-pattern or canonical-presentation fragment. -/
theorem typed_iff_receipt {bound : List TypeExpr} {source : Pattern} {sort : TypeExpr} :
    HasType language FreeTypeContext.empty bound source sort ↔
      ∃ term : Term (signatureOf language) bound sort,check term source = true :=
  ⟨typed_exists,fun ⟨term,accepted⟩ => typed term source accepted⟩



/-- Transporting the ambient context index does not change source readback. -/
theorem check_transport {first second : List TypeExpr} {sort : TypeExpr}
    (same : first = second) (term : Term (signatureOf language) first sort) (source : Pattern) :
    check (same ▸ term) source = check term source := by
  cases same
  rfl

/-- The actual slot wrapper is accepted without changing the scope. -/
theorem readBody_wrap {parameter : TermParam} {binders : List TypeExpr} {sort : TypeExpr}
    (scope : ParameterScope parameter binders sort) (body : Pattern) :
    readBody? scope (scope.wrap body) = some body := by
  cases scope <;> simp only [ParameterScope.wrap,readBody?,beq_self_eq_true,ite_true]

mutual
/-- Original intrinsic terms provide executable receipts for their own raw
erasure; no source-typing proof is searched or chosen at runtime. -/
theorem check_erase : ∀ {bound : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf language) bound sort),check term (erase term) = true
  | _,_,.var _ => by simp only [check,erase,beq_self_eq_true]
  | _,_,.op (.constructor _ _ _ scopes) arguments => by
      simp only [check,erase,beq_self_eq_true,Bool.true_and]
      exact checkConstructorArguments_erase scopes arguments
  | _,_,.op (.collectionConstructor _ _ _ _ _ _ _) arguments => by
      simp only [check,erase,beq_self_eq_true,Bool.true_and]
      exact checkArguments_erase arguments
  | _,_,.op (.lambda _ _) arguments =>
      match arguments with
      | .cons body .nil => check_erase body
  | _,_,.op (.multiLambda _ _ _) arguments =>
      match arguments with
      | .cons body .nil => by
          simp only [check,erase,beq_self_eq_true,Bool.true_and]
          exact check_erase body
  | _,_,.op (.subst _ _) arguments =>
      match arguments with
      | .cons body (.cons replacement .nil) => by
          simp only [check,erase,check_erase body,check_erase replacement,Bool.and_self]
  | _,_,.op (.collection _ _ _) arguments => by
      simp only [check,erase,beq_self_eq_true,Bool.true_and]
      exact checkArguments_erase arguments

theorem checkArguments_erase : ∀ {arity : List (List TypeExpr × TypeExpr)} {bound : List TypeExpr}
    (arguments : Args (signatureOf language) arity bound),
    checkArguments arguments (eraseArguments arguments) = true
  | _,_,.nil => rfl
  | _,_,.cons head tail => by
      simp only [checkArguments,eraseArguments,check_erase head,checkArguments_erase tail,Bool.and_self]

theorem checkConstructorArguments_erase : ∀ {parameters : List TermParam}
    {arity : List (List TypeExpr × TypeExpr)} {bound : List TypeExpr}
    (scopes : ParameterScopes parameters arity) (arguments : Args (signatureOf language) arity bound),
    checkConstructorArguments scopes arguments (eraseConstructorArguments scopes arguments) = true
  | _,_,_,.nil,.nil => rfl
  | _,_,_,.cons scope scopes,.cons head tail => by
      simp only [checkConstructorArguments,eraseConstructorArguments,readBody_wrap,
        check_erase head,checkConstructorArguments_erase scopes tail,Bool.and_self]
end

#print axioms readBody_eq_wrap
#print axioms typed
#print axioms argumentsTyped
#print axioms constructorArgumentsTyped
#print axioms typed_exists
#print axioms arguments_exists
#print axioms elements_exists
#print axioms typed_iff_receipt
#print axioms check_transport
#print axioms readBody_wrap
#print axioms check_erase
#print axioms checkArguments_erase
#print axioms checkConstructorArguments_erase
end Mettapedia.GSLT.LanguageDef.BindingSyntax.SourceReadback
