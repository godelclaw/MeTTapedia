import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

/-!
# The core of an authored language

A `CoreLanguageDef` is a language in its canonical, minimal form: binding by de Bruijn index
only, a collection constructor's terms written as the bare collection, and every rule and
equation carrying an admitted binding declaration. Compilation, execution and their proofs
are stated on it.

A `LanguageDef` is written the way people read rules, in our `languageDef!` notation and in
upstream MeTTaIL's `language!` notation:

- a constructor whose only parameter is a collection is applied to it, `(PPar {S, ...rest})`;
- binders carry names, `^x.P`, and bodies may mention them;
- `x # M` for a binder `x` says that `M` does not use `x`;
- a premise `S ~> T` whose `S` sits under binders is a step under those binders;
- a metavariable may stand for a whole abstraction, `(Lam fn)`, and `(eval fn a)` applies it.

`LanguageDef.toCore` reduces it exactly to its core: bare collections, eta-long abstractions
(`(Lam fn)` is `(Lam ^x.fn)` with `fn` depending on `x`, and `(eval fn a)` is
`(eval ^x.fn a)`), erased binder names, bound-name references as indices, binding declarations
whose dependencies and occurrence arguments are computed from the names, and scoped premises. Freshness of a bound name
becomes a dependency exclusion; freshness of a free name stays a premise. The result is
checked by the core predicate; anything else is reported, never guessed.

Binder names decide occurrence arguments: swapping two binders around a body, as in
`(PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P))`, gives the body the swapped arguments, not
the identity.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CoreReduction

open Syntax RuleBinding

/-! ## Patterns -/

/-- Constructors whose only parameter is a collection. -/
def bareLabels (language : LanguageDef) : List (String × CollType) :=
  language.terms.filterMap fun rule =>
    match rule.params with
    | [.simple _ (.collection kind _)] => some (rule.label, kind)
    | _ => none

/-- Bare collections for bare-collection constructors, everywhere in a pattern. A collection
written as the constructor's argument takes the collection kind the constructor declares: a
literal `{…}` is read at the kind of the parameter it fills. -/
def unwrap (bare : List (String × CollType)) : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply label arguments =>
      let inner := arguments.map (unwrap bare)
      match bare.lookup label with
      | some declared =>
        match inner with
        | [.collection _ elements rest] => .collection declared elements rest
        | _ => .apply label inner
      | none => .apply label inner
  | .lambda binder body => .lambda binder (unwrap bare body)
  | .multiLambda arity binders body => .multiLambda arity binders (unwrap bare body)
  | .subst body replacement => .subst (unwrap bare body) (unwrap bare replacement)
  | .collection kind elements rest => .collection kind (elements.map (unwrap bare)) rest
decreasing_by all_goals sizeOf_pattern_dec

/-- The binder names a binder node opens, innermost first. -/
def opened : Pattern → List (Option String)
  | .lambda binder _ => [binder]
  | .multiLambda arity binders _ =>
      if binders.length = arity then (binders.map some).reverse else List.replicate arity none
  | .subst _ _ => [none]
  | _ => []

/-- References to enclosing binder names become indices; names are erased. Applying an explicit
abstraction, `(eval ^x.b a)`, is the substitution node: `b` with `a` for `x`. -/
def resolve (names : List (Option String)) : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name =>
      match names.findIdx? (· == some name) with
      | some index => .bvar index
      | none => .fvar name
  | .apply label [.lambda binder body, replacement] =>
      if label == Pattern.evalHead then .subst (resolve (binder :: names) body) (resolve names replacement)
      else .apply label [.lambda none (resolve (binder :: names) body), resolve names replacement]
  | .apply label arguments => .apply label (arguments.map (resolve names))
  | .lambda binder body => .lambda none (resolve (binder :: names) body)
  | .multiLambda arity binders body =>
      let inner := if binders.length = arity then (binders.map some).reverse else List.replicate arity none
      .multiLambda arity [] (resolve (inner ++ names) body)
  | .subst body replacement => .subst (resolve (none :: names) body) (resolve names replacement)
  | .collection kind elements rest => .collection kind (elements.map (resolve names)) rest
decreasing_by all_goals sizeOf_pattern_dec

/-- A metavariable occurrence with the binder names around it, innermost first. -/
structure Site where
  name : String
  site : RulePatternSite
  path : List Nat
  names : List (Option String)
  deriving Repr, DecidableEq

mutual
  /-- Every metavariable occurrence, in path order. Bound-name references are not
  metavariables. -/
  def sites (site : RulePatternSite) (names : List (Option String)) (path : List Nat) :
      Pattern → List Site
    | .bvar _ => []
    | .fvar name => if names.contains (some name) then [] else [⟨name, site, path, names⟩]
    | .apply label [.lambda binder body, replacement] =>
        if label == Pattern.evalHead then
          sites site (binder :: names) (path ++ [0]) body ++ sites site names (path ++ [1]) replacement
        else
          sites site (binder :: names) (path ++ [0, 0]) body ++ sites site names (path ++ [1]) replacement
    | .apply _ arguments => siteList site names path 0 arguments
    | .lambda binder body => sites site (binder :: names) (path ++ [0]) body
    | .multiLambda arity binders body =>
        let inner := if binders.length = arity then (binders.map some).reverse else List.replicate arity none
        sites site (inner ++ names) (path ++ [0]) body
    | .subst body replacement =>
        sites site (none :: names) (path ++ [0]) body ++ sites site names (path ++ [1]) replacement
    | .collection _ elements rest =>
        siteList site names path 0 elements ++
          rest.toList.map fun name => ⟨name, site, path ++ [elements.length], names⟩
  termination_by pattern => sizeOf pattern

  def siteList (site : RulePatternSite) (names : List (Option String)) (path : List Nat) (index : Nat) :
      List Pattern → List Site
    | [] => []
    | pattern :: patterns => sites site names (path ++ [index]) pattern ++
        siteList site names path (index + 1) patterns
  termination_by patterns => sizeOf patterns
end

/-- Every binder name a pattern opens. -/
def binderNames : Pattern → List String
  | .bvar _ | .fvar _ => []
  | .apply _ arguments => arguments.flatMap binderNames
  | .lambda binder body => binder.toList ++ binderNames body
  | .multiLambda _ binders body => binders ++ binderNames body
  | .subst body replacement => binderNames body ++ binderNames replacement
  | .collection _ elements _ => elements.flatMap binderNames
decreasing_by all_goals sizeOf_pattern_dec

/-! ## Eta-long abstractions -/

/-- A constructor's parameters. -/
def paramsOf (language : LanguageDef) (label : String) : List TermParam :=
  ((language.terms.find? (·.label == label)).map (·.params)).getD []

mutual
  /-- The metavariables written directly in a one-binder abstraction slot. -/
  def slotNames (language : LanguageDef) : Pattern → List String
    | .bvar _ | .fvar _ => []
    | .apply label arguments => slotArguments language (paramsOf language label) arguments
    | .lambda _ body => slotNames language body
    | .multiLambda _ _ body => slotNames language body
    | .subst body replacement => slotNames language body ++ slotNames language replacement
    | .collection _ elements _ => slotList language elements
  termination_by pattern => (sizeOf pattern, 0)

  def slotArguments (language : LanguageDef) : List TermParam → List Pattern → List String
    | .abstractionNamed _ _ _ :: params, .fvar name :: rest => name :: slotArguments language params rest
    | _ :: params, pattern :: rest => slotNames language pattern ++ slotArguments language params rest
    | [], patterns => slotList language patterns
    | _, [] => []
  termination_by _ patterns => (sizeOf patterns, 1)

  def slotList (language : LanguageDef) : List Pattern → List String
    | [] => []
    | pattern :: patterns => slotNames language pattern ++ slotList language patterns
  termination_by patterns => (sizeOf patterns, 0)
end

mutual
  /-- A metavariable in a one-binder abstraction slot becomes `^x.m`, and `(eval m a)` for such
  an `m` becomes `(eval ^x.m a)`: `m` then depends on the binder. -/
  def etaLong (language : LanguageDef) (expanded : List String) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply label arguments =>
        if label == Pattern.evalHead then .apply label (etaScope language expanded arguments)
        else .apply label (etaArguments language expanded (paramsOf language label) arguments)
    | .lambda binder body => .lambda binder (etaLong language expanded body)
    | .multiLambda arity binders body => .multiLambda arity binders (etaLong language expanded body)
    | .subst body replacement => .subst (etaLong language expanded body) (etaLong language expanded replacement)
    | .collection kind elements rest => .collection kind (etaList language expanded elements) rest
  termination_by pattern => (sizeOf pattern, 0)

  def etaArguments (language : LanguageDef) (expanded : List String) :
      List TermParam → List Pattern → List Pattern
    | .abstractionNamed _ _ _ :: params, .fvar name :: rest =>
        .lambda none (.fvar name) :: etaArguments language expanded params rest
    | _ :: params, pattern :: rest =>
        etaLong language expanded pattern :: etaArguments language expanded params rest
    | [], patterns => etaList language expanded patterns
    | _, [] => []
  termination_by _ patterns => (sizeOf patterns, 1)

  def etaScope (language : LanguageDef) (expanded : List String) : List Pattern → List Pattern
    | .fvar name :: rest =>
        (if expanded.contains name then .lambda none (.fvar name) else .fvar name) ::
          etaList language expanded rest
    | patterns => etaList language expanded patterns
  termination_by patterns => (sizeOf patterns, 1)

  def etaList (language : LanguageDef) (expanded : List String) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => etaLong language expanded pattern :: etaList language expanded patterns
  termination_by patterns => (sizeOf patterns, 0)
end

/-! ## Rules -/

/-- An authored rule: name, left, right, premises and any authored type context. -/
structure AuthoredRule where
  name : String
  typeContext : List (String × TypeExpr)
  premises : List Premise
  left : Pattern
  right : Pattern
  deriving Repr

/-- Why an authored rule has no core. -/
inductive Failure where
  | untyped (rule metavariable : String)
  | outOfScope (rule metavariable binder : String)
  | unsupportedPremise (rule : String) (index : Nat)
  | notAdmitted (rule : String)
  | notCore (language : String)
  deriving Repr, DecidableEq

/-- A freshness premise on a binder name of the rule is absorbed into dependencies. -/
def boundFreshness (bound : List String) : Premise → Bool
  | .freshness condition => bound.contains condition.varName
  | _ => false

/-- The binder names excluded from a metavariable's dependencies by absorbed
freshness premises. -/
def excluded (bound : List String) (premises : List Premise) (metavariable : String) : List String :=
  premises.filterMap fun premise =>
    match premise with
    | .freshness condition =>
        if bound.contains condition.varName && condition.term.freeFvarNames.contains metavariable then
          some condition.varName
        else none
    | _ => none

/-- Grammar types at one site: the binder sorts around it and its result sort. -/
def typesAt (language : LanguageDef) (context : List (String × TypeExpr)) (pattern : Pattern)
    (path : List Nat) : Option (List TypeExpr × TypeExpr) := do
  let expected ← GeneralRuleBindingGrammar.headType? language context [] pattern
  GeneralRuleBindingGrammar.contextAt? language context [] expected pattern path

/-- A metavariable's binding: the names and sorts it may use, and its result sort. -/
structure Binding where
  name : String
  names : List (Option String)
  sorts : List TypeExpr
  result : TypeExpr
  deriving Repr, DecidableEq

/-- Occurrence arguments: each dependency by its name, or by position when unnamed. -/
def arguments (binding : Binding) (names : List (Option String)) : Option (List Pattern) :=
  (binding.names.zipIdx).mapM fun (name, position) =>
    match name with
    | some binder => (names.findIdx? (· == some binder)).map Pattern.bvar
    | none => if names[position]? = some none then some (.bvar position) else none

/-- Unwrap the patterns of a premise. -/
def unwrapPremise (bare : List (String × CollType)) : Premise → Premise
  | .freshness condition => .freshness ⟨condition.varName, unwrap bare condition.term⟩
  | .congruence source target => .congruence (unwrap bare source) (unwrap bare target)
  | .scopedStep step => .scopedStep {step with source := unwrap bare step.source, target := unwrap bare step.target}
  | .relationQuery relation arguments => .relationQuery relation (arguments.map (unwrap bare))
  | .forAll collection element body => .forAll collection element body

/-- The core parts of one rule. -/
structure Core where
  typeContext : List (String × TypeExpr)
  premises : List Premise
  left : Pattern
  right : Pattern
  bindings : RuleBindingSpec

/-- The binding of a metavariable from its first site, with absorbed exclusions. -/
def bindingAt (language : LanguageDef) (context : List (String × TypeExpr)) (bound : List String)
    (premises : List Premise) (pattern : Pattern) (site : Site) : Option Binding := do
  let (sorts, result) ← typesAt language context pattern site.path
  guard (sorts.length = site.names.length)
  let drop := excluded bound premises site.name
  let kept := (site.names.zip sorts).filter fun (name, _) =>
    match name with
    | some binder => !drop.contains binder
    | none => true
  return ⟨site.name, kept.map Prod.fst, kept.map Prod.snd, result⟩

/-- Reduce one authored rule to its core parts. -/
def reduceRule (language : LanguageDef) (rule : AuthoredRule) : Except Failure Core := do
  let bare := bareLabels language
  let expanded := slotNames language rule.left
  let left := unwrap bare (etaLong language expanded rule.left)
  let right := unwrap bare (etaLong language expanded rule.right)
  let authoredPremises := rule.premises.map (unwrapPremise bare)
  let premisePatterns := authoredPremises.flatMap fun premise =>
    match premise with
    | .freshness condition => [condition.term]
    | .congruence source target => [source, target]
    | .scopedStep step => [step.source, step.target]
    | .relationQuery _ arguments => arguments
    | .forAll _ _ _ => []
  let bound := binderNames left ++ binderNames right ++ premisePatterns.flatMap binderNames
  let kept := authoredPremises.filter fun premise => !boundFreshness bound premise
  let leftSites := sites .left [] [] left
  let rightSites := sites .right [] [] right
  -- metavariables bound by the left side
  let leftNames := (leftSites.map (·.name)).eraseDups
  let leftBindings ← leftNames.mapM fun name => do
    let some site := leftSites.find? (·.name == name) | throw (.untyped rule.name name)
    match bindingAt language rule.typeContext bound authoredPremises (resolve [] left) site with
    | some binding => pure binding
    | none => throw (.untyped rule.name name)
  let lookup (name : String) : Option Binding := leftBindings.find? (·.name == name)
  -- premises: scoped steps under the binders of their source; their sites
  let premiseRows ← kept.zipIdx.mapM fun (premise, index) => do
    match premise with
    | .congruence (.fvar source) (.fvar target) =>
        match lookup source with
        | some binding =>
            if binding.sorts.isEmpty then
              pure (premise, [⟨source, .premise index 0 0, [], []⟩, ⟨target, .premise index 0 1, [], []⟩],
                [(target, {binding with name := target})])
            else
              pure (.scopedStep ⟨binding.sorts, binding.result, .fvar source, .fvar target⟩,
                [⟨source, .premise index 0 0, [], binding.names⟩, ⟨target, .premise index 0 1, [], binding.names⟩],
                [(target, {binding with name := target})])
        | none => throw (.unsupportedPremise rule.name index)
    | .freshness condition =>
        pure (.freshness ⟨condition.varName, resolve [] condition.term⟩,
          sites (.premise index 0 0) [] [] condition.term, [])
    | _ => throw (.unsupportedPremise rule.name index)
  let premises := premiseRows.map (·.1)
  let premiseSites := premiseRows.flatMap (·.2.1)
  let produced := premiseRows.flatMap (·.2.2)
  let bindingOf (name : String) : Option Binding :=
    (lookup name).orElse fun _ => (produced.find? (·.1 == name)).map (·.2)
  -- every metavariable must be bound by the left side or a premise
  let allSites := leftSites ++ premiseSites ++ rightSites
  let names := (allSites.map (·.name)).eraseDups
  let bindings ← names.mapM fun name =>
    match bindingOf name with
    | some binding => pure binding
    | none => throw (.untyped rule.name name)
  let occurrences ← allSites.mapM fun site => do
    let some binding := bindings.find? (·.name == site.name) | throw (.untyped rule.name site.name)
    match arguments binding site.names with
    | some values => pure (⟨site.name, site.site, site.path, values⟩ : MetavariableOccurrence)
    | none =>
        let missing := (binding.names.filterMap id).find? fun binder => !site.names.contains (some binder)
        throw (.outOfScope rule.name site.name (missing.getD "?"))
  let extra := (bindings.filter fun binding => !(rule.typeContext.any (·.1 == binding.name))).map
    fun binding => (binding.name, binding.result)
  let typeContext := rule.typeContext ++ extra
  let dependencies := typeContext.map fun (name, _) =>
    (name, ((bindings.find? (·.name == name)).map (·.sorts)).getD [])
  return ⟨typeContext, premises, resolve [] left, resolve [] right, ⟨dependencies, occurrences⟩⟩

/-- The core rewrite rule, checked by the core admission predicate. -/
def reduceRewrite (language : LanguageDef) (rule : RewriteRule) : Except Failure RewriteRule := do
  match rule.bindings with
  | some _ => pure rule
  | none =>
    let core ← reduceRule language ⟨rule.name, rule.typeContext, rule.premises, rule.left, rule.right⟩
    let result : RewriteRule := ⟨rule.name, core.typeContext, core.premises, core.left, core.right, some core.bindings⟩
    if admittedFor result core.bindings && dependencySortsDeclared language core.bindings then pure result
    else throw (.notAdmitted rule.name)

/-- The core equation, checked as its forward rule. -/
def reduceEquation (language : LanguageDef) (equation : Equation) : Except Failure Equation := do
  match equation.bindings with
  | some _ => pure equation
  | none =>
    let core ← reduceRule language
      ⟨equation.name, equation.typeContext, equation.premises, equation.left, equation.right⟩
    let result : Equation := ⟨equation.name, core.typeContext, core.premises, core.left, core.right, some core.bindings⟩
    let forward : RewriteRule := ⟨result.name, result.typeContext, result.premises, result.left, result.right,
      result.bindings⟩
    if admittedFor forward core.bindings && dependencySortsDeclared language core.bindings then pure result
    else throw (.notAdmitted equation.name)

/-- Rules and equations reduced, or the first rule without a core. Rules and equations that
already carry a binding declaration are kept as authored. -/
def reduce (language : LanguageDef) : Except Failure LanguageDef := do
  let rewrites ← language.rewrites.mapM (reduceRewrite language)
  let equations ← language.equations.mapM (reduceEquation language)
  return { language with «rewrites» := rewrites, «equations» := equations }

/-! ## The core predicate -/

/-- A core pattern: erased binder names and bare collections. -/
def corePattern (bare : List (String × CollType)) (pattern : Pattern) : Bool :=
  pattern.hasCanonicalBinderMetadata && unwrap bare pattern == pattern

/-- A core rule: its patterns are core and its binding declaration is admitted. -/
def coreRule (language : LanguageDef) (rule : RewriteRule) : Bool :=
  match rule.bindings with
  | some spec =>
      corePattern (bareLabels language) rule.left && corePattern (bareLabels language) rule.right &&
        admittedFor rule spec && dependencySortsDeclared language spec
  | none => false

/-- A core equation: its forward rule is core. -/
def coreEquation (language : LanguageDef) (equation : Equation) : Bool :=
  coreRule language ⟨equation.name, equation.typeContext, equation.premises, equation.left, equation.right,
    equation.bindings⟩

/-- The core predicate on a language. -/
def isCore (language : LanguageDef) : Bool :=
  language.validate.isEmpty && language.rewrites.all (coreRule language) &&
    language.equations.all (coreEquation language)

end Mettapedia.OSLF.MeTTaIL.CoreReduction

namespace Mettapedia.OSLF.MeTTaIL

open Syntax

/-- **A language in its core form.** -/
structure CoreLanguageDef where
  language : Syntax.LanguageDef
  core : CoreReduction.isCore language = true

/-- **The reduction of an authored language to its core**, or why it has none. -/
def Syntax.LanguageDef.toCore (language : Syntax.LanguageDef) : Except CoreReduction.Failure CoreLanguageDef := do
  let reduced ← CoreReduction.reduce language
  if checked : CoreReduction.isCore reduced = true then
    return ⟨reduced, checked⟩
  else
    throw (.notCore language.name)

end Mettapedia.OSLF.MeTTaIL
