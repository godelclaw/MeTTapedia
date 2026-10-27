import Mettapedia.GSLT.LanguageDef.ModuleSource.Printer

/-!
# Languages as `.module` files

A language becomes a module with one theory: its sorts, constructors, equations and rewrites (`moduleOf`), printed
in the `.module` format (`moduleText`), which the format's reader reads back.

A rule in core form writes an abstraction's body as a metavariable under an anonymous binder, `Lam (λ. body)`, and
instantiates it by substitution. The `.module` format names the abstraction itself, `(Lam body)` with
`(eval body argument)`, as upstream's β does; a named binder there would put the metavariable in the binder's scope
and out of scope everywhere else. So a metavariable used only under anonymous binders and as the body of a
substitution is written as the abstraction (`authoredRule`).
-/

namespace Mettapedia.OSLF.NativeTypes.Product

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ModuleSource

/-- Whether the metavariable occurs other than as `λ. name` or as the body of a substitution. -/
partial def bareUse (name : String) : Pattern → Bool
  | .fvar other => other == name
  | .bvar _ => false
  | .apply _ arguments => arguments.any (bareUse name)
  | .lambda none (.fvar _) => false
  | .lambda _ body => bareUse name body
  | .multiLambda _ _ body => bareUse name body
  | .subst (.fvar _) argument => bareUse name argument
  | .subst body argument => bareUse name body || bareUse name argument
  | .collection _ elements _ => elements.any (bareUse name)

/-- The metavariables written as `λ. name`. -/
partial def abstracted : Pattern → List String
  | .lambda none (.fvar name) => [name]
  | .lambda _ body => abstracted body
  | .multiLambda _ _ body => abstracted body
  | .apply _ arguments => arguments.flatMap abstracted
  | .subst body argument => abstracted body ++ abstracted argument
  | .collection _ elements _ => elements.flatMap abstracted
  | _ => []

/-- `λ. name` written as `name`, for the given metavariables. -/
partial def contract (names : List String) : Pattern → Pattern
  | .lambda none (.fvar name) => if names.contains name then .fvar name else .lambda none (.fvar name)
  | .lambda binder body => .lambda binder (contract names body)
  | .multiLambda count binders body => .multiLambda count binders (contract names body)
  | .apply head arguments => .apply head (arguments.map (contract names))
  | .subst body argument => .subst (contract names body) (contract names argument)
  | .collection kind elements rest => .collection kind (elements.map (contract names)) rest
  | pattern => pattern

/-- Whether a premise mentions the metavariable at all. -/
def premiseMentions (name : String) : Premise → Bool
  | .congruence left right => bareUse name left || bareUse name right || (abstracted left ++ abstracted right).contains name
  | .freshness condition => condition.varName == name || bareUse name condition.term
  | _ => true

/-- **A rule as authored**: a metavariable used only under anonymous binders and as the body of a substitution, and
in no premise, is written as the abstraction. -/
def authoredRule (rule : RewriteRule) : RewriteRule :=
  let names := ((abstracted rule.left ++ abstracted rule.right).eraseDups).filter fun name =>
    !bareUse name rule.left && !bareUse name rule.right && !rule.premises.any (premiseMentions name)
  { rule with left := contract names rule.left, right := contract names rule.right }

/-- The theory of a language: its sorts, constructors, equations and rewrites. -/
def theoryOf (language : LanguageDef) : Theory where
  «name» := language.«name»
  params := []
  body := .extend none [.types language.«types», .terms language.«terms»,
    .equations language.equations, .rewrites (language.rewrites.map authoredRule)]

/-- **A language as a module** with one theory, which the module elaborates to. -/
def moduleOf (language : LanguageDef) : Module where
  imports := []
  «name» := language.«name»
  theories := [theoryOf language]
  entry := some ([language.«name»], [])

/-- A language as `.module` text. -/
def moduleText (language : LanguageDef) : String := Printer.print (moduleOf language)

end Mettapedia.OSLF.NativeTypes.Product
