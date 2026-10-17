import Mettapedia.GSLT.LanguageDef.ClosedTermChecker
import Mettapedia.GSLT.LanguageDef.BindingSignature

/-!
# Resolved module binder slots elaborate into the existing core

A source declaration has a spelling slot `Bind x S` and a body slot `(x)T`.
The spelling is notation metadata. The semantic argument is one abstraction
of type `S -> T`, not two independent arguments of types `S` and `T`.

This file treats resolved category expressions and source slot names. A unique
name lookup is one partial resolution method, not a completeness claim for
all scope interpretations. Successful resolution preserves and reflects the
body's declaration-derived typing, including the surrounding bound context.
No parser, native implementation or name-to-index projection adequacy follows
from these resolved-boundary theorems.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.BindingDeclarationElaboration

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BindingSyntax

/-- Ordered source spelling slots; repeated names are retained. -/
abbrev BinderSlots := List (String × TypeExpr)

def candidates (slots : BinderSlots) (name : String) : List TypeExpr :=
  slots.filterMap fun slot => if slot.1 = name then some slot.2 else none

/-- Unknown or ambiguous names leave this resolution method undecided. -/
def resolveDomain? (slots : BinderSlots) (name : String) : Option TypeExpr :=
  match candidates slots name with
  | [domain] => some domain
  | _ => none

def elaborateParameter? (slots : BinderSlots) (binder bodyName : String)
    (bodyType : TypeExpr) : Option TermParam :=
  (resolveDomain? slots binder).map fun domain =>
    .abstractionNamed (some binder) bodyName (.arrow domain bodyType)

theorem elaborateParameter_iff (slots : BinderSlots) (binder bodyName : String)
    (bodyType : TypeExpr) (parameter : TermParam) :
    elaborateParameter? slots binder bodyName bodyType = some parameter ↔
      ∃ domain, resolveDomain? slots binder = some domain ∧
        parameter = .abstractionNamed (some binder) bodyName (.arrow domain bodyType) := by
  cases resolved : resolveDomain? slots binder <;>
    simp [elaborateParameter?, resolved, eq_comm]

/-- Every successful slot elaboration has the core's existing binding arity.
No source spelling is made an additional semantic constructor argument. -/
theorem elaboration_scope {slots : BinderSlots} {binder bodyName : String}
    {bodyType : TypeExpr} {parameter : TermParam}
    (elaborated : elaborateParameter? slots binder bodyName bodyType = some parameter) :
    ∃ domain, resolveDomain? slots binder = some domain ∧
      Nonempty (ParameterScope parameter [domain] bodyType) := by
  obtain ⟨domain, resolved, rfl⟩ := (elaborateParameter_iff _ _ _ _ _).mp elaborated
  exact ⟨domain, resolved, ⟨.abstraction (some binder) bodyName domain bodyType⟩⟩

/-- The actual argument-spine judgment agrees in both directions with typing
the body in the extended context. The tail may have arbitrary other fields. -/
theorem elaboration_typing_iff
    {slots : BinderSlots} {binder bodyName : String} {domain bodyType : TypeExpr}
    {parameter : TermParam}
    (resolved : resolveDomain? slots binder = some domain)
    (elaborated : elaborateParameter? slots binder bodyName bodyType = some parameter)
    (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    (body : Pattern) (arguments : List Pattern) (parameters : List TermParam) :
    ArgumentsHaveTypes language free bound (.lambda none body :: arguments)
        (parameter :: parameters) ↔
      HasType language free (domain :: bound) body bodyType ∧
        ArgumentsHaveTypes language free bound arguments parameters := by
  simp only [elaborateParameter?, resolved, Option.map_some, Option.some.injEq] at elaborated
  subst parameter
  constructor
  · intro typed
    cases typed with
    | cons representation induced typed tail =>
        simp only [parameterType?, Option.some.injEq] at induced
        subst induced
        cases typed with
        | lambda bodyTyped => exact ⟨bodyTyped, tail⟩
  · rintro ⟨bodyTyped, tail⟩
    exact .cons (by simp [MatchesParameterRepresentation]) rfl (.lambda bodyTyped) tail

/-- A change of category interpretation leaves source-name resolution
coherent. No injectivity of the type map is needed: source occurrences,
including duplicate slots, are not identified by their image types. -/
theorem candidates_map_types (slots : BinderSlots) (name : String)
    (mapType : TypeExpr → TypeExpr) :
    candidates (slots.map fun slot => (slot.1, mapType slot.2)) name =
      (candidates slots name).map mapType := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
      by_cases same : slot.1 = name <;> simp_all [candidates]

theorem resolveDomain_map_types (slots : BinderSlots) (name : String)
    (mapType : TypeExpr → TypeExpr) :
    resolveDomain? (slots.map fun slot => (slot.1, mapType slot.2)) name =
      (resolveDomain? slots name).map mapType := by
  simp only [resolveDomain?, candidates_map_types]
  cases candidates slots name with
  | nil => rfl
  | cons domain remaining => cases remaining <;> rfl

/-- Scope and object formation are unchanged by the wrapper, except for its
one additional locally bound level. This excludes unresolved schema forms. -/
theorem elaborated_object_iff (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (domain codomain : TypeExpr) (body : Pattern) :
    OpenPatternWellSorted language free bound (.arrow domain codomain) (.lambda none body) ↔
      OpenPatternWellSorted language free (domain :: bound) codomain body := by
  simp only [OpenPatternWellSorted, Pattern.hasCanonicalBinderMetadata,
    Option.isNone_none, Bool.true_and, isObjectPattern, ScopeSafeAt,
    Pattern.isWellScopedAt, List.length_cons]
  constructor
  · rintro ⟨typed, canonical, object, inScope⟩
    cases typed with
    | lambda bodyTyped => exact ⟨bodyTyped, canonical, object, inScope⟩
  · rintro ⟨typed, canonical, object, inScope⟩
    exact ⟨.lambda typed, canonical, object, inScope⟩

/-! ## Independent closed-carrier controls -/

private def nameType := TypeExpr.base "Name"
private def exprType := TypeExpr.base "Expr"

def bindingLanguage : LanguageDef where
  name := "BindingValues"
  types := [⟨"Name", .ast⟩, ⟨"Expr", .ast⟩]
  terms := [
    { label := "Zero", category := "Expr", params := [], syntaxPattern := [.terminal "z"] },
    { label := "Ref", category := "Expr", params := [.simple "argument:0" nameType], syntaxPattern := [] },
    { label := "Lam", category := "Expr",
      params := [.abstractionNamed (some "x") "argument:1" (.arrow nameType exprType)],
      syntaxPattern := [.terminal "lam", .nonTerminal "x", .terminal ".", .nonTerminal "argument:1"] }]
  equations := []
  rewrites := []

def nestedOuterReference : Pattern :=
  .apply "Lam" [.lambda none (.apply "Lam" [.lambda none (.apply "Ref" [.bvar 1])])]

theorem resolved_parameter_control :
    elaborateParameter? [("x", nameType)] "x" "argument:1" exprType =
      some (.abstractionNamed (some "x") "argument:1" (.arrow nameType exprType)) := by decide

theorem unknown_and_ambiguous_controls :
    resolveDomain? [("x", nameType)] "y" = none ∧
    resolveDomain? [("x", nameType), ("x", exprType)] "x" = none := by decide

theorem nested_outer_reference_is_closed :
    checkClosedTerm bindingLanguage ⟨"Expr", by decide⟩
      nestedOuterReference = true := by decide +kernel

theorem escaped_reference_is_not_closed :
    checkClosedTerm bindingLanguage ⟨"Expr", by decide⟩
      (.apply "Lam" [.lambda none (.apply "Ref" [.bvar 1])]) = false := by decide +kernel

theorem in_scope_at_wrong_sort_is_rejected :
    checkClosedTerm bindingLanguage ⟨"Expr", by decide⟩
      (.apply "Lam" [.lambda none (.bvar 0)]) = false := by decide +kernel

theorem binder_erasure_changes_typing :
    ¬ ArgumentsHaveTypes bindingLanguage FreeTypeContext.empty []
      [.apply "Zero" []] [.abstractionNamed (some "x") "argument:1" (.arrow nameType exprType)] := by
  intro typed
  cases typed with
  | cons representation _ _ _ => cases representation

theorem duplicate_declarations_do_not_prevent_membership :
    checkClosedTerm { bindingLanguage with terms := bindingLanguage.terms ++ bindingLanguage.terms }
      ⟨"Expr", by decide⟩ nestedOuterReference = true := by decide +kernel

#print axioms elaboration_scope
#print axioms elaboration_typing_iff
#print axioms resolveDomain_map_types
#print axioms elaborated_object_iff
#print axioms nested_outer_reference_is_closed
#print axioms escaped_reference_is_not_closed

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.BindingDeclarationElaboration
