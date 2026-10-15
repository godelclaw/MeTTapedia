import Mettapedia.OSLF.Framework.RedexPosition
import Mettapedia.OSLF.MeTTaIL.ScopedReflectiveExecution

open Mettapedia.OSLF.Framework

/-!
# Scoped filling of a generated modal context

The hole is a term in its own exact binder context. The surrounding authored
pattern is instantiated at its original occurrence addresses. In particular,
explicit substitution nodes execute their binder operation; they do not need
to retain their raw parse-tree position after instantiation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.Instantiation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.Framework.RedexPosition

mutual

/-- Instantiate every authored component except the selected hole. -/
def fill? (operation : Pattern → Pattern → Pattern)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (hole : Pattern) : Pattern → Position → Option Pattern
  | _, [] => some hole
  | .apply constructor arguments, index :: rest => do
      let results ← fillArgs? operation rule spec ambient site path depth assignment
        hole index rest 0 arguments
      some (.apply constructor results)
  | .lambda binder body, 0 :: rest => do
      let result ← fill? operation rule spec ambient site (path ++ [0]) (depth + 1)
        assignment hole body rest
      some (.lambda binder result)
  | .multiLambda arity binders body, 0 :: rest => do
      let result ← fill? operation rule spec ambient site (path ++ [0]) (depth + arity)
        assignment hole body rest
      some (.multiLambda arity binders result)
  | .subst body replacement, 0 :: rest => do
      let body' ← fill? operation rule spec ambient site (path ++ [0]) (depth + 1)
        assignment hole body rest
      let replacement' ← instantiateWith? operation rule spec ambient site (path ++ [1]) depth
        assignment replacement
      some (operation replacement' body')
  | .subst body replacement, 1 :: rest => do
      let body' ← instantiateWith? operation rule spec ambient site (path ++ [0]) (depth + 1)
        assignment body
      let replacement' ← fill? operation rule spec ambient site (path ++ [1]) depth
        assignment hole replacement rest
      some (operation replacement' body')
  | .collection kind elements restVariable, index :: rest => do
      let explicit ← fillArgs? operation rule spec ambient site path depth assignment
        hole index rest 0 elements
      match restVariable with
      | none => some (.collection kind explicit none)
      | some name =>
          let value ← lookup assignment name
          let arguments ← arguments? rule spec name site (path ++ [elements.length])
          match ← instantiateValue? value ambient depth arguments with
          | .collection actualKind residual none =>
              if actualKind == kind then some (.collection kind (explicit ++ residual) none)
              else none
          | _ => none
  | _, _ :: _ => none
termination_by pattern _position => sizeOf pattern

/-- Ordered siblings retain their original addresses and binder contexts. -/
def fillArgs? (operation : Pattern → Pattern → Pattern)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (hole : Pattern) (selected : Nat) (rest : Position)
    (offset : Nat) : List Pattern → Option (List Pattern)
  | [] => none
  | pattern :: patterns => do
      let head ← if selected = 0 then
        fill? operation rule spec ambient site (path ++ [offset]) depth assignment hole pattern rest
      else instantiateWith? operation rule spec ambient site (path ++ [offset]) depth assignment pattern
      let tail ← if selected = 0 then
        instantiateArgsWith? operation rule spec ambient site path depth assignment (offset + 1) patterns
      else fillArgs? operation rule spec ambient site path depth assignment hole (selected - 1) rest (offset + 1) patterns
      some (head :: tail)
termination_by patterns => sizeOf patterns

end

/-- An independently selected focus and its scoped instantiatedFocus. This follows the
authored syntax, not the filling implementation. -/
inductive FocusInstance (operation : Pattern → Pattern → Pattern)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (assignment : Assignment) :
    List Nat → Nat → Pattern → Position → Pattern → Prop where
  | here {path : List Nat} {depth : Nat} {pattern instantiatedFocus : Pattern} :
      instantiateWith? operation rule spec ambient site path depth assignment pattern = some instantiatedFocus →
      FocusInstance operation rule spec ambient site assignment path depth pattern [] instantiatedFocus
  | application {path : List Nat} {depth : Nat} {constructor : String}
      {arguments : List Pattern} {index : Nat} {argument instantiatedFocus : Pattern} {rest : Position} :
      arguments[index]? = some argument →
      FocusInstance operation rule spec ambient site assignment (path ++ [index]) depth
        argument rest instantiatedFocus →
      FocusInstance operation rule spec ambient site assignment path depth
        (.apply constructor arguments) (index :: rest) instantiatedFocus
  | lambda {path : List Nat} {depth : Nat} {binder : Option String}
      {body instantiatedFocus : Pattern} {rest : Position} :
      FocusInstance operation rule spec ambient site assignment (path ++ [0]) (depth + 1)
        body rest instantiatedFocus →
      FocusInstance operation rule spec ambient site assignment path depth (.lambda binder body)
        (0 :: rest) instantiatedFocus
  | multiLambda {path : List Nat} {depth arity : Nat} {binders : List String}
      {body instantiatedFocus : Pattern} {rest : Position} :
      FocusInstance operation rule spec ambient site assignment (path ++ [0]) (depth + arity)
        body rest instantiatedFocus →
      FocusInstance operation rule spec ambient site assignment path depth (.multiLambda arity binders body)
        (0 :: rest) instantiatedFocus
  | substitutionBody {path : List Nat} {depth : Nat} {body replacement instantiatedFocus : Pattern}
      {rest : Position} :
      FocusInstance operation rule spec ambient site assignment (path ++ [0]) (depth + 1)
        body rest instantiatedFocus →
      FocusInstance operation rule spec ambient site assignment path depth (.subst body replacement)
        (0 :: rest) instantiatedFocus
  | substitutionArgument {path : List Nat} {depth : Nat} {body replacement instantiatedFocus : Pattern}
      {rest : Position} :
      FocusInstance operation rule spec ambient site assignment (path ++ [1]) depth
        replacement rest instantiatedFocus →
      FocusInstance operation rule spec ambient site assignment path depth (.subst body replacement)
        (1 :: rest) instantiatedFocus
  | collection {path : List Nat} {depth : Nat} {kind : CollType} {elements : List Pattern}
      {restVariable : Option String} {index : Nat} {element instantiatedFocus : Pattern} {rest : Position} :
      elements[index]? = some element →
      FocusInstance operation rule spec ambient site assignment (path ++ [index]) depth
        element rest instantiatedFocus →
      FocusInstance operation rule spec ambient site assignment path depth
        (.collection kind elements restVariable) (index :: rest) instantiatedFocus

private theorem fillArgs_authored (operation : Pattern → Pattern → Pattern)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite)
    (path : List Nat) (depth : Nat) (assignment : Assignment) (hole : Pattern)
    (rest : Position) : ∀ (patterns : List Pattern) (offset selected : Nat) (pattern : Pattern),
    patterns[selected]? = some pattern →
    fill? operation rule spec ambient site (path ++ [offset + selected]) depth assignment
      hole pattern rest = instantiateWith? operation rule spec ambient site
        (path ++ [offset + selected]) depth assignment pattern →
    fillArgs? operation rule spec ambient site path depth assignment hole selected rest offset patterns =
      instantiateArgsWith? operation rule spec ambient site path depth assignment offset patterns := by
  intro patterns
  induction patterns with
  | nil => intro _ _ _ impossible _; simp at impossible
  | cons head tail ih =>
      intro offset selected pattern located filling
      cases selected with
      | zero =>
          have same : head = pattern := Option.some.inj located
          cases same
          simp only [Nat.add_zero] at filling
          simp only [fillArgs?, instantiateArgsWith?, ↓reduceIte, filling]
      | succ selected =>
          have located' : tail[selected]? = some pattern := located
          have filling' : fill? operation rule spec ambient site (path ++ [offset + 1 + selected])
              depth assignment hole pattern rest = instantiateWith? operation rule spec ambient site
                (path ++ [offset + 1 + selected]) depth assignment pattern := by
            simpa only [Nat.add_assoc, Nat.add_comm 1 selected] using filling
          simp only [fillArgs?, instantiateArgsWith?, Nat.succ_ne_zero, ↓reduceIte,
            Nat.add_one_sub_one, ih (offset + 1) selected pattern located' filling']

/-- Filling with the scoped instantiatedFocus of the authored focus reproduces the
whole authored source, including binder elimination and collection rests. -/
theorem fill_authored {operation : Pattern → Pattern → Pattern}
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
    {assignment : Assignment} {path : List Nat} {depth : Nat}
    {pattern instantiatedFocus : Pattern} {position : Position}
    (selected : FocusInstance operation rule spec ambient site assignment path depth pattern position instantiatedFocus) :
    fill? operation rule spec ambient site path depth assignment instantiatedFocus pattern position =
      instantiateWith? operation rule spec ambient site path depth assignment pattern := by
  induction selected with
  | here instantiated => simpa only [fill?] using instantiated.symm
  | @application path depth constructor arguments index argument instantiatedFocus rest located _ ih =>
      simp only [fill?, instantiateWith?,
        fillArgs_authored operation rule spec ambient site path depth assignment instantiatedFocus rest
          arguments 0 index argument located (by simpa using ih)]
  | lambda _ ih => simp only [fill?, instantiateWith?, ih]
  | multiLambda _ ih => simp only [fill?, instantiateWith?, ih]
  | substitutionBody _ ih => simp only [fill?, instantiateWith?, ih]
  | substitutionArgument _ ih => simp only [fill?, instantiateWith?, ih]
  | @collection path depth kind elements restVariable index element instantiatedFocus rest located _ ih =>
      simp only [fill?, instantiateWith?,
        fillArgs_authored operation rule spec ambient site path depth assignment instantiatedFocus rest
          elements 0 index element located (by simpa using ih)]
      rfl

/-- Every independently selected instantiatedFocus has a genuine authored position. -/
theorem FocusInstance.position {operation : Pattern → Pattern → Pattern}
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
    {assignment : Assignment} {path : List Nat} {depth : Nat}
    {pattern instantiatedFocus : Pattern} {position : Position}
    (selected : FocusInstance operation rule spec ambient site assignment path depth pattern position instantiatedFocus) :
    ∃ focus, subtermAt pattern position = some focus := by
  induction selected with
  | here => exact ⟨_, rfl⟩
  | application located _ ih =>
      obtain ⟨focus, found⟩ := ih
      exact ⟨focus, by simp only [subtermAt, childAt, children, located, Option.bind_some, found]⟩
  | lambda _ ih =>
      obtain ⟨focus, found⟩ := ih
      exact ⟨focus, by simp only [subtermAt, childAt, children, List.getElem?_cons_zero,
        Option.bind_some, found]⟩
  | multiLambda _ ih =>
      obtain ⟨focus, found⟩ := ih
      exact ⟨focus, by simp only [subtermAt, childAt, children, List.getElem?_cons_zero,
        Option.bind_some, found]⟩
  | substitutionBody _ ih =>
      obtain ⟨focus, found⟩ := ih
      exact ⟨focus, by simp only [subtermAt, childAt, children, List.getElem?_cons_zero,
        Option.bind_some, found]⟩
  | substitutionArgument _ ih =>
      obtain ⟨focus, found⟩ := ih
      exact ⟨focus, by simp only [subtermAt, childAt, children, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.bind_some, found]⟩
  | collection located _ ih =>
      obtain ⟨focus, found⟩ := ih
      exact ⟨focus, by simp only [subtermAt, childAt, children, located, Option.bind_some, found]⟩

end Mettapedia.OSLF.NativeTypes.Modal.Instantiation
