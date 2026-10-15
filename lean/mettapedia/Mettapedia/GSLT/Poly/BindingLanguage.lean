import Mettapedia.GSLT.Poly.BindingSignature
import Mettapedia.GSLT.LanguageDef.WellSorted

/-!
# A binder fragment of a language as a binding signature

Constructors whose parameters are ordinary arguments at base sorts, one
abstraction of an arrow of base sorts, or a multi-binder of a base sort,
determine a binding signature. The same-sort shorthand stores only the body
sort and means the arrow with both ends equal. A multi-binder stores either
that shorthand or an arrow whose domain is a `multiBinder` of a base sort.
The number of variables a multi-binder binds is chosen by the occurrence, so
an operator is a constructor together with those counts. A direction then
lands in the context extended by that many copies of the binder sort.

Each binding term prints as an `apply` pattern. An ordinary binder is an
unnamed `lambda`. A multi-binder is an unnamed `multiLambda`. Variables are
de Bruijn `bvar` indices. The language's own `HasType` judgment types the
print in the bound context of base sorts.

When every constructor lies in this fragment and labels are distinct, the
closed object patterns typed at a base sort are exactly those terms, and
therefore exactly the free-monad trees of the context-indexed polynomial
at the empty context.

A collection parameter stays outside the fragment, as does a multi-binder
whose domain is not a base sort.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.BindingLanguage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Poly.BindingSignature
open IPFunctor

/-- Binder sort and body sort of a base-sort multi-binder. -/
def multiBase? : TermParam → Option (String × String)
  | .multiAbstractionNamed _ _ (.base sort) => some (sort, sort)
  | .multiAbstractionNamed _ _ (.arrow (.multiBinder (.base domain)) (.base body)) =>
      some (domain, body)
  | _ => none

/-- The binding declaration of one parameter, when it belongs to the fragment.

A simple parameter at a base sort binds nothing. An abstraction whose type is
an arrow of base sorts binds one variable of the domain sort and returns the
codomain sort. The same-sort shorthand stores only the body sort and means
that same arrow. A base-sort multi-binder records one copy of its binder sort
here; the occurrence chooses how many copies to open. -/
def bindingDecl? : TermParam → Option (List String × String)
  | .simple _ (.base sort) => some ([], sort)
  | .abstractionNamed _ _ (.arrow (.base domain) (.base body)) => some ([domain], body)
  | .abstractionNamed _ _ (.base sort) => some ([sort], sort)
  | .multiAbstractionNamed _ _ (.base sort) => some ([sort], sort)
  | .multiAbstractionNamed _ _ (.arrow (.multiBinder (.base domain)) (.base body)) =>
      some ([domain], body)
  | _ => none

/-- Every parameter of the rule lies in the binder fragment. -/
def BinderRule (rule : GrammarRule) : Prop :=
  ∀ parameter ∈ rule.params, (bindingDecl? parameter).isSome

/-- Which fragment shape a parameter has. -/
inductive InFragment : TermParam → Prop where
  | simple (name sort : String) : InFragment (.simple name (.base sort))
  | abstraction (binder : Option String) (bodyName domain body : String) :
      InFragment (.abstractionNamed binder bodyName (.arrow (.base domain) (.base body)))
  | shorthand (binder : Option String) (bodyName sort : String) :
      InFragment (.abstractionNamed binder bodyName (.base sort))
  | multiShorthand (binders : List String) (bodyName sort : String) :
      InFragment (.multiAbstractionNamed binders bodyName (.base sort))
  | multi (binders : List String) (bodyName domain body : String) :
      InFragment (.multiAbstractionNamed binders bodyName
        (.arrow (.multiBinder (.base domain)) (.base body)))

theorem inFragment_of_isSome {parameter : TermParam} (ok : (bindingDecl? parameter).isSome) :
    InFragment parameter := by
  cases parameter with
  | simple name type =>
      cases type with
      | base sort => exact .simple name sort
      | arrow _ _ => simp [bindingDecl?] at ok
      | multiBinder _ => simp [bindingDecl?] at ok
      | collection _ _ => simp [bindingDecl?] at ok
  | abstractionNamed binder bodyName type =>
      cases type with
      | base sort => exact .shorthand binder bodyName sort
      | arrow domain codomain =>
          cases domain with
          | base domainSort =>
              cases codomain with
              | base bodySort => exact .abstraction binder bodyName domainSort bodySort
              | arrow _ _ => simp [bindingDecl?] at ok
              | multiBinder _ => simp [bindingDecl?] at ok
              | collection _ _ => simp [bindingDecl?] at ok
          | arrow _ _ => simp [bindingDecl?] at ok
          | multiBinder _ => simp [bindingDecl?] at ok
          | collection _ _ => simp [bindingDecl?] at ok
      | multiBinder _ => simp [bindingDecl?] at ok
      | collection _ _ => simp [bindingDecl?] at ok
  | multiAbstractionNamed binders bodyName type =>
      cases type with
      | base sort => exact .multiShorthand binders bodyName sort
      | arrow domain codomain =>
          cases domain with
          | multiBinder domainType =>
              cases domainType with
              | base domainSort =>
                  cases codomain with
                  | base bodySort => exact .multi binders bodyName domainSort bodySort
                  | arrow _ _ => simp [bindingDecl?] at ok
                  | multiBinder _ => simp [bindingDecl?] at ok
                  | collection _ _ => simp [bindingDecl?] at ok
              | arrow _ _ => simp [bindingDecl?] at ok
              | multiBinder _ => simp [bindingDecl?] at ok
              | collection _ _ => simp [bindingDecl?] at ok
          | base _ => simp [bindingDecl?] at ok
          | arrow _ _ => simp [bindingDecl?] at ok
          | collection _ _ => simp [bindingDecl?] at ok
      | multiBinder _ => simp [bindingDecl?] at ok
      | collection _ _ => simp [bindingDecl?] at ok

/-- Binders and result sort of one parameter at a chosen multi-binder count.
Counts on parameters that are not multi-binders are ignored. -/
def slotBinders (parameter : TermParam) (count : Nat) : List String × String :=
  match parameter with
  | .simple _ (.base sort) => ([], sort)
  | .abstractionNamed _ _ (.arrow (.base domain) (.base body)) => ([domain], body)
  | .abstractionNamed _ _ (.base sort) => ([sort], sort)
  | .multiAbstractionNamed _ _ (.base sort) => (List.replicate count sort, sort)
  | .multiAbstractionNamed _ _ (.arrow (.multiBinder (.base domain)) (.base body)) =>
      (List.replicate count domain, body)
  | _ => ([], "")

/-- A base-sort multi-binder opens as many copies of its binder sort as the
occurrence chooses. -/
theorem slotBinders_of_multiBase {parameter : TermParam} {domain body : String}
    (shape : multiBase? parameter = some (domain, body)) (count : Nat) :
    slotBinders parameter count = (List.replicate count domain, body) := by
  cases parameter with
  | simple _ type => simp [multiBase?] at shape
  | abstractionNamed _ _ type => simp [multiBase?] at shape
  | multiAbstractionNamed _ _ type =>
      cases type with
      | base sort =>
          simp [multiBase?, slotBinders] at shape
          obtain ⟨rfl, rfl⟩ := shape
          rfl
      | arrow domainType codomain =>
          cases domainType with
          | multiBinder inner =>
              cases inner with
              | base domainSort =>
                  cases codomain with
                  | base bodySort =>
                      simp [multiBase?, slotBinders] at shape
                      obtain ⟨rfl, rfl⟩ := shape
                      rfl
                  | arrow _ _ => simp [multiBase?] at shape
                  | multiBinder _ => simp [multiBase?] at shape
                  | collection _ _ => simp [multiBase?] at shape
              | arrow _ _ => simp [multiBase?] at shape
              | multiBinder _ => simp [multiBase?] at shape
              | collection _ _ => simp [multiBase?] at shape
          | base _ => simp [multiBase?] at shape
          | arrow _ _ => simp [multiBase?] at shape
          | collection _ _ => simp [multiBase?] at shape
      | multiBinder _ => simp [multiBase?] at shape
      | collection _ _ => simp [multiBase?] at shape

/-- Argument declarations of a parameter list at the chosen counts. -/
def slots : List TermParam → List Nat → List (List String × String)
  | [], _ => []
  | _, [] => []
  | parameter :: parameters, count :: counts =>
      slotBinders parameter count :: slots parameters counts

/-- Placeholder parameter used only when an index falls outside a parameter list. -/
def missingParameter : TermParam := .simple "" (.base "")

/-- Counts chosen by one occurrence. A parameter that is not a base-sort
multi-binder contributes the count zero. -/
structure Occurrence (parameters : List TermParam) where
  counts : List Nat
  length_eq : counts.length = parameters.length
  fixed : ∀ i : Nat,
    (multiBase? (parameters.getD i missingParameter)).isNone → counts.getD i 0 = 0

namespace Occurrence

def cons {parameter : TermParam} {parameters : List TermParam} (count : Nat)
    (canonical : (multiBase? parameter).isNone → count = 0)
    (tail : Occurrence parameters) : Occurrence (parameter :: parameters) where
  counts := count :: tail.counts
  length_eq := by simp [List.length_cons, tail.length_eq]
  fixed := by
    intro index premise
    cases index with
    | zero =>
        have notMulti : (multiBase? parameter).isNone := by
          simpa [List.getD, missingParameter] using premise
        simpa [List.getD] using canonical notMulti
    | succ index =>
        have tailPremise :
            (multiBase? (parameters.getD index missingParameter)).isNone := by
          simpa [List.getD, missingParameter] using premise
        simpa [List.getD] using tail.fixed index tailPremise

theorem ext {parameters : List TermParam} {left right : Occurrence parameters}
    (same : left.counts = right.counts) : left = right := by
  cases left with
  | mk counts leftLength leftFixed =>
      cases right with
      | mk _ rightLength rightFixed =>
          cases same
          have lengths : leftLength = rightLength := Subsingleton.elim _ _
          subst lengths
          have fixedEqual : leftFixed = rightFixed := by
            funext index premise
            exact Subsingleton.elim _ _
          subst fixedEqual
          rfl

end Occurrence

theorem getD_replicate_zero (count index : Nat) :
    (List.replicate count 0).getD index 0 = 0 := by
  induction count generalizing index with
  | zero => simp [List.getD, List.replicate]
  | succ count inductionHypothesis =>
      cases index with
      | zero => simp [List.getD, List.replicate]
      | succ index =>
          show (0 :: List.replicate count 0).getD index.succ 0 = 0
          simp only [List.getD, List.getElem?_cons_succ]
          exact inductionHypothesis index

/-- The unique occurrence that chooses no multi-binders. -/
def plainOccurrence (parameters : List TermParam)
    (_plain : ∀ parameter ∈ parameters, (multiBase? parameter).isNone) :
    Occurrence parameters where
  counts := List.replicate parameters.length 0
  length_eq := by simp
  fixed := by
    intro index _
    exact getD_replicate_zero parameters.length index

/-- The binding signature of the fragment. An operator of a sort is a
constructor of that category whose parameters lie in the fragment, together
with the multi-binder counts of one occurrence. -/
abbrev signature (language : LanguageDef) : Signature where
  Srt := String
  Op sort :=
    Σ rule : {rule : GrammarRule //
      rule ∈ language.terms ∧ BinderRule rule ∧ rule.category = sort},
      Occurrence rule.1.params
  arity operator := slots operator.1.1.params operator.2.counts

theorem not_usesBareCollection {rule : GrammarRule} (bound : BinderRule rule) :
    ¬ UsesBareCollection rule := by
  rintro ⟨name, collectionType, elementType, shape⟩
  have ok := bound (.simple name (.collection collectionType elementType)) (by simp [shape])
  simp [bindingDecl?] at ok

variable {language : LanguageDef}

/-- Bound context of a binding context: each variable has its base sort. -/
def typeContext (Γ : List String) : List TypeExpr :=
  Γ.map .base

theorem lookup_base {Γ : List String} {index : Nat} {sort : String}
    (found : (typeContext Γ)[index]? = some (.base sort)) :
    Γ[index]? = some sort := by
  induction Γ generalizing index sort with
  | nil => simp [typeContext] at found
  | cons head tail inductionHypothesis =>
      cases index with
      | zero =>
          simp [typeContext, TypeExpr.base.injEq] at found
          subst found
          rfl
      | succ index =>
          apply inductionHypothesis
          simpa [typeContext, List.getElem?_cons_succ] using found

/-- De Bruijn index of a binding variable. The head of the context is index 0. -/
def varIndex {Γ : List String} {sort : String} : Var Γ sort → Nat
  | .zero => 0
  | .succ variable_ => varIndex variable_ + 1

theorem varIndex_injective {Γ : List String} {sort : String} :
    (left right : Var Γ sort) → varIndex left = varIndex right → left = right
  | .zero, .zero, _ => rfl
  | .zero, .succ _, same => by
      simp [varIndex] at same
  | .succ _, .zero, same => by
      simp [varIndex] at same
  | .succ left, .succ right, same => by
      simp only [varIndex] at same
      exact congrArg Var.succ (varIndex_injective left right (Nat.succ.inj same))

theorem varIndex_lookup {Γ : List String} {sort : String} (variable_ : Var Γ sort) :
    (typeContext Γ)[varIndex variable_]? = some (.base sort) := by
  induction variable_ with
  | zero => simp [varIndex, typeContext]
  | succ variable_ inductionHypothesis =>
      simpa [varIndex, typeContext, List.getElem?_cons_succ] using inductionHypothesis

theorem exists_var_of_get {Γ : List String} {sort : String} {index : Nat}
    (found : Γ[index]? = some sort) :
    ∃ variable_ : Var Γ sort, varIndex variable_ = index := by
  induction Γ generalizing index sort with
  | nil => simp at found
  | cons head tail inductionHypothesis =>
      cases index with
      | zero =>
          simp at found
          subst found
          exact ⟨.zero, by simp [varIndex]⟩
      | succ index =>
          simp at found
          obtain ⟨variable_, printed⟩ := inductionHypothesis found
          exact ⟨.succ variable_, by simp [varIndex, printed]⟩

/-- Wrap a body in one unnamed lambda per bound sort. The head of the list is
the innermost binder. -/
def wrapBinders : List String → Pattern → Pattern
  | [], pattern => pattern
  | _ :: binders, pattern => wrapBinders binders (.lambda none pattern)

theorem wrapBinders_injective (binders : List String) :
    Function.Injective (wrapBinders binders) := by
  intro left right same
  induction binders generalizing left right with
  | nil => simpa [wrapBinders] using same
  | cons _ binders inductionHypothesis =>
      have equal := inductionHypothesis (by simpa [wrapBinders] using same)
      simp only [Pattern.lambda.injEq] at equal
      exact equal.2

theorem wrapBinders_isObject (binders : List String) {pattern : Pattern}
    (object : isObjectPattern pattern = true) :
    isObjectPattern (wrapBinders binders pattern) = true := by
  induction binders generalizing pattern with
  | nil => simpa [wrapBinders] using object
  | cons _ binders inductionHypothesis =>
      simpa [wrapBinders] using
        inductionHypothesis (by simpa [isObjectPattern] using object)

/-- Print one argument. A base-sort multi-binder is one unnamed `multiLambda`
of the occurrence's count. Every other fragment parameter uses one unnamed
`lambda` per bound sort. -/
def printArgument (parameter : TermParam) (count : Nat) (body : Pattern) : Pattern :=
  match parameter with
  | .multiAbstractionNamed _ _ (.base _) => .multiLambda count [] body
  | .multiAbstractionNamed _ _ (.arrow (.multiBinder (.base _)) (.base _)) =>
      .multiLambda count [] body
  | _ => wrapBinders (slotBinders parameter count).1 body

theorem printArgument_isObject (parameter : TermParam) (count : Nat) {body : Pattern}
    (object : isObjectPattern body = true) :
    isObjectPattern (printArgument parameter count body) = true := by
  cases parameter with
  | simple _ type =>
      cases type <;>
        simpa [printArgument, slotBinders, wrapBinders, isObjectPattern] using object
  | abstractionNamed _ _ type =>
      cases type with
      | base _ =>
          simpa [printArgument, slotBinders, wrapBinders, isObjectPattern] using object
      | arrow domain codomain =>
          cases domain <;> cases codomain <;>
            simpa [printArgument, slotBinders, wrapBinders, isObjectPattern] using object
      | multiBinder _ =>
          simpa [printArgument, slotBinders, wrapBinders, isObjectPattern] using object
      | collection _ _ =>
          simpa [printArgument, slotBinders, wrapBinders, isObjectPattern] using object
  | multiAbstractionNamed _ _ type =>
      cases type with
      | base _ =>
          simpa [printArgument, isObjectPattern] using object
      | arrow domain codomain =>
          cases domain with
          | multiBinder inner =>
              cases inner <;> cases codomain <;>
                simpa [printArgument, slotBinders, wrapBinders, isObjectPattern] using object
          | base _ =>
              simpa [printArgument, slotBinders, wrapBinders, isObjectPattern] using object
          | arrow _ _ =>
              simpa [printArgument, slotBinders, wrapBinders, isObjectPattern] using object
          | collection _ _ =>
              simpa [printArgument, slotBinders, wrapBinders, isObjectPattern] using object
      | multiBinder _ =>
          simpa [printArgument, slotBinders, wrapBinders, isObjectPattern] using object
      | collection _ _ =>
          simpa [printArgument, slotBinders, wrapBinders, isObjectPattern] using object

theorem printArgument_injective (parameter : TermParam) (count : Nat) :
    Function.Injective (printArgument parameter count) := by
  intro left right same
  cases parameter with
  | simple _ type =>
      cases type <;>
        simpa only [printArgument, slotBinders, wrapBinders] using same
  | abstractionNamed _ _ type =>
      cases type with
      | base _ =>
          simp only [printArgument, slotBinders, wrapBinders] at same
          injection same
      | arrow domain codomain =>
          cases domain with
          | base _ =>
              cases codomain with
              | base _ =>
                  simp only [printArgument, slotBinders, wrapBinders] at same
                  injection same
              | arrow _ _ =>
                  simpa only [printArgument, slotBinders, wrapBinders] using same
              | multiBinder _ =>
                  simpa only [printArgument, slotBinders, wrapBinders] using same
              | collection _ _ =>
                  simpa only [printArgument, slotBinders, wrapBinders] using same
          | arrow _ _ =>
              simpa only [printArgument, slotBinders, wrapBinders] using same
          | multiBinder _ =>
              simpa only [printArgument, slotBinders, wrapBinders] using same
          | collection _ _ =>
              simpa only [printArgument, slotBinders, wrapBinders] using same
      | multiBinder _ =>
          simpa only [printArgument, slotBinders, wrapBinders] using same
      | collection _ _ =>
          simpa only [printArgument, slotBinders, wrapBinders] using same
  | multiAbstractionNamed _ _ type =>
      cases type with
      | base _ =>
          simp only [printArgument] at same
          injection same
      | arrow domain codomain =>
          cases domain with
          | multiBinder inner =>
              cases inner with
              | base _ =>
                  cases codomain with
                  | base _ =>
                      simp only [printArgument] at same
                      injection same
                  | arrow _ _ =>
                      simpa only [printArgument, slotBinders, wrapBinders] using same
                  | multiBinder _ =>
                      simpa only [printArgument, slotBinders, wrapBinders] using same
                  | collection _ _ =>
                      simpa only [printArgument, slotBinders, wrapBinders] using same
              | arrow _ _ =>
                  simpa only [printArgument, slotBinders, wrapBinders] using same
              | multiBinder _ =>
                  simpa only [printArgument, slotBinders, wrapBinders] using same
              | collection _ _ =>
                  simpa only [printArgument, slotBinders, wrapBinders] using same
          | base _ =>
              simpa only [printArgument, slotBinders, wrapBinders] using same
          | arrow _ _ =>
              simpa only [printArgument, slotBinders, wrapBinders] using same
          | collection _ _ =>
              simpa only [printArgument, slotBinders, wrapBinders] using same
      | multiBinder _ =>
          simpa only [printArgument, slotBinders, wrapBinders] using same
      | collection _ _ =>
          simpa only [printArgument, slotBinders, wrapBinders] using same

/-- The multi-binder count read back from a printed argument. Other parameters
contribute zero. -/
def observableCount (parameter : TermParam) (pattern : Pattern) : Nat :=
  match parameter with
  | .multiAbstractionNamed _ _ (.base _) =>
      match pattern with
      | .multiLambda count _ _ => count
      | _ => 0
  | .multiAbstractionNamed _ _ (.arrow (.multiBinder (.base _)) (.base _)) =>
      match pattern with
      | .multiLambda count _ _ => count
      | _ => 0
  | _ => 0

def observableCounts : List TermParam → List Pattern → List Nat
  | [], _ => []
  | _ :: _, [] => []
  | parameter :: parameters, pattern :: patterns =>
      observableCount parameter pattern :: observableCounts parameters patterns

theorem observableCount_print (parameter : TermParam) (count : Nat) (body : Pattern)
    (canonical : (multiBase? parameter).isNone → count = 0) :
    observableCount parameter (printArgument parameter count body) = count := by
  cases parameter with
  | simple _ type =>
      have countZero : count = 0 := canonical (by cases type <;> simp [multiBase?])
      simp [observableCount, countZero]
  | abstractionNamed _ _ type =>
      have countZero : count = 0 := canonical (by cases type <;> simp [multiBase?])
      simp [observableCount, countZero]
  | multiAbstractionNamed _ _ type =>
      cases type with
      | base _ =>
          simp [observableCount, printArgument]
      | arrow domain codomain =>
          cases domain with
          | multiBinder inner =>
              cases inner with
              | base _ =>
                  cases codomain with
                  | base _ => simp [observableCount, printArgument]
                  | arrow _ _ =>
                      have countZero : count = 0 := canonical (by simp [multiBase?])
                      simp [observableCount, countZero]
                  | multiBinder _ =>
                      have countZero : count = 0 := canonical (by simp [multiBase?])
                      simp [observableCount, countZero]
                  | collection _ _ =>
                      have countZero : count = 0 := canonical (by simp [multiBase?])
                      simp [observableCount, countZero]
              | arrow _ _ =>
                  have countZero : count = 0 := canonical (by simp [multiBase?])
                  simp [observableCount, countZero]
              | multiBinder _ =>
                  have countZero : count = 0 := canonical (by simp [multiBase?])
                  simp [observableCount, countZero]
              | collection _ _ =>
                  have countZero : count = 0 := canonical (by simp [multiBase?])
                  simp [observableCount, countZero]
          | base _ =>
              have countZero : count = 0 := canonical (by simp [multiBase?])
              simp [observableCount, countZero]
          | arrow _ _ =>
              have countZero : count = 0 := canonical (by simp [multiBase?])
              simp [observableCount, countZero]
          | collection _ _ =>
              have countZero : count = 0 := canonical (by simp [multiBase?])
              simp [observableCount, countZero]
      | multiBinder _ =>
          have countZero : count = 0 := canonical (by simp [multiBase?])
          simp [observableCount, countZero]
      | collection _ _ =>
          have countZero : count = 0 := canonical (by simp [multiBase?])
          simp [observableCount, countZero]

theorem isObjectPatternList_eq_true_iff :
    (patterns : List Pattern) →
      isObjectPatternList patterns = true ↔ ∀ pattern ∈ patterns, isObjectPattern pattern = true
  | [] => by simp [isObjectPatternList]
  | pattern :: patterns => by
      simp [isObjectPatternList, isObjectPatternList_eq_true_iff patterns]

mutual

/-- A binding term as an `apply` / `lambda` / `multiLambda` / `bvar` pattern. -/
def toPattern {Γ : List String} {sort : String} : Term (signature language) Γ sort → Pattern
  | .var variable_ => .bvar (varIndex variable_)
  | .op operator arguments =>
      .apply operator.1.1.label
        (patternsOfDecl operator.1.1.params operator.2.counts
          (slots operator.1.1.params operator.2.counts) arguments)

/-- Print arguments against an explicit declaration list. `Args.cons` is indexed
by a pair constructor, and `slotBinders` does not reduce to one while its
parameter is still a variable, so the declaration list is matched on its own. -/
def patternsOfDecl {Γ : List String} (parameters : List TermParam) (counts : List Nat) :
    (declarations : List (List String × String)) →
      Args (signature language) declarations Γ → List Pattern
  | [], .nil => []
  | (_binders, _sort) :: declarations, .cons head tail =>
      match parameters, counts with
      | parameter :: parameters, count :: counts =>
          printArgument parameter count (toPattern head) ::
            patternsOfDecl parameters counts declarations tail
      | _, _ => []

end

/-- The arguments of an operator. Each multi-binder is printed at its count. -/
abbrev patternsOf (parameters : List TermParam) (counts : List Nat) {Γ : List String}
    (arguments : Args (signature language) (slots parameters counts) Γ) : List Pattern :=
  patternsOfDecl parameters counts (slots parameters counts) arguments

theorem patternsOfDecl_cons {Γ : List String}
    (parameter : TermParam) (parameters : List TermParam) (count : Nat) (counts : List Nat)
    (binders : List String) (sort : String) (declarations : List (List String × String))
    (head : Term (signature language) (binders ++ Γ) sort)
    (tail : Args (signature language) declarations Γ) :
    patternsOfDecl (parameter :: parameters) (count :: counts) ((binders, sort) :: declarations)
      (Args.cons (bs := binders) (s := sort) head tail) =
    printArgument parameter count (toPattern head) ::
      patternsOfDecl parameters counts declarations tail := by
  simp only [patternsOfDecl]

mutual

/-- The number of operator nodes and argument nodes in a binding term. -/
def termSize {Γ : List String} {sort : String} : Term (signature language) Γ sort → Nat
  | .var _ => 0
  | .op _ arguments => argsSize arguments + 1

/-- The number of operator nodes and argument nodes in an argument list. -/
def argsSize {declarations : List (List String × String)} {Γ : List String} :
    Args (signature language) declarations Γ → Nat
  | .nil => 0
  | .cons head tail => termSize head + argsSize tail + 1

end

/-- A parameter outside the fragment contradicts the fragment hypothesis. -/
theorem argumentsOutside
    {parameter : TermParam} {parameters : List TermParam} {count : Nat} {counts : List Nat}
    (allBound : ∀ item ∈ parameter :: parameters, (bindingDecl? item).isSome)
    (outside : bindingDecl? parameter = none) {Γ : List String}
    (arguments : Args (signature language)
      (slots (parameter :: parameters) (count :: counts)) Γ) :
    ArgumentsHaveTypes language FreeTypeContext.empty (typeContext Γ)
      (patternsOf (parameter :: parameters) (count :: counts) arguments)
      (parameter :: parameters) := by
  have ok := allBound parameter (List.mem_cons_self)
  simp [outside] at ok

/-! ## Printed terms are typed by the language's own judgment -/

/-- Typing of a printed term and of its arguments, by induction on a size bound.
The bound is a plain `Nat`, so each recursive call is the induction hypothesis
applied to a strictly smaller term. -/
theorem printSized (n : Nat) :
    (∀ {Γ : List String} {sort : String} (term : Term (signature language) Γ sort),
        termSize term < n →
          HasType language FreeTypeContext.empty (typeContext Γ) (toPattern term) (.base sort)) ∧
    (∀ (parameters : List TermParam) (counts : List Nat)
        (aligned : counts.length = parameters.length)
        (allBound : ∀ parameter ∈ parameters, (bindingDecl? parameter).isSome)
        {Γ : List String} (declarations : List (List String × String))
        (same : declarations = slots parameters counts)
        (arguments : Args (signature language) declarations Γ),
        argsSize arguments < n →
          ArgumentsHaveTypes language FreeTypeContext.empty (typeContext Γ)
            (patternsOfDecl parameters counts declarations arguments) parameters) := by
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro Γ sort term small
        exact absurd small (Nat.not_lt_zero _)
      · intro parameters counts aligned allBound Γ declarations same arguments small
        exact absurd small (Nat.not_lt_zero _)
  | succ n inductionHypothesis =>
      obtain ⟨termSmall, argsSmall⟩ := inductionHypothesis
      refine ⟨?_, ?_⟩
      · intro Γ sort term small
        match term with
        | .var variable_ =>
            simpa [toPattern] using HasType.bvar (varIndex_lookup variable_)
        | .op operator arguments =>
            have argumentsSmall : argsSize arguments < n := by
              have : argsSize arguments + 1 < n + 1 := by simpa [termSize] using small
              omega
            have printed :=
              argsSmall operator.1.1.params operator.2.counts operator.2.length_eq
                operator.1.2.2.1 (slots operator.1.1.params operator.2.counts) rfl arguments
                argumentsSmall
            simpa [toPattern, operator.1.2.2.2] using
              HasType.constructor (rule := operator.1.1) operator.1.2.1
                (not_usesBareCollection operator.1.2.2.1) printed
      · intro parameters counts aligned allBound Γ declarations same arguments argumentsSmall
        match arguments with
        | .nil =>
            match parameters, counts with
            | [], _ =>
                simp [patternsOfDecl]
                exact ArgumentsHaveTypes.nil
            | _ :: _, [] =>
                simp at aligned
            | _ :: _, _ :: _ =>
                simp [slots] at same
        | .cons (bs := binders) (s := resultSort) (as := tailDeclarations) head tail =>
            match parameters, counts with
            | [], _ =>
                simp [slots] at same
            | _ :: _, [] =>
                simp [slots] at same
            | parameter :: parameters, count :: counts =>
                have decomposed :
                    (binders, resultSort) = slotBinders parameter count ∧
                      tailDeclarations = slots parameters counts := by
                  simpa [slots, List.cons.injEq] using same
                obtain ⟨headEq, tailEq⟩ := decomposed
                have tailAligned : counts.length = parameters.length := by
                  simp only [List.length_cons] at aligned
                  omega
                have tailBound : ∀ item ∈ parameters, (bindingDecl? item).isSome :=
                  fun item member => allBound item (List.mem_cons_of_mem _ member)
                have headSmall : termSize head < n := by
                  have : termSize head + argsSize tail + 1 < n + 1 := by
                    simpa [argsSize] using argumentsSmall
                  omega
                have tailSmall : argsSize tail < n := by
                  have : termSize head + argsSize tail + 1 < n + 1 := by
                    simpa [argsSize] using argumentsSmall
                  omega
                have tailTyped :=
                  argsSmall parameters counts tailAligned tailBound tailDeclarations tailEq tail
                    tailSmall
                match inFragment_of_isSome (allBound parameter (List.mem_cons_self)) with
                | .simple _ result =>
                    simp only [slotBinders] at headEq
                    have bindersEq : binders = [] := congrArg Prod.fst headEq
                    have sortEq : resultSort = result := congrArg Prod.snd headEq
                    subst bindersEq
                    subst sortEq
                    have headTyped := termSmall head headSmall
                    simp only [patternsOfDecl, printArgument, slotBinders, wrapBinders]
                    exact ArgumentsHaveTypes.cons trivial rfl headTyped tailTyped
                | .abstraction _ _ domain bodySort =>
                    simp only [slotBinders] at headEq
                    have bindersEq : binders = [domain] := congrArg Prod.fst headEq
                    have sortEq : resultSort = bodySort := congrArg Prod.snd headEq
                    subst bindersEq
                    subst sortEq
                    have bodyTyped :
                        HasType language FreeTypeContext.empty
                          (.base domain :: typeContext Γ) (toPattern head) (.base resultSort) := by
                      simpa [typeContext, List.map_append, List.map_cons, List.map_nil] using
                        termSmall head headSmall
                    simp only [patternsOfDecl, printArgument, slotBinders, wrapBinders]
                    exact ArgumentsHaveTypes.cons trivial rfl (HasType.lambda bodyTyped) tailTyped
                | .shorthand _ _ bodySort =>
                    simp only [slotBinders] at headEq
                    have bindersEq : binders = [bodySort] := congrArg Prod.fst headEq
                    have sortEq : resultSort = bodySort := congrArg Prod.snd headEq
                    subst bindersEq
                    subst sortEq
                    have bodyTyped :
                        HasType language FreeTypeContext.empty
                          (.base resultSort :: typeContext Γ) (toPattern head)
                          (.base resultSort) := by
                      simpa [typeContext, List.map_append, List.map_cons, List.map_nil] using
                        termSmall head headSmall
                    simp only [patternsOfDecl, printArgument, slotBinders, wrapBinders]
                    exact ArgumentsHaveTypes.cons trivial rfl (HasType.lambda bodyTyped) tailTyped
                | .multiShorthand _ _ result =>
                    simp only [slotBinders] at headEq
                    have bindersEq : binders = List.replicate count result :=
                      congrArg Prod.fst headEq
                    have sortEq : resultSort = result := congrArg Prod.snd headEq
                    subst bindersEq
                    subst sortEq
                    have bodyTyped :
                        HasType language FreeTypeContext.empty
                          (List.replicate count (.base resultSort) ++ typeContext Γ) (toPattern head)
                          (.base resultSort) := by
                      simpa [typeContext, List.map_append, List.map_replicate] using
                        termSmall head headSmall
                    simp only [patternsOfDecl, printArgument]
                    exact ArgumentsHaveTypes.cons trivial rfl
                      (HasType.multiLambda (binders := []) bodyTyped) tailTyped
                | .multi _ _ domain bodySort =>
                    simp only [slotBinders] at headEq
                    have bindersEq : binders = List.replicate count domain :=
                      congrArg Prod.fst headEq
                    have sortEq : resultSort = bodySort := congrArg Prod.snd headEq
                    subst bindersEq
                    subst sortEq
                    have bodyTyped :
                        HasType language FreeTypeContext.empty
                          (List.replicate count (.base domain) ++ typeContext Γ) (toPattern head)
                          (.base resultSort) := by
                      simpa [typeContext, List.map_append, List.map_replicate] using
                        termSmall head headSmall
                    simp only [patternsOfDecl, printArgument]
                    exact ArgumentsHaveTypes.cons trivial rfl
                      (HasType.multiLambda (binders := []) bodyTyped) tailTyped

theorem toPattern_hasType {Γ : List String} {sort : String}
    (term : Term (signature language) Γ sort) :
    HasType language FreeTypeContext.empty (typeContext Γ) (toPattern term) (.base sort) :=
  (printSized (termSize term + 1)).1 term (Nat.lt_succ_self _)

theorem patternsOfDecl_hasType
    (parameters : List TermParam) (counts : List Nat)
    (aligned : counts.length = parameters.length)
    (allBound : ∀ parameter ∈ parameters, (bindingDecl? parameter).isSome)
    {Γ : List String} (declarations : List (List String × String))
    (same : declarations = slots parameters counts)
    (arguments : Args (signature language) declarations Γ) :
    ArgumentsHaveTypes language FreeTypeContext.empty (typeContext Γ)
      (patternsOfDecl parameters counts declarations arguments) parameters :=
  (printSized (argsSize arguments + 1)).2 parameters counts aligned allBound declarations same
    arguments (Nat.lt_succ_self _)

mutual

theorem toPattern_isObjectPattern :
    {Γ : List String} → {sort : String} → (term : Term (signature language) Γ sort) →
      isObjectPattern (toPattern term) = true
  | _, _, .var _ => rfl
  | _, _, .op _ arguments => by
      simp only [toPattern, isObjectPattern]
      rw [isObjectPatternList_eq_true_iff]
      exact patternsOfDecl_isObject _ _ (slots _ _) arguments
termination_by _ _ term => termSize term
decreasing_by all_goals (dsimp only [termSize, argsSize]; omega)

theorem patternsOfDecl_isObject
    (parameters : List TermParam) (counts : List Nat) {Γ : List String}
    (declarations : List (List String × String))
    (arguments : Args (signature language) declarations Γ) :
    ∀ pattern ∈ patternsOfDecl parameters counts declarations arguments,
      isObjectPattern pattern = true := by
  match arguments with
  | .nil => simp [patternsOfDecl]
  | .cons head tail =>
      match parameters, counts with
      | [], _ => simp [patternsOfDecl]
      | _ :: _, [] => simp [patternsOfDecl]
      | parameter :: parameters, count :: counts =>
          simp only [patternsOfDecl, List.mem_cons, forall_eq_or_imp]
          exact ⟨printArgument_isObject parameter count (toPattern_isObjectPattern head),
            patternsOfDecl_isObject parameters counts _ tail⟩
termination_by argsSize arguments
decreasing_by all_goals (dsimp only [termSize, argsSize]; omega)

end

/-- The printed arguments determine the occurrence counts. -/
theorem patternsOfDecl_observable
    (parameters : List TermParam) (counts : List Nat)
    (aligned : counts.length = parameters.length)
    (fixed : ∀ i : Nat, (multiBase? (parameters.getD i missingParameter)).isNone →
      counts.getD i 0 = 0)
    {Γ : List String} (declarations : List (List String × String))
    (same : declarations = slots parameters counts)
    (arguments : Args (signature language) declarations Γ) :
    counts =
      observableCounts parameters (patternsOfDecl parameters counts declarations arguments) := by
  match arguments with
  | .nil =>
      match parameters, counts with
      | [], [] => simp [observableCounts]
      | [], _ :: _ => simp at aligned
      | _ :: _, [] => simp at aligned
      | _ :: _, _ :: _ => simp [slots] at same
  | .cons (as := tailDeclarations) head tail =>
      match parameters, counts with
      | [], _ => simp [slots] at same
      | _ :: _, [] => simp [slots] at same
      | parameter :: parameters, count :: counts =>
          have canonical : (multiBase? parameter).isNone → count = 0 := by
            intro notMulti
            have counted := fixed 0 (by simpa [List.getD, missingParameter] using notMulti)
            simpa [List.getD] using counted
          have tailFixed : ∀ i : Nat,
              (multiBase? (parameters.getD i missingParameter)).isNone →
                counts.getD i 0 = 0 := by
            intro index premise
            have counted := fixed (index + 1) (by simpa [List.getD] using premise)
            simpa [List.getD] using counted
          have tailEq : tailDeclarations = slots parameters counts :=
            (by simpa [slots, List.cons.injEq] using same :
              _ ∧ tailDeclarations = slots parameters counts).2
          have tailAligned : counts.length = parameters.length := by
            simp only [List.length_cons] at aligned
            omega
          have tailEquation :=
            patternsOfDecl_observable parameters counts tailAligned tailFixed tailDeclarations
              tailEq tail
          rw [patternsOfDecl_cons]
          simp only [observableCounts]
          rw [observableCount_print parameter count (toPattern head) canonical, ← tailEquation]
termination_by argsSize arguments
decreasing_by all_goals (dsimp only [termSize, argsSize]; omega)

/-! ## Distinct labels: printing is injective -/

/-- Injectivity of printing, by induction on a size bound. -/
theorem printInj (labels : (language.terms.map (·.label)).Nodup) (n : Nat) :
    (∀ {Γ : List String} {sort : String} (left right : Term (signature language) Γ sort),
        termSize left < n → toPattern left = toPattern right → left = right) ∧
    (∀ (parameters : List TermParam) (counts : List Nat)
        (aligned : counts.length = parameters.length)
        {Γ : List String} {declarations : List (List String × String)}
        (same : declarations = slots parameters counts)
        (left right : Args (signature language) declarations Γ),
        argsSize left < n →
          patternsOfDecl parameters counts declarations left =
            patternsOfDecl parameters counts declarations right →
          left = right) := by
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro Γ sort left right small _printed
        exact absurd small (Nat.not_lt_zero _)
      · intro parameters counts _aligned Γ declarations _same left right small _printed
        exact absurd small (Nat.not_lt_zero _)
  | succ n inductionHypothesis =>
      obtain ⟨termSmall, argsSmall⟩ := inductionHypothesis
      refine ⟨?_, ?_⟩
      · intro Γ sort left right small printed
        match left, right with
        | .var leftVar, .var rightVar =>
            simp only [toPattern, Pattern.bvar.injEq] at printed
            exact congrArg Term.var (varIndex_injective leftVar rightVar printed)
        | .var _, .op _ _ =>
            simp only [toPattern] at printed
            cases printed
        | .op _ _, .var _ =>
            simp only [toPattern] at printed
            cases printed
        | .op leftOperator leftArguments, .op rightOperator rightArguments =>
            have argumentsSmall : argsSize leftArguments < n := by
              have : argsSize leftArguments + 1 < n + 1 := by simpa [termSize] using small
              omega
            simp only [toPattern, Pattern.apply.injEq] at printed
            obtain ⟨sameLabel, sameArguments⟩ := printed
            rcases leftOperator with ⟨leftPacked, leftOccurrence⟩
            rcases rightOperator with ⟨rightPacked, rightOccurrence⟩
            have sameRule : leftPacked.1 = rightPacked.1 :=
              List.inj_on_of_nodup_map labels leftPacked.2.1 rightPacked.2.1 sameLabel
            have samePacked : leftPacked = rightPacked := Subtype.ext sameRule
            subst samePacked
            have leftCounts := patternsOfDecl_observable _ _ leftOccurrence.length_eq
              leftOccurrence.fixed (slots _ _) rfl leftArguments
            have rightCounts := patternsOfDecl_observable _ _ rightOccurrence.length_eq
              rightOccurrence.fixed (slots _ _) rfl rightArguments
            have sameCounts : leftOccurrence.counts = rightOccurrence.counts := by
              rw [leftCounts, rightCounts, sameArguments]
            have occAligned := leftOccurrence.length_eq
            have sameOccurrence : leftOccurrence = rightOccurrence := Occurrence.ext sameCounts
            subst sameOccurrence
            have sameArgs :=
              argsSmall _ _ occAligned rfl leftArguments rightArguments argumentsSmall sameArguments
            subst sameArgs
            rfl
      · intro parameters counts aligned Γ declarations same left right small printed
        match left, right with
        | .nil, .nil => rfl
        | .cons (as := tailDeclarations) leftHead leftTail, .cons rightHead rightTail =>
            match parameters, counts with
            | [], _ => simp [slots] at same
            | _ :: _, [] => simp [slots] at same
            | parameter :: parameters, count :: counts =>
                simp only [patternsOfDecl] at printed
                simp only [List.cons.injEq] at printed
                obtain ⟨sameHead, sameTail⟩ := printed
                have headSmall : termSize leftHead < n := by
                  have : termSize leftHead + argsSize leftTail + 1 < n + 1 := by
                    simpa [argsSize] using small
                  omega
                have tailSmall : argsSize leftTail < n := by
                  have : termSize leftHead + argsSize leftTail + 1 < n + 1 := by
                    simpa [argsSize] using small
                  omega
                have heads :=
                  termSmall leftHead rightHead headSmall
                    (printArgument_injective parameter count sameHead)
                have tailSame : tailDeclarations = slots parameters counts :=
                  (by simpa [slots, List.cons.injEq] using same :
                    _ ∧ tailDeclarations = slots parameters counts).2
                have tails :=
                  argsSmall parameters counts
                    (by simp only [List.length_cons] at aligned; omega) tailSame leftTail rightTail
                    tailSmall sameTail
                subst heads
                subst tails
                rfl

theorem toPattern_injective (labels : (language.terms.map (·.label)).Nodup)
    {Γ : List String} {sort : String} (left right : Term (signature language) Γ sort)
    (printed : toPattern left = toPattern right) : left = right :=
  (printInj labels (termSize left + 1)).1 left right (Nat.lt_succ_self _) printed

theorem patternsOfDecl_injective (labels : (language.terms.map (·.label)).Nodup)
    (parameters : List TermParam) (counts : List Nat)
    (aligned : counts.length = parameters.length)
    {Γ : List String} {declarations : List (List String × String)}
    (same : declarations = slots parameters counts)
    (left right : Args (signature language) declarations Γ)
    (printed : patternsOfDecl parameters counts declarations left =
      patternsOfDecl parameters counts declarations right) :
    left = right :=
  (printInj labels (argsSize left + 1)).2 parameters counts aligned same left right
    (Nat.lt_succ_self _) printed

/-! ## The fragment reaches every typed object pattern at a base sort -/

theorem exists_args
    {bound : Nat}
    (recurse :
      ∀ {Γ : List String} {sort : String} (pattern : Pattern),
        sizeOf pattern < bound →
        HasType language FreeTypeContext.empty (typeContext Γ) pattern (.base sort) →
        isObjectPattern pattern = true →
        ∃ term : Term (signature language) Γ sort, toPattern term = pattern) :
    (parameters : List TermParam) →
    (allBound : ∀ parameter ∈ parameters, (bindingDecl? parameter).isSome) →
    {Γ : List String} →
    (argumentPatterns : List Pattern) →
    (typed : ArgumentsHaveTypes language FreeTypeContext.empty (typeContext Γ)
      argumentPatterns parameters) →
    (smaller : ∀ pattern ∈ argumentPatterns, sizeOf pattern < bound) →
    (objects : ∀ pattern ∈ argumentPatterns, isObjectPattern pattern = true) →
    ∃ occurrence : Occurrence parameters,
      ∃ arguments : Args (signature language) (slots parameters occurrence.counts) Γ,
        patternsOf parameters occurrence.counts arguments = argumentPatterns
  | [], _, _, _, typed, _, _ => by
      cases typed
      exact ⟨{ counts := [], length_eq := rfl, fixed := by intro _ _; simp [List.getD] },
        .nil, rfl⟩
  | parameter :: parameters, allBound, Γ, argumentPatterns, typed, smaller, objects => by
      have ok := allBound parameter (List.mem_cons_self)
      cases inFragment_of_isSome ok with
      | simple _ sort =>
          cases argumentPatterns with
          | nil => cases typed
          | cons argument argumentPatterns =>
              cases typed with
              | cons _ expectedType argumentTyped restTyped =>
                  simp only [parameterType?, Option.some.injEq] at expectedType
                  subst expectedType
                  obtain ⟨term, printed⟩ :=
                    recurse (Γ := Γ) (sort := sort) argument
                      (smaller argument (List.mem_cons_self)) argumentTyped
                      (objects argument (List.mem_cons_self))
                  obtain ⟨tail, rest, restPrinted⟩ :=
                    exists_args recurse parameters
                      (fun parameter member => allBound parameter (List.mem_cons_of_mem _ member))
                      argumentPatterns restTyped
                      (fun pattern member => smaller pattern (List.mem_cons_of_mem _ member))
                      (fun pattern member => objects pattern (List.mem_cons_of_mem _ member))
                  refine ⟨Occurrence.cons 0 (by intro; rfl) tail, .cons term rest, ?_⟩
                  unfold patternsOf
                  simp only [Occurrence.cons, slots, slotBinders, patternsOfDecl, printArgument,
                    wrapBinders, printed, restPrinted]
      | abstraction _ _ domain bodySort =>
          cases argumentPatterns with
          | nil => cases typed
          | cons argument argumentPatterns =>
              cases typed with
              | cons representation expectedType argumentTyped restTyped =>
                  simp only [parameterType?, Option.some.injEq] at expectedType
                  subst expectedType
                  obtain ⟨body, rfl⟩ :=
                    (matchesParameterRepresentation_abstractionNamed_iff _ _ _ argument).mp
                      representation
                  cases argumentTyped with
                  | lambda bodyTyped =>
                      have bodySmall : sizeOf body < bound := by
                        have argumentSmall := smaller _ (List.mem_cons_self)
                        simp only [Pattern.lambda.sizeOf_spec] at argumentSmall
                        omega
                      have bodyObject : isObjectPattern body = true := by
                        have object := objects _ (List.mem_cons_self)
                        simpa [isObjectPattern] using object
                      obtain ⟨term, printed⟩ :=
                        recurse (Γ := domain :: Γ) (sort := bodySort) body bodySmall bodyTyped
                          bodyObject
                      obtain ⟨tail, rest, restPrinted⟩ :=
                        exists_args recurse parameters
                          (fun parameter member =>
                            allBound parameter (List.mem_cons_of_mem _ member))
                          argumentPatterns restTyped
                          (fun pattern member => smaller pattern (List.mem_cons_of_mem _ member))
                          (fun pattern member => objects pattern (List.mem_cons_of_mem _ member))
                      refine ⟨Occurrence.cons 0 (by intro; rfl) tail, .cons term rest, ?_⟩
                      unfold patternsOf
                      simp only [Occurrence.cons, slots, slotBinders, patternsOfDecl,
                        printArgument, wrapBinders, printed, restPrinted]
      | shorthand _ _ sort =>
          cases argumentPatterns with
          | nil => cases typed
          | cons argument argumentPatterns =>
              cases typed with
              | cons representation expectedType argumentTyped restTyped =>
                  simp only [parameterType?, Option.some.injEq] at expectedType
                  subst expectedType
                  obtain ⟨body, rfl⟩ :=
                    (matchesParameterRepresentation_abstractionNamed_iff _ _ _ argument).mp
                      representation
                  cases argumentTyped with
                  | lambda bodyTyped =>
                      have bodySmall : sizeOf body < bound := by
                        have argumentSmall := smaller _ (List.mem_cons_self)
                        simp only [Pattern.lambda.sizeOf_spec] at argumentSmall
                        omega
                      have bodyObject : isObjectPattern body = true := by
                        have object := objects _ (List.mem_cons_self)
                        simpa [isObjectPattern] using object
                      obtain ⟨term, printed⟩ :=
                        recurse (Γ := sort :: Γ) (sort := sort) body bodySmall bodyTyped bodyObject
                      obtain ⟨tail, rest, restPrinted⟩ :=
                        exists_args recurse parameters
                          (fun parameter member =>
                            allBound parameter (List.mem_cons_of_mem _ member))
                          argumentPatterns restTyped
                          (fun pattern member => smaller pattern (List.mem_cons_of_mem _ member))
                          (fun pattern member => objects pattern (List.mem_cons_of_mem _ member))
                      refine ⟨Occurrence.cons 0 (by intro; rfl) tail, .cons term rest, ?_⟩
                      unfold patternsOf
                      simp only [Occurrence.cons, slots, slotBinders, patternsOfDecl,
                        printArgument, wrapBinders, printed, restPrinted]
      | multiShorthand _ _ sort =>
          cases argumentPatterns with
          | nil => cases typed
          | cons argument argumentPatterns =>
              cases typed with
              | cons representation expectedType argumentTyped restTyped =>
                  simp only [parameterType?, Option.some.injEq] at expectedType
                  subst expectedType
                  obtain ⟨arity, body, rfl⟩ :=
                    (matchesParameterRepresentation_multiAbstractionNamed_iff _ _ _ argument).mp
                      representation
                  cases argumentTyped with
                  | multiLambda bodyTyped =>
                      have bodySmall : sizeOf body < bound := by
                        have argumentSmall := smaller _ (List.mem_cons_self)
                        simp only [Pattern.multiLambda.sizeOf_spec] at argumentSmall
                        omega
                      have bodyObject : isObjectPattern body = true := by
                        have object := objects _ (List.mem_cons_self)
                        simpa [isObjectPattern] using object
                      have bodyTyped' :
                          HasType language FreeTypeContext.empty
                            (typeContext (List.replicate arity sort ++ Γ)) body (.base sort) := by
                        simpa [typeContext, List.map_append, List.map_replicate] using bodyTyped
                      obtain ⟨term, printed⟩ :=
                        recurse (Γ := List.replicate arity sort ++ Γ) (sort := sort) body
                          bodySmall bodyTyped' bodyObject
                      obtain ⟨tail, rest, restPrinted⟩ :=
                        exists_args recurse parameters
                          (fun parameter member =>
                            allBound parameter (List.mem_cons_of_mem _ member))
                          argumentPatterns restTyped
                          (fun pattern member => smaller pattern (List.mem_cons_of_mem _ member))
                          (fun pattern member => objects pattern (List.mem_cons_of_mem _ member))
                      refine ⟨Occurrence.cons arity (by
                          intro bad
                          cases bad) tail, .cons term rest, ?_⟩
                      unfold patternsOf
                      simp only [Occurrence.cons, slots, slotBinders, patternsOfDecl,
                        printArgument, printed, restPrinted]
      | multi _ _ domain bodySort =>
          cases argumentPatterns with
          | nil => cases typed
          | cons argument argumentPatterns =>
              cases typed with
              | cons representation expectedType argumentTyped restTyped =>
                  simp only [parameterType?, Option.some.injEq] at expectedType
                  subst expectedType
                  obtain ⟨arity, body, rfl⟩ :=
                    (matchesParameterRepresentation_multiAbstractionNamed_iff _ _ _ argument).mp
                      representation
                  cases argumentTyped with
                  | multiLambda bodyTyped =>
                      have bodySmall : sizeOf body < bound := by
                        have argumentSmall := smaller _ (List.mem_cons_self)
                        simp only [Pattern.multiLambda.sizeOf_spec] at argumentSmall
                        omega
                      have bodyObject : isObjectPattern body = true := by
                        have object := objects _ (List.mem_cons_self)
                        simpa [isObjectPattern] using object
                      have bodyTyped' :
                          HasType language FreeTypeContext.empty
                            (typeContext (List.replicate arity domain ++ Γ)) body
                            (.base bodySort) := by
                        simpa [typeContext, List.map_append, List.map_replicate] using bodyTyped
                      obtain ⟨term, printed⟩ :=
                        recurse (Γ := List.replicate arity domain ++ Γ) (sort := bodySort) body
                          bodySmall bodyTyped' bodyObject
                      obtain ⟨tail, rest, restPrinted⟩ :=
                        exists_args recurse parameters
                          (fun parameter member =>
                            allBound parameter (List.mem_cons_of_mem _ member))
                          argumentPatterns restTyped
                          (fun pattern member => smaller pattern (List.mem_cons_of_mem _ member))
                          (fun pattern member => objects pattern (List.mem_cons_of_mem _ member))
                      refine ⟨Occurrence.cons arity (by
                          intro bad
                          cases bad) tail, .cons term rest, ?_⟩
                      unfold patternsOf
                      simp only [Occurrence.cons, slots, slotBinders, patternsOfDecl,
                        printArgument, printed, restPrinted]

theorem exists_toPattern_of_size
    (fragment : ∀ rule ∈ language.terms, BinderRule rule) :
    (bound : Nat) → (Γ : List String) → (pattern : Pattern) → sizeOf pattern < bound →
      (sort : String) →
      HasType language FreeTypeContext.empty (typeContext Γ) pattern (.base sort) →
      isObjectPattern pattern = true →
      ∃ term : Term (signature language) Γ sort, toPattern term = pattern
  | 0, _, _, small, _, _, _ => absurd small (Nat.not_lt_zero _)
  | bound + 1, Γ, pattern, small, sort, typed, objects => by
      cases pattern with
      | bvar index =>
          cases typed with
          | bvar found =>
              obtain ⟨variable_, printed⟩ := exists_var_of_get (lookup_base found)
              exact ⟨.var variable_, by simp [toPattern, printed]⟩
      | fvar _ =>
          cases typed with
          | fvar found => simp [FreeTypeContext.empty] at found
      | apply _ arguments =>
          cases typed with
          | constructor member _notBare argumentsTyped =>
              rename_i rule
              have smaller : ∀ pattern ∈ arguments, sizeOf pattern < bound := by
                intro pattern memberPattern
                have := List.sizeOf_lt_of_mem memberPattern
                simp only [Pattern.apply.sizeOf_spec] at small
                omega
              have argumentObjects : ∀ pattern ∈ arguments, isObjectPattern pattern = true := by
                simpa [isObjectPattern, isObjectPatternList_eq_true_iff] using objects
              obtain ⟨occurrence, argumentsTerm, printed⟩ :=
                exists_args
                  (fun {Δ} {argumentSort} pattern smallPattern typedPattern objectPattern =>
                    exists_toPattern_of_size fragment bound Δ pattern smallPattern argumentSort
                      typedPattern objectPattern)
                  rule.params (fragment rule member) arguments argumentsTyped smaller
                  argumentObjects
              refine ⟨.op ⟨⟨rule, member, fragment rule member, ?_⟩, occurrence⟩ argumentsTerm, ?_⟩
              · rfl
              · simp [toPattern, printed]
      | lambda _ _ => cases typed
      | multiLambda _ _ _ => cases typed
      | subst _ _ => simp [isObjectPattern] at objects
      | collection collectionType _ _ =>
          obtain ⟨rule, member, _, parameterName, elementType, shape⟩ :=
            declared_collection_constructor_of_hasSort typed
          have ok := fragment rule member
            (.simple parameterName (.collection collectionType elementType))
            (by rw [shape]; exact List.mem_singleton_self _)
          simp [bindingDecl?] at ok

theorem exists_toPattern
    (fragment : ∀ rule ∈ language.terms, BinderRule rule)
    {Γ : List String} (pattern : Pattern) (sort : String)
    (typed : HasType language FreeTypeContext.empty (typeContext Γ) pattern (.base sort))
    (objects : isObjectPattern pattern = true) :
    ∃ term : Term (signature language) Γ sort, toPattern term = pattern :=
  exists_toPattern_of_size fragment (sizeOf pattern + 1) Γ pattern (Nat.lt_succ_self _)
    sort typed objects

/-- In a language whose constructors lie in the binder fragment and whose labels
are distinct, the closed object patterns typed at a base sort are the closed
binding terms of that fragment. -/
noncomputable def closedPatternEquiv
    (fragment : ∀ rule ∈ language.terms, BinderRule rule)
    (labels : (language.terms.map (·.label)).Nodup) (sort : String) :
    Term (signature language) [] sort ≃
      {pattern : Pattern //
        HasType language FreeTypeContext.empty [] pattern (.base sort) ∧
          isObjectPattern pattern = true} :=
  Equiv.ofBijective
    (fun term => ⟨toPattern term, toPattern_hasType term, toPattern_isObjectPattern term⟩)
    ⟨fun left right same =>
        toPattern_injective labels left right (congrArg Subtype.val same),
      fun pattern => by
        obtain ⟨term, printed⟩ :=
          exists_toPattern (Γ := []) fragment pattern.1 sort pattern.2.1 pattern.2.2
        exact ⟨term, Subtype.ext printed⟩⟩

/-- Those patterns are the free-monad trees of the fragment's polynomial at the
empty context, with variables as leaves. The head of a tree is an operator
together with the multi-binder counts of that occurrence. -/
noncomputable def closedPatternFreeEquiv
    (fragment : ∀ rule ∈ language.terms, BinderRule rule)
    (labels : (language.terms.map (·.label)).Nodup) (sort : String) :
    {pattern : Pattern //
        HasType language FreeTypeContext.empty [] pattern (.base sort) ∧
          isObjectPattern pattern = true} ≃
      IFreeM (polynomial (signature language)) (Vars (signature language)) ([], sort) :=
  (closedPatternEquiv fragment labels sort).symm.trans
    (termEquiv (signature language) [] sort)

end Mettapedia.GSLT.Poly.BindingLanguage
