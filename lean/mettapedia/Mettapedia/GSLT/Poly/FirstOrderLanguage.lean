import Mettapedia.GSLT.Poly.SortedSignature
import Mettapedia.GSLT.LanguageDef.WellSorted

/-!
# The first-order constructors of a language as an indexed polynomial

The constructors of a `LanguageDef` whose parameters are all ordinary arguments at
base sorts form a sorted signature, and so a PolyFun indexed polynomial. A closed
term of that signature prints as an `apply` pattern, which the language's own sort
judgment `HasType` types at the term's sort.

When the language's labels are distinct, printing is injective. When moreover every
constructor of the language is first order, printing reaches every closed object
pattern that `HasType` types at a base sort. Those patterns are therefore exactly
the closed terms of the signature, and, by `SortedSignature.closedTermEquiv`, exactly
the free-monad trees of its polynomial without variables.

Binding parameters, collection parameters and explicit substitutions are outside
this fragment: a binder argument is a `lambda` node typed at an arrow type, and a
collection argument is not a constructor tree.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.FirstOrderLanguage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.SortedConstructors

/-- The base sort of an ordinary parameter, if it has one. -/
def baseSort? : TermParam → Option String
  | .simple _ (.base sort) => some sort
  | _ => none

theorem eq_simple_of_baseSort? {parameter : TermParam} {sort : String}
    (found : baseSort? parameter = some sort) :
    ∃ name, parameter = .simple name (.base sort) := by
  match parameter, found with
  | .simple name (.base _), rfl => exact ⟨name, rfl⟩

/-- Every parameter of the rule is an ordinary argument at a base sort. -/
def FirstOrderRule (rule : GrammarRule) : Prop :=
  ∀ parameter ∈ rule.params, (baseSort? parameter).isSome

/-- The first-order constructors of a language. -/
abbrev FirstOrderConstructor (language : LanguageDef) :=
  {rule : GrammarRule // rule ∈ language.terms ∧ FirstOrderRule rule}

/-- The sorted signature of a language's first-order constructors. -/
abbrev signature (language : LanguageDef) : Signature.{0, 0} where
  Srt := String
  Constructor := FirstOrderConstructor language
  arity rule := rule.1.params.length
  input rule position :=
    (baseSort? (rule.1.params.get position)).get (rule.2.2 _ (List.get_mem _ _))
  output rule := rule.1.category

theorem baseSort?_input {language : LanguageDef} (rule : FirstOrderConstructor language)
    (position : Fin rule.1.params.length) :
    baseSort? (rule.1.params.get position) = some ((signature language).input rule position) :=
  (Option.some_get _).symm

theorem not_usesBareCollection {rule : GrammarRule} (firstOrder : FirstOrderRule rule) :
    ¬ UsesBareCollection rule := by
  rintro ⟨name, collectionType, elementType, shape⟩
  have shape := (GrammarRule.bareParams_cons_iff _ _ _).mp shape |>.2
  have isBase := firstOrder (.simple name (.collection collectionType elementType)) (by simp [shape])
  simp [baseSort?] at isBase

variable {language : LanguageDef}

/-- A closed term of the first-order signature as an `apply` pattern. -/
def toPattern : {sort : String} → Term (signature language) sort → Pattern
  | _, .node rule arguments =>
      .apply rule.1.label (List.ofFn fun position => toPattern (arguments position))

/-! ## Printed terms are typed by the language's own judgment -/

theorem argumentsHaveTypes_ofFn {free : FreeTypeContext} {bound : List TypeExpr} :
    (parameters : List TermParam) → (arguments : Fin parameters.length → Pattern) →
    (∀ position, ∃ sort, baseSort? (parameters.get position) = some sort ∧
        HasType language free bound (arguments position) (.base sort)) →
    ArgumentsHaveTypes language free bound (List.ofFn arguments) parameters
  | [], _, _ => by
      simpa using ArgumentsHaveTypes.nil (language := language) (free := free) (bound := bound)
  | parameter :: parameters, arguments, typed => by
      rw [List.ofFn_succ]
      obtain ⟨sort, found, argumentTyped⟩ := typed 0
      obtain ⟨name, rfl⟩ := eq_simple_of_baseSort? found
      exact ArgumentsHaveTypes.cons trivial rfl argumentTyped
        (argumentsHaveTypes_ofFn parameters (fun position => arguments position.succ)
          (fun position => typed position.succ))

theorem toPattern_hasType {free : FreeTypeContext} {bound : List TypeExpr} :
    {sort : String} → (term : Term (signature language) sort) →
      HasType language free bound (toPattern term) (.base sort)
  | _, .node rule arguments => by
      simp only [toPattern]
      exact HasType.constructor rule.2.1 (not_usesBareCollection rule.2.2)
        (argumentsHaveTypes_ofFn rule.1.params _ fun position =>
          ⟨_, baseSort?_input rule position, toPattern_hasType (arguments position)⟩)

theorem isObjectPatternList_eq_true_iff :
    (patterns : List Pattern) →
      isObjectPatternList patterns = true ↔ ∀ pattern ∈ patterns, isObjectPattern pattern = true
  | [] => by simp [isObjectPatternList]
  | pattern :: patterns => by
      simp [isObjectPatternList, isObjectPatternList_eq_true_iff patterns]

theorem toPattern_isObjectPattern :
    {sort : String} → (term : Term (signature language) sort) →
      isObjectPattern (toPattern term) = true
  | _, .node _ arguments => by
      simp only [toPattern, isObjectPattern]
      rw [isObjectPatternList_eq_true_iff]
      intro pattern member
      obtain ⟨position, rfl⟩ := List.mem_ofFn.mp member
      exact toPattern_isObjectPattern (arguments position)

/-! ## Distinct labels: printing is injective -/

theorem toPattern_sigma_injective (labels : (language.terms.map (·.label)).Nodup) :
    {first second : String} → (left : Term (signature language) first) →
      (right : Term (signature language) second) → toPattern left = toPattern right →
      (⟨first, left⟩ : Σ sort, Term (signature language) sort) = ⟨second, right⟩
  | _, _, .node leftRule leftArguments, .node rightRule rightArguments, printed => by
      simp only [toPattern, Pattern.apply.injEq] at printed
      obtain ⟨sameLabel, sameArguments⟩ := printed
      have sameRule : leftRule = rightRule :=
        Subtype.ext (List.inj_on_of_nodup_map labels leftRule.2.1 rightRule.2.1 sameLabel)
      subst sameRule
      have samePrinted := List.ofFn_injective sameArguments
      have same : leftArguments = rightArguments := funext fun position => by
        have recursive := toPattern_sigma_injective labels (leftArguments position)
          (rightArguments position) (congrFun samePrinted position)
        exact eq_of_heq (Sigma.mk.inj recursive).2
      subst same
      rfl

theorem toPattern_injective (labels : (language.terms.map (·.label)).Nodup) (sort : String) :
    Function.Injective (toPattern (language := language) (sort := sort)) := by
  intro left right printed
  exact eq_of_heq (Sigma.mk.inj (toPattern_sigma_injective labels left right printed)).2

/-! ## First-order languages: printing reaches every typed closed object pattern -/

theorem argumentsHaveTypes_get {free : FreeTypeContext} {bound : List TypeExpr} :
    (arguments : List Pattern) → (parameters : List TermParam) →
    ArgumentsHaveTypes language free bound arguments parameters →
    (∀ parameter ∈ parameters, (baseSort? parameter).isSome) →
    ∀ (position : Nat) (inArguments : position < arguments.length)
      (inParameters : position < parameters.length) (sort : String),
      baseSort? (parameters.get ⟨position, inParameters⟩) = some sort →
      HasType language free bound (arguments.get ⟨position, inArguments⟩) (.base sort)
  | [], _, _, _, _, inArguments, _, _, _ => absurd inArguments (Nat.not_lt_zero _)
  | _ :: _, [], _, _, _, _, inParameters, _, _ => absurd inParameters (Nat.not_lt_zero _)
  | argument :: arguments, parameter :: parameters, typed, firstOrder, position,
      inArguments, inParameters, sort, found => by
      obtain ⟨parameterSort, parameterFound⟩ :=
        Option.isSome_iff_exists.mp (firstOrder parameter (List.mem_cons_self ..))
      obtain ⟨name, rfl⟩ := eq_simple_of_baseSort? parameterFound
      obtain ⟨argumentTyped, argumentsTyped⟩ := ArgumentsHaveTypes.simple_cons_inv typed
      cases position with
      | zero =>
          simp only [List.get_eq_getElem, List.getElem_cons_zero, baseSort?,
            Option.some.injEq] at found
          subst found
          exact argumentTyped
      | succ position =>
          exact argumentsHaveTypes_get arguments parameters argumentsTyped
            (fun other member => firstOrder other (List.mem_cons_of_mem _ member)) position
            (Nat.lt_of_succ_lt_succ inArguments) (Nat.lt_of_succ_lt_succ inParameters) sort found

theorem exists_toPattern_of_size (firstOrder : ∀ rule ∈ language.terms, FirstOrderRule rule) :
    (bound : Nat) → (pattern : Pattern) → sizeOf pattern < bound → (sort : String) →
    HasType language FreeTypeContext.empty [] pattern (.base sort) →
    isObjectPattern pattern = true →
    ∃ term : Term (signature language) sort, toPattern term = pattern
  | 0, _, small, _, _, _ => absurd small (Nat.not_lt_zero _)
  | bound + 1, pattern, small, sort, typed, objects => by
      cases pattern with
      | bvar _ =>
          cases typed with
          | bvar found => simp at found
      | fvar _ =>
          cases typed with
          | fvar found => simp [FreeTypeContext.empty] at found
      | apply label arguments =>
          cases typed with
          | constructor member notBare argumentsTyped =>
              rename_i rule
              have ruleFirstOrder := firstOrder rule member
              have lengths := argumentsTyped.length_eq
              have inArguments : ∀ position : Fin rule.params.length,
                  position.1 < arguments.length :=
                fun position => by rw [lengths]; exact position.2
              have argumentObjects : ∀ argument ∈ arguments, isObjectPattern argument = true := by
                simpa [isObjectPattern, isObjectPatternList_eq_true_iff] using objects
              let constructor : (signature language).Constructor := ⟨rule, member, ruleFirstOrder⟩
              have children : ∀ position : Fin rule.params.length,
                  ∃ child : Term (signature language)
                      ((signature language).input constructor position),
                    toPattern child = arguments.get ⟨position.1, inArguments position⟩ := by
                intro position
                have size : sizeOf (arguments.get ⟨position.1, inArguments position⟩) < bound := by
                  have := List.sizeOf_lt_of_mem
                    (List.get_mem arguments ⟨position.1, inArguments position⟩)
                  simp only [Pattern.apply.sizeOf_spec] at small
                  omega
                exact exists_toPattern_of_size firstOrder bound _ size _
                  (argumentsHaveTypes_get arguments rule.params argumentsTyped ruleFirstOrder
                    position.1 (inArguments position) position.2 _
                    (baseSort?_input constructor position))
                  (argumentObjects _ (List.get_mem _ _))
              choose child printed using children
              refine ⟨@Term.node (signature language) constructor child, ?_⟩
              simp only [toPattern]
              congr 1
              apply List.ext_get
              · simp [constructor, lengths]
              · intro position inOfFn inGiven
                simp only [List.get_eq_getElem, List.getElem_ofFn]
                have := printed ⟨position, by simpa [constructor] using inOfFn⟩
                simpa [List.get_eq_getElem] using this
      | lambda _ _ => cases typed
      | multiLambda _ _ _ => cases typed
      | subst _ _ => simp [isObjectPattern] at objects
      | collection _ _ _ =>
          cases typed with
          | collectionConstructor member shape _ =>
              rename_i rule _ _ _
              have shape := (GrammarRule.bareParams_cons_iff _ _ _).mp shape |>.2
              have isBase := firstOrder rule member _ (by rw [shape]; exact List.mem_singleton_self _)
              simp [baseSort?] at isBase

theorem exists_toPattern (firstOrder : ∀ rule ∈ language.terms, FirstOrderRule rule)
    (pattern : Pattern) (sort : String)
    (typed : HasType language FreeTypeContext.empty [] pattern (.base sort))
    (objects : isObjectPattern pattern = true) :
    ∃ term : Term (signature language) sort, toPattern term = pattern :=
  exists_toPattern_of_size firstOrder (sizeOf pattern + 1) pattern (Nat.lt_succ_self _) sort
    typed objects

/-- In a first-order language with distinct labels, the closed object patterns that
the language types at a base sort are exactly the closed terms of its first-order
signature. -/
noncomputable def closedPatternEquiv (firstOrder : ∀ rule ∈ language.terms, FirstOrderRule rule)
    (labels : (language.terms.map (·.label)).Nodup) (sort : String) :
    Term (signature language) sort ≃
      {pattern : Pattern // HasType language FreeTypeContext.empty [] pattern (.base sort) ∧
        isObjectPattern pattern = true} :=
  Equiv.ofBijective
    (fun term => ⟨toPattern term, toPattern_hasType term, toPattern_isObjectPattern term⟩)
    ⟨fun left right same => toPattern_injective labels sort (congrArg Subtype.val same),
      fun pattern => by
        obtain ⟨term, printed⟩ := exists_toPattern firstOrder pattern.1 sort pattern.2.1 pattern.2.2
        exact ⟨term, Subtype.ext printed⟩⟩

/-- The same patterns are the free-monad trees of the signature's polynomial
without variables. -/
noncomputable def closedPatternFreeEquiv
    (firstOrder : ∀ rule ∈ language.terms, FirstOrderRule rule)
    (labels : (language.terms.map (·.label)).Nodup) (sort : String) :
    {pattern : Pattern // HasType language FreeTypeContext.empty [] pattern (.base sort) ∧
        isObjectPattern pattern = true} ≃
      SortedSignature.ClosedFree (signature language) sort :=
  (closedPatternEquiv firstOrder labels sort).symm.trans
    (SortedSignature.closedTermEquiv (signature language) sort)

end Mettapedia.GSLT.Poly.FirstOrderLanguage
