import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ContextLabels
import Mettapedia.GSLT.Logic.BagSaturated

/-!
# Token nets at the front door are parallel reactive systems

A **token net** is a language whose terms are bags of tokens, constants of one sort collected by a declared bag
former, and whose rules consume some tokens beside a rest and produce others beside it, with no premises, equations
or collection algebra (`TokenNet`): Petri nets, written as languages.

- **Markings are equivalent exactly when they are permutations** (`objectEquivalent_iff`), and a term equivalent to a
  marking is a marking (`shape_of_objectEquivalent`).
- **The front door's steps of a marking are the net's reactions in the parallel context category** (`step_iff`): the
  marking `xs` steps to a term exactly when, for some rule `l ⟶ k`, `l ≤ xs` and the term is equivalent to the marking
  `k + (xs - l)`; that is `Reacts` for the reaction rules of the net (`reactions`) in `BagRelativePushout`'s category.
- **A marking's steps beside tokens are its reactions in that context** (`contextStep_iff`): the context
  `{c₁, …, cₙ, ...x}` is the arrow `cs` of the parallel context category, and the marking placed in it reacts as the
  composite.
- **Least labels are context steps** (`step_of_actIPO`): the least label of a marking for a rule is what it lacks of the
  rule's consumed tokens (`actIPO_iff`), and the marking steps beside it. So saturated bisimilarity of markings,
  against every environment, is semi-saturated (`BagSaturated`), and its least labels are the front door's context
  labels.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.TokenNets

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (canon canon_collection canon_apply arrange arrange_bag perm_of_sortLex_eq)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff)
open Mettapedia.GSLT.RedexRelativeCongruence (ReactionRule)
open Mettapedia.GSLT.BagRelativePushout (Obj bag bag_injective)
open Mettapedia.GSLT.SemiSaturated (Reacts)
open Mettapedia.GSLT.RedexRelativeCongruence (ActIPO)

/-! ## Tokens and markings -/

/-- A token: a constant. -/
def token (name : String) : Pattern := .apply name []

/-- The marking of a list of tokens. -/
def marking (names : List String) : Pattern := .collection .hashBag (names.map token) none

theorem token_injective : Function.Injective token := fun _ _ same => by
  simp only [token, Pattern.apply.injEq] at same
  exact same.1

/-- **A rule of a token net**: consume tokens beside a rest, produce tokens beside it. -/
structure NetRule where
  consumed : List String
  produced : List String
  rest : String

/-- A rewrite rule presents a net rule. -/
def NetRule.Presents (net : NetRule) (rule : RewriteRule) : Prop :=
  rule.premises = [] ∧ rule.left = .collection .hashBag (net.consumed.map token) (some net.rest) ∧
    rule.right = .collection .hashBag (net.produced.map token) (some net.rest)

/-- **A token net**: no equations or collection algebra, a declared bag former of a sort, tokens of that sort, and
rules that consume and produce tokens beside a rest. -/
structure TokenNet (language : LanguageDef) where
  noEquations : language.equations = []
  noAlgebra : language.hasAlgebraDeclarations = false
  former : GrammarRule
  formerDeclared : former ∈ language.terms
  sort : String
  parameter : String
  formerParameter : TermParam.simple parameter (.collection .hashBag (.base sort)) ∈ former.params
  tokens : List String
  typed : ∀ name ∈ tokens, HasType language FreeTypeContext.empty [] (token name) (.base sort)
  rules : ∀ rule ∈ language.rewrites, ∃ net : NetRule, net.Presents rule ∧ (∀ name ∈ net.consumed, name ∈ tokens) ∧
    ∀ name ∈ net.produced, name ∈ tokens

variable {language : LanguageDef} (net : TokenNet language) {relEnv : RelationEnv}

/-- Markings of the net's tokens. -/
def Region (names : List String) : Prop := ∀ name ∈ names, name ∈ net.tokens

/-! ## Equivalence of markings -/

theorem isObjectPatternList_tokens : ∀ names : List String, isObjectPatternList (names.map token) = true
  | [] => rfl
  | _ :: names => by
    simp only [List.map_cons, isObjectPatternList, token, isObjectPattern, Bool.true_and]
    exact isObjectPatternList_tokens names

theorem isWellScopedListAt_tokens : ∀ names : List String, Pattern.isWellScopedListAt 0 (names.map token) = true
  | [] => rfl
  | _ :: names => by
    simp only [List.map_cons, Pattern.isWellScopedListAt, token, Pattern.isWellScopedAt, Bool.true_and]
    exact isWellScopedListAt_tokens names

theorem state_marking (names : List String) : IsState (marking names) :=
  ⟨by simp [marking, Pattern.isWellScopedAt, isWellScopedListAt_tokens],
    by simp [marking, IsObject, isObjectPattern, isObjectPatternList_tokens]⟩

include net in
theorem collectionTyped {names : List String} (region : Region net names) :
    CollectionTypedAt language net.former .hashBag (names.map token) :=
  ⟨_, net.formerParameter, .base net.sort, .here, FreeTypeContext.empty, [],
    HasType.collection (elementsHaveType_iff.mpr fun item member => by
      obtain ⟨name, found, rfl⟩ := List.mem_map.mp member
      exact net.typed name (region name found))⟩

/-- **A permutation of a marking is an equation.** -/
theorem objectEquivalent_of_perm {names others : List String} (region : Region net names) (perm : names.Perm others) :
    ObjectEquivalent relEnv language .syntax (marking names) (marking others) := by
  have generator : Generator relEnv language (marking names) (marking others) :=
    Or.inr (DerivedInstance.bagPerm net.formerDeclared (collectionTyped net region) (perm.map token))
  exact Relation.EqvGen.rel _ _ ⟨(state_marking names).2, (state_marking others).2,
    EquationStep.inContext .hole generator⟩

theorem canon_token (name : String) : canon (token name) = token name := by
  rw [token, canon_apply]
  rfl

theorem canon_tokens (names : List String) : (names.map token).map canon = names.map token := by
  simp only [List.map_map, Function.comp_def, canon_token]

/-- A pattern whose canonical form is a token is that token. -/
theorem eq_token_of_canon {pattern : Pattern} {name : String} (same : canon pattern = token name) :
    pattern = token name := by
  cases pattern with
  | apply label arguments =>
    rw [canon_apply, token, Pattern.apply.injEq] at same
    obtain ⟨rfl, empty⟩ := same
    rw [List.map_eq_nil_iff] at empty
    rw [empty]
    rfl
  | bvar _ => rw [canon] at same; cases same
  | fvar _ => rw [canon] at same; cases same
  | lambda _ _ => rw [canon] at same; cases same
  | multiLambda _ _ _ => rw [canon] at same; cases same
  | subst _ _ => rw [canon] at same; cases same
  | collection kind elements rest => rw [canon_collection] at same; cases same

/-- Patterns whose canonical forms are tokens are those tokens. -/
theorem eq_tokens_of_canon : ∀ {patterns : List Pattern} {names : List String},
    patterns.map canon = names.map token → patterns = names.map token
  | [], [], _ => rfl
  | [], _ :: _, same => by simp at same
  | _ :: _, [], same => by simp at same
  | pattern :: patterns, name :: names, same => by
    simp only [List.map_cons, List.cons.injEq] at same
    rw [eq_token_of_canon same.1, eq_tokens_of_canon same.2]
    rfl

/-- The name of a token. -/
def nameOf : Pattern → String
  | .apply label _ => label
  | _ => ""

/-- A list of tokens is the tokens of its names. -/
theorem eq_map_nameOf {patterns : List Pattern} (tokens : ∀ pattern ∈ patterns, ∃ name, pattern = token name) :
    patterns = (patterns.map nameOf).map token := by
  rw [List.map_map]
  conv => lhs; rw [← List.map_id patterns]
  exact List.map_congr_left fun pattern member => by
    obtain ⟨name, rfl⟩ := tokens pattern member
    rfl

/-- The names of tokens in a list whose canonical forms permute a marking's. -/
theorem tokens_of_perm {patterns : List Pattern} {names : List String} (perm : (patterns.map canon).Perm (names.map token)) :
    ∃ others : List String, patterns = others.map token ∧ names.Perm others := by
  have back : patterns = (patterns.map nameOf).map token := eq_map_nameOf fun pattern member => by
    obtain ⟨name, -, same⟩ := List.mem_map.mp (perm.subset (List.mem_map_of_mem member))
    exact ⟨name, eq_token_of_canon same.symm⟩
  refine ⟨patterns.map nameOf, back, ?_⟩
  have canonical : patterns.map canon = patterns := by
    rw [back, canon_tokens]
  rw [canonical, back] at perm
  exact ((List.map_perm_map_iff token_injective).mp perm).symm

/-- A pattern whose canonical form is a collection is a collection of the same kind and rest. -/
theorem eq_collection_of_canon {pattern : Pattern} {kind : CollType} {elements : List Pattern}
    {rest : Option String} (same : canon pattern = .collection kind elements rest) :
    ∃ members, pattern = .collection kind members rest ∧ arrange kind (members.map canon) = elements := by
  cases pattern with
  | collection kind' members rest' =>
    rw [canon_collection, Pattern.collection.injEq] at same
    obtain ⟨rfl, arranged, rfl⟩ := same
    exact ⟨members, rfl, arranged⟩
  | apply _ _ => rw [canon_apply] at same; cases same
  | bvar _ => rw [canon] at same; cases same
  | fvar _ => rw [canon] at same; cases same
  | lambda _ _ => rw [canon] at same; cases same
  | multiLambda _ _ _ => rw [canon] at same; cases same
  | subst _ _ => rw [canon] at same; cases same

include net in
/-- **A term equivalent to a marking is a marking**, of a permutation of its tokens. -/
theorem shape_of_objectEquivalent {names : List String} {term : Pattern}
    (equivalent : ObjectEquivalent relEnv language .syntax (marking names) term) :
    ∃ others : List String, term = marking others ∧ names.Perm others := by
  have same := BagForms.canon_eq_of_equivalent net.noEquations net.noAlgebra equivalent
  rw [marking, canon_collection, arrange_bag, canon_tokens] at same
  obtain ⟨elements, rfl, sorted⟩ := eq_collection_of_canon same.symm
  rw [arrange_bag] at sorted
  obtain ⟨others, rfl, perm⟩ := tokens_of_perm (perm_of_sortLex_eq sorted)
  exact ⟨others, rfl, perm⟩

theorem marking_injective : Function.Injective marking := fun first second same => by
  simp only [marking, Pattern.collection.injEq, true_and, and_true] at same
  exact (List.map_injective_iff.mpr token_injective) same

/-- **Markings are equivalent exactly when they are permutations.** -/
theorem objectEquivalent_iff {names others : List String} (region : Region net names) :
    ObjectEquivalent relEnv language .syntax (marking names) (marking others) ↔ names.Perm others := by
  constructor
  · intro equivalent
    obtain ⟨found, same, perm⟩ := shape_of_objectEquivalent net equivalent
    rw [marking_injective same]
    exact perm
  · exact objectEquivalent_of_perm net region

/-! ## Matching a rule against a marking -/

theorem matchRel_token {name : String} {term : Pattern} {bindings : Bindings}
    (matched : MatchRel (token name) term bindings) : term = token name ∧ bindings = [] := by
  unfold token at matched
  cases matched with
  | apply arguments _ =>
    cases arguments
    exact ⟨rfl, rfl⟩

theorem matchRel_token_self (name : String) : MatchRel (token name) (token name) [] :=
  .apply .nil rfl

theorem mergeBindings_single (name : String) (value : Pattern) :
    mergeBindings [] [(name, value)] = some [(name, value)] := rfl

/-- **A rule's tokens match a bag** only where the bag permutes them beside a remainder, which the rest captures. -/
theorem matchBag_tokens {rest : String} : ∀ {names : List String} {terms : List Pattern} {bindings : Bindings},
    MatchBagRel (names.map token) (some rest) .hashBag terms bindings →
      ∃ remainder, (names.map token ++ remainder).Perm terms ∧
        bindings = [(rest, .collection .hashBag remainder none)]
  | [], terms, bindings, matched => by
    rw [List.map_nil] at matched
    cases matched
    exact ⟨terms, .refl _, rfl⟩
  | name :: names, terms, bindings, matched => by
    rw [List.map_cons] at matched
    cases matched with
    | cons index bound head tail merged =>
      obtain ⟨found, rfl⟩ := matchRel_token head
      obtain ⟨remainder, perm, rfl⟩ := matchBag_tokens tail
      refine ⟨remainder, ?_, ?_⟩
      · rw [List.map_cons, List.cons_append, ← found]
        exact (perm.cons _).trans (List.getElem_cons_eraseIdx_perm bound)
      · rw [mergeBindings_single] at merged
        exact (Option.some.inj merged).symm

/-- **A rule's tokens match a bag that begins with them**, the rest capturing the remainder. -/
theorem matchBag_prefix (rest : String) (remainder : List Pattern) : ∀ names : List String,
    MatchBagRel (names.map token) (some rest) .hashBag (names.map token ++ remainder)
      [(rest, .collection .hashBag remainder none)]
  | [] => .nilRest
  | name :: names => by
    rw [List.map_cons]
    exact .cons 0 (by simp) (matchRel_token_self name) (matchBag_prefix rest remainder names) rfl

/-! ## The right side of a rule -/

theorem liftBVars_token (cutoff shift : ℕ) (name : String) :
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars cutoff shift (token name) = token name := rfl

theorem applyBindingsScoped_token (sites : Pattern) (bindings : Bindings) (depth : ℕ) (name : String) :
    applyBindingsScoped sites bindings depth (token name) = token name := by
  rw [token, applyBindingsScoped_apply]
  rfl

/-- The rest of a rule, bound to a remainder of tokens, splices the remainder. -/
theorem restSplice_tokens (sites : Pattern) (rest : String) (remainder : List String) (depth : ℕ) :
    restSplice sites [(rest, .collection .hashBag (remainder.map token) none)] depth .hashBag (some rest) =
      (remainder.map token, none) := by
  simp only [restSplice, List.find?_cons, beq_self_eq_true, ↓reduceIte]
  split <;> simp [List.map_map, Function.comp_def, liftBVars_token]

/-- **A rule's right side, with the rest bound to a remainder of tokens, is the marking of its produced tokens and the
remainder.** -/
theorem contractum_eq {rule : RewriteRule} {netRule : NetRule} (presents : netRule.Presents rule)
    (remainder : List String) :
    applyBindingsScoped (captureSites rule) [(netRule.rest, .collection .hashBag (remainder.map token) none)] 0
      rule.right = marking (netRule.produced ++ remainder) := by
  rw [presents.2.2, applyBindingsScoped, applyBindingsScopedList_eq_map, restSplice_tokens, marking,
    List.map_append, List.map_map]
  simp only [Function.comp_def, applyBindingsScoped_token]

/-! ## Steps are reactions -/

/-- The rule a rewrite rule presents is unique. -/
theorem NetRule.Presents.unique {first second : NetRule} {rule : RewriteRule} (one : first.Presents rule)
    (other : second.Presents rule) : first = second := by
  obtain ⟨-, firstLeft, firstRight⟩ := one
  obtain ⟨-, secondLeft, secondRight⟩ := other
  rw [firstLeft, Pattern.collection.injEq] at secondLeft
  rw [firstRight, Pattern.collection.injEq] at secondRight
  obtain ⟨-, consumed, rest⟩ := secondLeft
  obtain ⟨-, produced, -⟩ := secondRight
  have injective := List.map_injective_iff.mpr token_injective
  cases first
  cases second
  simp only [Option.some.injEq] at rest
  simp only [NetRule.mk.injEq]
  exact ⟨injective consumed, injective produced, rest⟩

/-- A rule of the net produces the net's tokens. -/
theorem produced_region {rule : RewriteRule} (member : rule ∈ language.rewrites) {netRule : NetRule}
    (presents : netRule.Presents rule) : Region net netRule.produced := by
  obtain ⟨other, otherPresents, -, produced⟩ := net.rules rule member
  rw [presents.unique otherPresents]
  exact produced

/-- **The reaction rules of a language's token rules** in the parallel context category: a rule's consumed tokens are
its redex, its produced tokens its reactum. -/
def reactions (language : LanguageDef) (reaction : ReactionRule (Obj String)) : Prop :=
  ∃ rule ∈ language.rewrites, ∃ netRule : NetRule, netRule.Presents rule ∧
    reaction = ⟨Obj String, bag (netRule.consumed : Multiset String), bag (netRule.produced : Multiset String)⟩

/-- **The steps of a marking are the net's reactions**: the marking `names` steps to a term exactly when the term is
equivalent to a marking its bag reacts to, by a rule `l ⟶ k` with `l ≤ names`, as the bag `k + (names - l)`. -/
theorem step_iff {names : List String} (region : Region net names) {target : Pattern} :
    (referenceStructure relEnv language).step (marking names) .any target ↔
      IsState target ∧ ∃ others : List String,
        Reacts (reactions language) (bag (names : Multiset String)) (bag (others : Multiset String)) ∧
          ObjectEquivalent relEnv language .syntax (marking others) target := by
  constructor
  · rintro ⟨-, targetState, redex, contractum, witness, toRedex, -, valid, -, toTarget, -⟩
    have valid : StepValid relEnv language redex witness contractum := valid
    obtain ⟨others, rfl, perm⟩ := shape_of_objectEquivalent net toRedex
    cases valid with
    | rule found matched premises =>
      have member := List.mem_of_getElem? found
      obtain ⟨netRule, presents, -, -⟩ := net.rules _ member
      rw [presents.1] at premises
      cases premises
      rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel, presents.2.1, marking] at matched
      cases matched with
      | collection _ bagMatch =>
        obtain ⟨remainder, split, rfl⟩ := matchBag_tokens bagMatch
        have remainderTokens : ∀ pattern ∈ remainder, ∃ name, pattern = token name := fun pattern found => by
          obtain ⟨name, -, same⟩ := List.mem_map.mp (split.subset (List.mem_append_right _ found))
          exact ⟨name, same.symm⟩
        obtain ⟨rest, rfl⟩ : ∃ rest : List String, remainder = rest.map token :=
          ⟨_, eq_map_nameOf remainderTokens⟩
        rw [← List.map_append] at split
        have total : (netRule.consumed : Multiset String) + rest = names := by
          rw [Multiset.coe_add, Multiset.coe_eq_coe]
          exact ((List.map_perm_map_iff token_injective).mp split).trans perm.symm
        refine ⟨targetState, netRule.produced ++ rest, ?_, ?_⟩
        · refine Mettapedia.GSLT.BagSaturated.reacts_iff.mpr ⟨_, ⟨_, member, netRule, presents, rfl⟩, netRule.consumed,
            netRule.produced, rfl, rfl, ?_, ?_⟩
          · rw [← total]
            exact Multiset.le_add_right _ _
          · rw [← total, add_tsub_cancel_left, Multiset.coe_add]
        · rwa [contractum_eq presents] at toTarget
  · rintro ⟨targetState, others, reacts, toTarget⟩
    obtain ⟨_, ⟨rule, member, netRule, presents, rfl⟩, l, k, redexEq, reactumEq, contained, result⟩ :=
      Mettapedia.GSLT.BagSaturated.reacts_iff.mp reacts
    obtain rfl : (netRule.consumed : Multiset String) = l := bag_injective redexEq
    obtain rfl : (netRule.produced : Multiset String) = k := bag_injective reactumEq
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨rest, restEq⟩ : ∃ rest, rest = names.diff netRule.consumed := ⟨_, rfl⟩
    have restSum : (netRule.consumed : Multiset String) + rest = names := by
      rw [restEq, ← Multiset.coe_sub, add_tsub_cancel_of_le contained]
    have restRegion : Region net rest := fun name found => region name (List.diff_subset _ _ (restEq ▸ found))
    have contractumRegion : Region net (netRule.produced ++ rest) := fun name found =>
      (List.mem_append.mp found).elim (produced_region net member presents name) (restRegion name)
    have toRedex : ObjectEquivalent relEnv language .syntax (marking names) (marking (netRule.consumed ++ rest)) :=
      objectEquivalent_of_perm net region (Multiset.coe_eq_coe.mp (by rw [← Multiset.coe_add, restSum]))
    have toOthers : ObjectEquivalent relEnv language .syntax (marking (netRule.produced ++ rest)) (marking others) :=
      objectEquivalent_of_perm net contractumRegion
        (Multiset.coe_eq_coe.mp (by rw [← Multiset.coe_add, result, ← restSum, add_tsub_cancel_left]))
    have matched : [(netRule.rest, .collection .hashBag (rest.map token) none)] ∈
        matchPatternForRule language rule (marking (netRule.consumed ++ rest)) := by
      rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel, presents.2.1, marking, List.map_append]
      exact .collection (by decide) (matchBag_prefix _ _ _)
    have premises : PremisesValid relEnv language (captureSites rule)
        [(netRule.rest, .collection .hashBag (rest.map token) none)] rule.premises []
        [(netRule.rest, .collection .hashBag (rest.map token) none)] := by
      rw [presents.1]
      exact .nil _
    have valid := StepValid.rule found matched premises
    rw [contractum_eq presents] at valid
    exact ⟨state_marking names, targetState, _, _, _, toRedex, state_marking _, valid, state_marking _,
      Relation.EqvGen.trans _ _ _ toOthers toTarget, rfl⟩

/-! ## Steps beside tokens -/

/-- **The context of tokens beside a marking**: `{c₁, …, cₙ, ...x}`. -/
def beside (hole : String) (names : List String) : Pattern := .collection .hashBag (names.map token) (some hole)

/-- **A marking placed beside tokens is the marking of both.** -/
theorem plug_beside (hole : String) (context names : List String) :
    plug hole (beside hole context) (marking names) = marking (context ++ names) := by
  rw [plug, beside, marking, applyBindingsScoped, applyBindingsScopedList_eq_map, restSplice_tokens, marking,
    List.map_append, List.map_map]
  simp only [Function.comp_def, applyBindingsScoped_token]

theorem bag_append (first second : List String) :
    bag ((first ++ second : List String) : Multiset String) = bag (second : Multiset String) ≫ bag (first : Multiset String) := by
  rw [Mettapedia.GSLT.BagRelativePushout.bag_comp, Multiset.coe_add, Multiset.coe_eq_coe.mpr List.perm_append_comm]

/-- **A marking's steps beside tokens are its reactions in that context**: placed beside `cs`, the marking `names` steps
to a term exactly when the composite `names ; cs` of the parallel context category reacts to a marking equivalent to
it. -/
theorem contextStep_iff (hole : String) {names context : List String} (region : Region net names)
    (contextRegion : Region net context) {target : Pattern} :
    (referenceStructure relEnv language).step (marking names) (.context hole (beside hole context) .any) target ↔
      IsState target ∧ ∃ others : List String,
        Reacts (reactions language) (bag (names : Multiset String) ≫ bag (context : Multiset String))
          (bag (others : Multiset String)) ∧
          ObjectEquivalent relEnv language .syntax (marking others) target := by
  rw [step_context_iff]
  constructor
  · rintro ⟨-, presentation, presents, -, step⟩
    obtain ⟨presented, rfl, perm⟩ := shape_of_objectEquivalent net presents
    rw [plug_beside] at step
    have joined : Region net (context ++ presented) := fun name found =>
      (List.mem_append.mp found).elim (contextRegion name) (fun inside => region name (perm.symm.subset inside))
    obtain ⟨targetState, others, reacts, toTarget⟩ := (step_iff net joined).mp step
    refine ⟨targetState, others, ?_, toTarget⟩
    rwa [bag_append, Multiset.coe_eq_coe.mpr perm.symm] at reacts
  · rintro ⟨targetState, others, reacts, toTarget⟩
    have joined : Region net (context ++ names) := fun name found =>
      (List.mem_append.mp found).elim (contextRegion name) (region name)
    refine ⟨state_marking names, marking names, Relation.EqvGen.refl _, state_marking names, ?_⟩
    rw [plug_beside]
    exact (step_iff net joined).mpr ⟨targetState, others, by rwa [bag_append], toTarget⟩

/-- **The least labels of a marking, by the net's rules**: the marking `names` steps under the least label `p` to `t`
exactly when, for a rule consuming `l` and producing `k`, `p` is what `names` lacks of `l`, and `t` is `k` beside what
`names` keeps. -/
theorem actIPO_iff {names label result : List String} :
    ActIPO (reactions language) (bag (label : Multiset String)) (bag (names : Multiset String))
        (bag (result : Multiset String)) ↔
      ∃ rule ∈ language.rewrites, ∃ netRule : NetRule, netRule.Presents rule ∧
        (label : Multiset String) = netRule.consumed - names ∧
          (result : Multiset String) = netRule.produced + (names - netRule.consumed) := by
  rw [Mettapedia.GSLT.BagSaturated.actIPO_iff]
  constructor
  · rintro ⟨_, ⟨rule, member, netRule, presents, rfl⟩, l, k, redexEq, reactumEq, labelEq, resultEq⟩
    obtain rfl : (netRule.consumed : Multiset String) = l := bag_injective redexEq
    obtain rfl : (netRule.produced : Multiset String) = k := bag_injective reactumEq
    exact ⟨rule, member, netRule, presents, labelEq, resultEq⟩
  · rintro ⟨rule, member, netRule, presents, labelEq, resultEq⟩
    exact ⟨_, ⟨rule, member, netRule, presents, rfl⟩, netRule.consumed, netRule.produced, rfl, rfl, labelEq, resultEq⟩

/-- **A least-labelled transition is a context step at the front door**: placed beside its least label, the marking
steps to the transition's result. -/
theorem step_of_actIPO (hole : String) {names label result : List String} (region : Region net names)
    (labelRegion : Region net label)
    (least : ActIPO (reactions language) (bag (label : Multiset String)) (bag (names : Multiset String))
      (bag (result : Multiset String))) :
    (referenceStructure relEnv language).step (marking names) (.context hole (beside hole label) .any)
      (marking result) :=
  (contextStep_iff net hole region labelRegion).mpr
    ⟨state_marking result, result, Mettapedia.GSLT.SemiSaturated.Reacts.of_actIPO least, Relation.EqvGen.refl _⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.TokenNets
