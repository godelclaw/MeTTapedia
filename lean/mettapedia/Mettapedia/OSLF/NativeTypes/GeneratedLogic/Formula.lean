import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# The native type formulas a language generates

A language generates its native types from its own theory, closed under logic:
- each constructor gives a structural former that holds at a term built by that constructor from
  arguments satisfying the given formulas (`built`);
- each collection kind gives the formers of its algebra: empty, singleton, and a split into two parts
  (`empty`, `single`, `split`);
- binders give formers on abstractions: their body under a fresh name (`body`, `multiBody`), the bound
  variables in such bodies (`bound`), and the hom type, which says what the abstraction does to every
  argument (`mapsAll`);
- the language's steps give the modalities, forward and backward, for all steps, one rule's steps, or
  the steps at one site: a rule's step inside the context that a congruence rule provides
  (`possibly`, `necessarily`, `sometimeBefore`, `alwaysBefore`, labelled by `StepLabel`);
- the steps also give counting modalities: at least `k` distinct terms one step away satisfy a formula,
  or fewer than `k` fail it (`atLeast`, `allButFewer`, in either `Direction`). Distinct means distinct as
  the language identifies terms, modulo its equations, so two steps to the same term count once;
- the language's types give typing formers and quantifiers over the terms of a type (`typed`,
  `someOf`, `everyOf`), and its terms give singleton types (`is`);
- logic adds conjunction and disjunction, and least and greatest fixed points.

Formulas are in negation normal form: every former comes with its De Morgan dual as a former of its own
(`dual`, an involution: `dual_dual`). Every fixed-point variable therefore occurs positively. The hom
type is written positively too: `mapsAll χ ψ` says that every argument fails `χ` or gives a result
satisfying `ψ`, so `φ ⇒ ψ` is `mapsAll (dual φ) ψ`. For closed formulas the dual is negation, and
implication is `imp`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The steps a modality ranges over. -/
inductive StepLabel where
  /-- Every step. -/
  | any
  /-- The steps of the rule at this index. -/
  | rule (index : ℕ)
  /-- The steps of the rule at this index with a premise step that has the label: steps at the site
  that rule's congruence provides. -/
  | under (index : ℕ) (label : StepLabel)
  deriving DecidableEq, Repr

/-- Which way steps are taken: from the term, or into it. -/
inductive Direction where
  | forward
  | backward
  deriving DecidableEq, Repr

mutual
/-- **Native type formulas** in negation normal form, with `n` free fixed-point variables. -/
inductive Formula : ℕ → Type where
  /-- Every term. -/
  | top {n : ℕ} : Formula n
  /-- No term. -/
  | bot {n : ℕ} : Formula n
  | and {n : ℕ} : Formula n → Formula n → Formula n
  | or {n : ℕ} : Formula n → Formula n → Formula n
  /-- A fixed-point variable. -/
  | var {n : ℕ} : Fin n → Formula n
  /-- The least fixed point. -/
  | mu {n : ℕ} : Formula (n + 1) → Formula n
  /-- The greatest fixed point. -/
  | nu {n : ℕ} : Formula (n + 1) → Formula n
  /-- Some step leads to a term satisfying the formula. -/
  | possibly {n : ℕ} : StepLabel → Formula n → Formula n
  /-- Every step leads to a term satisfying the formula. -/
  | necessarily {n : ℕ} : StepLabel → Formula n → Formula n
  /-- Some step leads here from a term satisfying the formula. -/
  | sometimeBefore {n : ℕ} : StepLabel → Formula n → Formula n
  /-- Every step that leads here comes from a term satisfying the formula. -/
  | alwaysBefore {n : ℕ} : StepLabel → Formula n → Formula n
  /-- At least this many distinct terms one step away, in the direction, satisfy the formula. -/
  | atLeast {n : ℕ} : ℕ → Direction → StepLabel → Formula n → Formula n
  /-- Fewer than this many distinct terms one step away, in the direction, fail the formula. -/
  | allButFewer {n : ℕ} : ℕ → Direction → StepLabel → Formula n → Formula n
  /-- The term is built by the constructor from arguments satisfying the formulas, in some way. -/
  | built {n : ℕ} : String → Formulas n → Formula n
  /-- Every way of building the term by the constructor has some argument satisfying its formula. -/
  | everyBuilt {n : ℕ} : String → Formulas n → Formula n
  /-- The term is a collection of the kind that splits into two parts satisfying the formulas. -/
  | split {n : ℕ} : CollType → Formula n → Formula n → Formula n
  /-- Every split of the term into two parts has one part satisfying its formula. -/
  | everySplit {n : ℕ} : CollType → Formula n → Formula n → Formula n
  /-- The term is the empty collection of the kind. -/
  | empty {n : ℕ} : CollType → Formula n
  /-- The term is not the empty collection of the kind. -/
  | nonEmpty {n : ℕ} : CollType → Formula n
  /-- The term is a one-element collection of the kind whose element satisfies the formula. -/
  | single {n : ℕ} : CollType → Formula n → Formula n
  /-- Every presentation of the term as a one-element collection has its element satisfying the formula. -/
  | everySingle {n : ℕ} : CollType → Formula n → Formula n
  /-- The term is an abstraction whose body, under a fresh name, satisfies the formula. -/
  | body {n : ℕ} : Formula n → Formula n
  /-- Every presentation of the term as an abstraction has its body satisfying the formula. -/
  | everyBody {n : ℕ} : Formula n → Formula n
  /-- The term abstracts several variables at once, and its body satisfies the formula. -/
  | multiBody {n : ℕ} : ℕ → Formula n → Formula n
  /-- Every presentation of the term as such an abstraction has its body satisfying the formula. -/
  | everyMultiBody {n : ℕ} : ℕ → Formula n → Formula n
  /-- The term is the bound variable with this index. -/
  | bound {n : ℕ} : ℕ → Formula n
  /-- The term is not the bound variable with this index. -/
  | notBound {n : ℕ} : ℕ → Formula n
  /-- The term has the type. -/
  | typed {n : ℕ} : TypeExpr → Formula n
  /-- The term does not have the type. -/
  | untyped {n : ℕ} : TypeExpr → Formula n
  /-- The term is this term. -/
  | is {n : ℕ} : Pattern → Formula n
  /-- The term is not this term. -/
  | isNot {n : ℕ} : Pattern → Formula n
  /-- The term is an abstraction, and every argument fails the first formula or gives a result
  satisfying the second. -/
  | mapsAll {n : ℕ} : Formula n → Formula n → Formula n
  /-- For every presentation of the term as an abstraction, some argument satisfies the first formula
  and gives a result satisfying the second. -/
  | mapsSome {n : ℕ} : Formula n → Formula n → Formula n
  /-- Some term of the type satisfies the formula. -/
  | someOf {n : ℕ} : TypeExpr → Formula n → Formula n
  /-- Every term of the type satisfies the formula. -/
  | everyOf {n : ℕ} : TypeExpr → Formula n → Formula n

/-- A list of formulas, the arguments of a structural former. -/
inductive Formulas : ℕ → Type where
  | nil {n : ℕ} : Formulas n
  | cons {n : ℕ} : Formula n → Formulas n → Formulas n
end

namespace Formula

mutual
/-- **The De Morgan dual**: each former is exchanged with its dual. -/
def dual : {n : ℕ} → Formula n → Formula n
  | _, .top => .bot
  | _, .bot => .top
  | _, .and left right => .or (dual left) (dual right)
  | _, .or left right => .and (dual left) (dual right)
  | _, .var index => .var index
  | _, .mu inner => .nu (dual inner)
  | _, .nu inner => .mu (dual inner)
  | _, .possibly label formula => .necessarily label (dual formula)
  | _, .necessarily label formula => .possibly label (dual formula)
  | _, .sometimeBefore label formula => .alwaysBefore label (dual formula)
  | _, .alwaysBefore label formula => .sometimeBefore label (dual formula)
  | _, .atLeast count direction label formula => .allButFewer count direction label (dual formula)
  | _, .allButFewer count direction label formula => .atLeast count direction label (dual formula)
  | _, .built constructor arguments => .everyBuilt constructor (dualList arguments)
  | _, .everyBuilt constructor arguments => .built constructor (dualList arguments)
  | _, .split kind left right => .everySplit kind (dual left) (dual right)
  | _, .everySplit kind left right => .split kind (dual left) (dual right)
  | _, .empty kind => .nonEmpty kind
  | _, .nonEmpty kind => .empty kind
  | _, .single kind formula => .everySingle kind (dual formula)
  | _, .everySingle kind formula => .single kind (dual formula)
  | _, .body formula => .everyBody (dual formula)
  | _, .everyBody formula => .body (dual formula)
  | _, .multiBody arity formula => .everyMultiBody arity (dual formula)
  | _, .everyMultiBody arity formula => .multiBody arity (dual formula)
  | _, .bound index => .notBound index
  | _, .notBound index => .bound index
  | _, .typed type => .untyped type
  | _, .untyped type => .typed type
  | _, .is term => .isNot term
  | _, .isNot term => .is term
  | _, .mapsAll argument result => .mapsSome (dual argument) (dual result)
  | _, .mapsSome argument result => .mapsAll (dual argument) (dual result)
  | _, .someOf type formula => .everyOf type (dual formula)
  | _, .everyOf type formula => .someOf type (dual formula)

/-- The duals of a list of formulas. -/
def dualList : {n : ℕ} → Formulas n → Formulas n
  | _, .nil => .nil
  | _, .cons formula formulas => .cons (dual formula) (dualList formulas)
end

mutual
/-- **The dual is an involution.** -/
theorem dual_dual : ∀ {n : ℕ} (formula : Formula n), dual (dual formula) = formula
  | _, .top | _, .bot | _, .var _ | _, .empty _ | _, .nonEmpty _ | _, .bound _ | _, .notBound _
  | _, .typed _ | _, .untyped _ | _, .is _ | _, .isNot _ => rfl
  | _, .and left right | _, .or left right | _, .split _ left right | _, .everySplit _ left right
  | _, .mapsAll left right | _, .mapsSome left right => by
    simp only [dual, dual_dual left, dual_dual right]
  | _, .mu inner | _, .nu inner => by simp only [dual, dual_dual inner]
  | _, .possibly _ formula | _, .necessarily _ formula | _, .sometimeBefore _ formula
  | _, .alwaysBefore _ formula | _, .single _ formula | _, .everySingle _ formula | _, .body formula
  | _, .everyBody formula | _, .multiBody _ formula | _, .everyMultiBody _ formula | _, .someOf _ formula
  | _, .everyOf _ formula | _, .atLeast _ _ _ formula | _, .allButFewer _ _ _ formula => by
    simp only [dual, dual_dual formula]
  | _, .built _ arguments | _, .everyBuilt _ arguments => by simp only [dual, dualList_dualList arguments]

theorem dualList_dualList : ∀ {n : ℕ} (formulas : Formulas n), dualList (dualList formulas) = formulas
  | _, .nil => rfl
  | _, .cons formula formulas => by simp only [dualList, dual_dual formula, dualList_dualList formulas]
end

/-- **Implication**: the dual of the premise, or the conclusion. For a closed premise it holds where the
premise implies the conclusion (`NativeStructure.sat_imp`). -/
def imp {n : ℕ} (premise conclusion : Formula n) : Formula n := .or (dual premise) conclusion

/-- **At most `count` distinct terms one step away satisfy the formula**: the dual of at least one more. -/
def atMost {n : ℕ} (count : ℕ) (direction : Direction) (label : StepLabel) (formula : Formula n) : Formula n :=
  dual (.atLeast (count + 1) direction label formula)

/-- **Exactly one distinct term is one step away**: at least one, and at most one. -/
def exactlyOne {n : ℕ} (direction : Direction) (label : StepLabel) : Formula n :=
  .and (.atLeast 1 direction label .top) (atMost 1 direction label .top)

end Formula

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
