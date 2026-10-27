import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Formula
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# What the generated formulas mean

A native structure interprets the generators of a language over a carrier, given as a parameter so
that structures over one carrier share their elements:
- steps between elements, each with the rule it uses;
- the structure of elements: which are built by which constructor from which arguments; which are
  collections that split into which parts, are empty, or have one element; which are abstractions with
  which bodies; which are bound variables; and what an abstraction's body gives on an argument;
- which elements have which types, and which elements the language's terms name;
- which elements are the same element, as the language identifies them. The counting modalities count
  elements up to this identity.

These are relations rather than functions, since modulo equations an element has many presentations.

Satisfaction (`sat`) is defined by recursion on formulas. A least fixed point is the intersection of the
sets closed under its body, and a greatest fixed point the union of the sets its body preserves, as in
the modal μ-calculus.

**The De Morgan law** (`sat_dual`): the dual of a formula holds exactly where the formula fails, once
the fixed-point environment is complemented. It needs no monotonicity, since the duality of least and
greatest fixed points is purely logical. For closed formulas the dual is negation (`sat_dual_closed`),
and `imp` is implication (`sat_imp`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax

universe u

/-- A fixed-point environment: one set for each free fixed-point variable. -/
abbrev Env (Carrier : Type u) (n : ℕ) := Fin n → Set Carrier

namespace Env

variable {Carrier : Type u}

/-- Bind the newest fixed-point variable. -/
def extend {n : ℕ} (env : Env Carrier n) (set : Set Carrier) : Env Carrier (n + 1) := Fin.cons set env

/-- Complement every set of an environment. -/
def complement {n : ℕ} (env : Env Carrier n) : Env Carrier n := fun index => (env index)ᶜ

theorem complement_extend {n : ℕ} (env : Env Carrier n) (set : Set Carrier) :
    (env.extend set).complement = env.complement.extend setᶜ := by
  funext index
  refine Fin.cases ?_ (fun _ => ?_) index <;> rfl

/-- The environment of a closed formula. -/
abbrev closed : Env Carrier 0 := Fin.elim0

theorem complement_closed : (closed : Env Carrier 0).complement = closed := funext fun index => index.elim0

end Env

/-- **A native structure**: the generators of a language interpreted over a carrier. -/
structure NativeStructure (Carrier : Type u) where
  /-- A step, with the rules it may use. -/
  step : Carrier → StepLabel → Carrier → Prop
  /-- The element is built by the constructor from these arguments. -/
  built : Carrier → String → List Carrier → Prop
  /-- The element is a collection of the kind splitting into these two parts. -/
  split : Carrier → CollType → Carrier → Carrier → Prop
  /-- The element is the empty collection of the kind. -/
  empty : Carrier → CollType → Prop
  /-- The element is a one-element collection of the kind with this element. -/
  single : Carrier → CollType → Carrier → Prop
  /-- The element is an abstraction with this body. -/
  body : Carrier → Carrier → Prop
  /-- The element abstracts this many variables at once, with this body. -/
  multiBody : Carrier → ℕ → Carrier → Prop
  /-- The element is the bound variable with this index. -/
  bound : Carrier → ℕ → Prop
  /-- The element has the type. -/
  typed : Carrier → TypeExpr → Prop
  /-- The element is the one the term names. -/
  named : Carrier → Pattern → Prop
  /-- The two elements are the same element, as the language identifies them. -/
  same : Carrier → Carrier → Prop
  /-- A body applied to an argument. -/
  apply : Carrier → Carrier → Carrier
  /-- The element is in the declared relation. -/
  inRelation : Carrier → String → Prop

namespace NativeStructure

variable {Carrier : Type u} (S : NativeStructure Carrier)

open Formula

/-- A step in the direction: from the element to the other, or from the other to the element. -/
def stepIn (direction : Direction) (element : Carrier) (label : StepLabel) (other : Carrier) : Prop :=
  match direction with
  | .forward => S.step element label other
  | .backward => S.step other label element

/-- **At least `count` distinct elements satisfy the predicate**: a list of that length, no two the same,
all satisfying it. -/
def AtLeast (count : ℕ) (holds : Carrier → Prop) : Prop :=
  ∃ witnesses : List Carrier, witnesses.length = count ∧
    witnesses.Pairwise (fun first second => ¬ S.same first second) ∧ ∀ witness ∈ witnesses, holds witness

variable {S} in
/-- Counting is monotone in the predicate. -/
theorem AtLeast.mono {count : ℕ} {holds stronger : Carrier → Prop} (many : S.AtLeast count holds)
    (implies : ∀ element, holds element → stronger element) : S.AtLeast count stronger := by
  obtain ⟨witnesses, length, distinct, all⟩ := many
  exact ⟨witnesses, length, distinct, fun witness member => implies witness (all witness member)⟩

variable {S} in
/-- Counting respects equivalent predicates. -/
theorem AtLeast.congr {count : ℕ} {holds other : Carrier → Prop} (same : ∀ element, holds element ↔ other element) :
    S.AtLeast count holds ↔ S.AtLeast count other :=
  ⟨fun many => many.mono fun element => (same element).mp, fun many => many.mono fun element => (same element).mpr⟩

variable {S} in
theorem atLeast_zero (holds : Carrier → Prop) : S.AtLeast 0 holds :=
  ⟨[], rfl, List.Pairwise.nil, fun _ member => nomatch member⟩

variable {S} in
/-- **Counting one more**: a first witness, then as many others, none the same as it. -/
theorem atLeast_succ (count : ℕ) (holds : Carrier → Prop) :
    S.AtLeast (count + 1) holds ↔ ∃ first, holds first ∧ S.AtLeast count fun other => holds other ∧ ¬ S.same first other := by
  constructor
  · rintro ⟨_ | ⟨first, rest⟩, length, distinct, all⟩
    · cases length
    · rw [List.pairwise_cons] at distinct
      exact ⟨first, all first (List.mem_cons_self ..), rest, Nat.succ_injective length, distinct.2,
        fun other member => ⟨all other (List.mem_cons_of_mem _ member), distinct.1 other member⟩⟩
  · rintro ⟨first, firstHolds, rest, length, distinct, all⟩
    refine ⟨first :: rest, by simp [length], List.pairwise_cons.mpr ⟨fun other member => (all other member).2, distinct⟩,
      fun other member => ?_⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact firstHolds
    · exact (all other member).1

mutual
/-- **Satisfaction** of a formula at an element, in an environment for its fixed-point variables. -/
def sat : {n : ℕ} → Env Carrier n → Formula n → Carrier → Prop
  | _, _, .top, _ => True
  | _, _, .bot, _ => False
  | _, env, .and left right, element => sat env left element ∧ sat env right element
  | _, env, .or left right, element => sat env left element ∨ sat env right element
  | _, env, .var index, element => element ∈ env index
  | _, env, .mu inner, element =>
      ∀ closed : Set Carrier, (∀ other, sat (env.extend closed) inner other → other ∈ closed) → element ∈ closed
  | _, env, .nu inner, element =>
      ∃ invariant : Set Carrier, element ∈ invariant ∧ ∀ other ∈ invariant, sat (env.extend invariant) inner other
  | _, env, .possibly label formula, element => ∃ next, S.step element label next ∧ sat env formula next
  | _, env, .necessarily label formula, element => ∀ next, S.step element label next → sat env formula next
  | _, env, .sometimeBefore label formula, element => ∃ previous, S.step previous label element ∧ sat env formula previous
  | _, env, .alwaysBefore label formula, element => ∀ previous, S.step previous label element → sat env formula previous
  | _, env, .atLeast count direction label formula, element =>
      S.AtLeast count fun other => S.stepIn direction element label other ∧ sat env formula other
  | _, env, .allButFewer count direction label formula, element =>
      ¬ S.AtLeast count fun other => S.stepIn direction element label other ∧ ¬ sat env formula other
  | _, env, .built constructor arguments, element =>
      ∃ parts, S.built element constructor parts ∧ satAll env arguments parts
  | _, env, .everyBuilt constructor arguments, element =>
      ∀ parts, S.built element constructor parts → satSome env arguments parts
  | _, env, .split kind left right, element =>
      ∃ first second, S.split element kind first second ∧ sat env left first ∧ sat env right second
  | _, env, .everySplit kind left right, element =>
      ∀ first second, S.split element kind first second → sat env left first ∨ sat env right second
  | _, _, .empty kind, element => S.empty element kind
  | _, _, .nonEmpty kind, element => ¬ S.empty element kind
  | _, env, .single kind formula, element => ∃ member, S.single element kind member ∧ sat env formula member
  | _, env, .everySingle kind formula, element => ∀ member, S.single element kind member → sat env formula member
  | _, env, .body formula, element => ∃ inner, S.body element inner ∧ sat env formula inner
  | _, env, .everyBody formula, element => ∀ inner, S.body element inner → sat env formula inner
  | _, env, .multiBody arity formula, element =>
      ∃ inner, S.multiBody element arity inner ∧ sat env formula inner
  | _, env, .everyMultiBody arity formula, element =>
      ∀ inner, S.multiBody element arity inner → sat env formula inner
  | _, _, .bound index, element => S.bound element index
  | _, _, .notBound index, element => ¬ S.bound element index
  | _, _, .typed type, element => S.typed element type
  | _, _, .untyped type, element => ¬ S.typed element type
  | _, _, .is term, element => S.named element term
  | _, _, .isNot term, element => ¬ S.named element term
  | _, env, .mapsAll argument result, element =>
      ∃ inner, S.body element inner ∧ ∀ value, sat env argument value ∨ sat env result (S.apply inner value)
  | _, env, .mapsSome argument result, element =>
      ∀ inner, S.body element inner → ∃ value, sat env argument value ∧ sat env result (S.apply inner value)
  | _, env, .someOf type formula, _ => ∃ witness, S.typed witness type ∧ sat env formula witness
  | _, env, .everyOf type formula, _ => ∀ witness, S.typed witness type → sat env formula witness
  | _, _, .inRelation relation, element => S.inRelation element relation
  | _, _, .notInRelation relation, element => ¬ S.inRelation element relation

/-- Every formula of the list holds at the corresponding part, and the lengths agree. -/
def satAll : {n : ℕ} → Env Carrier n → Formulas n → List Carrier → Prop
  | _, _, .nil, [] => True
  | _, env, .cons formula formulas, part :: parts => sat env formula part ∧ satAll env formulas parts
  | _, _, _, _ => False

/-- Some formula of the list holds at the corresponding part, or the lengths differ. -/
def satSome : {n : ℕ} → Env Carrier n → Formulas n → List Carrier → Prop
  | _, _, .nil, [] => False
  | _, env, .cons formula formulas, part :: parts => sat env formula part ∨ satSome env formulas parts
  | _, _, _, _ => True
end

/-! ## The De Morgan law -/

mutual
/-- **The dual of a formula holds exactly where the formula fails**, in the complemented environment. -/
theorem sat_dual : ∀ {n : ℕ} (formula : Formula n) (env : Env Carrier n) (element : Carrier),
    S.sat env.complement formula.dual element ↔ ¬ S.sat env formula element
  | _, .top, _, _ => by simp [sat, dual]
  | _, .bot, _, _ => by simp [sat, dual]
  | _, .and left right, env, element => by
    simp only [dual, sat, sat_dual left env element, sat_dual right env element, not_and_or]
  | _, .or left right, env, element => by
    simp only [dual, sat, sat_dual left env element, sat_dual right env element, not_or]
  | _, .var index, env, element => by simp [dual, sat, Env.complement]
  | _, .mu inner, env, element => by
    simp only [dual, sat, not_forall, exists_prop]
    constructor
    · rintro ⟨invariant, member, preserved⟩
      refine ⟨invariantᶜ, fun other holds => ?_, fun outside => outside member⟩
      intro inside
      have := preserved other inside
      rw [← compl_compl invariant, ← Env.complement_extend, sat_dual inner] at this
      exact this holds
    · rintro ⟨closed, isClosed, outside⟩
      refine ⟨closedᶜ, outside, fun other inside => ?_⟩
      rw [← Env.complement_extend, sat_dual inner]
      exact fun holds => inside (isClosed other holds)
  | _, .nu inner, env, element => by
    have key : ∀ (set : Set Carrier) (other : Carrier),
        S.sat (env.complement.extend set) inner.dual other ↔ ¬ S.sat (env.extend setᶜ) inner other := by
      intro set other
      rw [show env.complement.extend set = (env.extend setᶜ).complement by
        rw [Env.complement_extend, compl_compl]]
      exact sat_dual inner (env.extend setᶜ) other
    simp only [dual, sat, not_exists, not_and]
    constructor
    · intro least invariant member preserved
      have inComplement := least invariantᶜ fun other holds => by
        rw [key, compl_compl] at holds
        exact fun inside => holds (preserved other inside)
      exact inComplement member
    · intro noInvariant closed isClosed
      by_contra outside
      apply noInvariant closedᶜ outside
      intro other inside
      by_contra fails
      exact inside (isClosed other ((key closed other).mpr fails))
  | _, .possibly label formula, env, element => by
    simp only [dual, sat, sat_dual formula, not_exists, not_and]
  | _, .necessarily label formula, env, element => by
    simp only [dual, sat, sat_dual formula, not_forall, exists_prop]
  | _, .sometimeBefore label formula, env, element => by
    simp only [dual, sat, sat_dual formula, not_exists, not_and]
  | _, .alwaysBefore label formula, env, element => by
    simp only [dual, sat, sat_dual formula, not_forall, exists_prop]
  | _, .atLeast count direction label formula, env, element => by
    simp only [dual, sat, sat_dual formula, not_not]
  | _, .allButFewer count direction label formula, env, element => by
    simp only [dual, sat, sat_dual formula, not_not]
  | _, .built constructor arguments, env, element => by
    simp only [dual, sat, satSome_dualList arguments, not_exists, not_and]
  | _, .everyBuilt constructor arguments, env, element => by
    simp only [dual, sat, satAll_dualList arguments, not_forall, exists_prop]
  | _, .split kind left right, env, element => by
    simp only [dual, sat, sat_dual left, sat_dual right, not_exists, not_and, imp_iff_not_or]
  | _, .everySplit kind left right, env, element => by
    simp only [dual, sat, sat_dual left, sat_dual right, not_forall, not_or, exists_prop]
  | _, .empty kind, env, element => by simp [dual, sat]
  | _, .nonEmpty kind, env, element => by simp [dual, sat]
  | _, .single kind formula, env, element => by
    simp only [dual, sat, sat_dual formula, not_exists, not_and]
  | _, .everySingle kind formula, env, element => by
    simp only [dual, sat, sat_dual formula, not_forall, exists_prop]
  | _, .body formula, env, element => by
    simp only [dual, sat, sat_dual formula, not_exists, not_and]
  | _, .everyBody formula, env, element => by
    simp only [dual, sat, sat_dual formula, not_forall, exists_prop]
  | _, .multiBody arity formula, env, element => by
    simp only [dual, sat, sat_dual formula, not_exists, not_and]
  | _, .everyMultiBody arity formula, env, element => by
    simp only [dual, sat, sat_dual formula, not_forall, exists_prop]
  | _, .bound index, env, element => by simp [dual, sat]
  | _, .notBound index, env, element => by simp [dual, sat]
  | _, .typed type, env, element => by simp [dual, sat]
  | _, .untyped type, env, element => by simp [dual, sat]
  | _, .is term, env, element => by simp [dual, sat]
  | _, .isNot term, env, element => by simp [dual, sat]
  | _, .inRelation relation, env, element => by simp [dual, sat]
  | _, .notInRelation relation, env, element => by simp [dual, sat]
  | _, .mapsAll argument result, env, element => by
    simp only [dual, sat, sat_dual argument, sat_dual result, not_exists, not_and, not_forall, not_or]
  | _, .mapsSome argument result, env, element => by
    simp only [dual, sat, sat_dual argument, sat_dual result, not_forall, not_exists, not_and_or, exists_prop]
  | _, .someOf type formula, env, element => by
    simp only [dual, sat, sat_dual formula, not_exists, not_and]
  | _, .everyOf type formula, env, element => by
    simp only [dual, sat, sat_dual formula, not_forall, exists_prop]

/-- The duals of a list hold somewhere exactly where the list does not hold everywhere. -/
theorem satSome_dualList : ∀ {n : ℕ} (formulas : Formulas n) {env : Env Carrier n} {parts : List Carrier},
    S.satSome env.complement (dualList formulas) parts ↔ ¬ S.satAll env formulas parts
  | _, .nil, _, [] => by simp [satSome, satAll, dualList]
  | _, .nil, _, _ :: _ => by simp [satSome, satAll, dualList]
  | _, .cons formula formulas, _, [] => by simp [satSome, satAll, dualList]
  | _, .cons formula formulas, env, part :: parts => by
    simp only [dualList, satSome, satAll, sat_dual formula env part, satSome_dualList formulas, not_and_or]

/-- The duals of a list hold everywhere exactly where the list holds nowhere. -/
theorem satAll_dualList : ∀ {n : ℕ} (formulas : Formulas n) {env : Env Carrier n} {parts : List Carrier},
    S.satAll env.complement (dualList formulas) parts ↔ ¬ S.satSome env formulas parts
  | _, .nil, _, [] => by simp [satSome, satAll, dualList]
  | _, .nil, _, _ :: _ => by simp [satSome, satAll, dualList]
  | _, .cons formula formulas, _, [] => by simp [satSome, satAll, dualList]
  | _, .cons formula formulas, env, part :: parts => by
    simp only [dualList, satSome, satAll, sat_dual formula env part, satAll_dualList formulas, not_or]
end

/-- **For a closed formula, the dual is the negation.** -/
theorem sat_dual_closed (formula : Formula 0) (element : Carrier) :
    S.sat Env.closed formula.dual element ↔ ¬ S.sat Env.closed formula element := by
  have := S.sat_dual formula Env.closed element
  rwa [Env.complement_closed] at this

/-- **At most `count`** distinct terms one step away satisfy a closed formula. -/
theorem sat_atMost (count : ℕ) (direction : Direction) (label : StepLabel) (formula : Formula 0) (element : Carrier) :
    S.sat Env.closed (atMost count direction label formula) element ↔
      ¬ S.AtLeast (count + 1) fun other => S.stepIn direction element label other ∧ S.sat Env.closed formula other := by
  rw [atMost, sat_dual_closed]
  rfl

/-- **Exactly one** distinct term is one step away. -/
theorem sat_exactlyOne (direction : Direction) (label : StepLabel) (element : Carrier) :
    S.sat Env.closed (exactlyOne (n := 0) direction label) element ↔
      S.AtLeast 1 (fun other => S.stepIn direction element label other) ∧
        ¬ S.AtLeast 2 fun other => S.stepIn direction element label other := by
  simp only [exactlyOne, sat, sat_atMost, and_true]

/-- **Implication**: for a closed premise, `imp` holds where the premise implies the conclusion. -/
theorem sat_imp (premise : Formula 0) (conclusion : Formula 0) (element : Carrier) :
    S.sat Env.closed (imp premise conclusion) element ↔
      (S.sat Env.closed premise element → S.sat Env.closed conclusion element) := by
  simp only [imp, sat, sat_dual_closed, imp_iff_not_or]

end NativeStructure

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
