import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Semantics

/-!
# Many-sorted native types, as one-sorted native types with sort guards

A language with several sorts has a native type language whose formulas are about elements of a sort
(`SFormula`): steps, splits and past steps stay within the sort; a constructor's arguments, a singleton's member and
a quantified witness each have their own declared sort; a fixed point binds a predicate on elements of its sort.
Their meaning (`SortedStructure.ssat`) is over carriers by sort.

- **The sorted structure of a one-sorted structure** (`restrict`): the elements of a sort are the elements typed at it,
  and each generator relates them as the one-sorted structure does. Its elements form the sum over sorts of the
  elements of each sort.
- **The guarded translation** (`core`, `guard`): each sorted formula becomes a one-sorted formula, every position
  guarded by its sort: an existential position requires the sort (`typed`), a universal one quantifies over the
  elements of the sort only (`untyped` or the formula).
- **The reduction is exact** (`core_iff`, `guard_iff`, `guard_iff_closed`): in corresponding environments, a sorted
  formula holds at an element of a sort exactly when its translation holds at the element in the one-sorted structure.
  No property of the one-sorted structure is needed: its steps may leave a sort and its elements may have several
  types; the guards read only the elements of each position's sort.

Binder formers are not sorted here: an abstraction's body is an open term, which no closed sort types.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySorted

open Mettapedia.OSLF.MeTTaIL.Syntax

universe u

/-- **A many-sorted structure**: carriers by sort, and the generators of a language between elements of the sorts they
relate. Steps and splits stay within a sort; constructor arguments and singleton members carry their sorts. -/
structure SortedStructure (Srt : Type) where
  Carrier : Srt → Type u
  step : {sort : Srt} → Carrier sort → StepLabel → Carrier sort → Prop
  built : {sort : Srt} → Carrier sort → String → List (Σ other, Carrier other) → Prop
  split : {sort : Srt} → Carrier sort → CollType → Carrier sort → Carrier sort → Prop
  empty : {sort : Srt} → Carrier sort → CollType → Prop
  single : {sort : Srt} → Carrier sort → CollType → (Σ other, Carrier other) → Prop
  named : {sort : Srt} → Carrier sort → Pattern → Prop
  inRelation : {sort : Srt} → Carrier sort → String → Prop

/-- An element of some sort. -/
abbrev SortedStructure.Element {Srt : Type} (M : SortedStructure.{u} Srt) : Type u := Σ sort, M.Carrier sort

mutual
/-- **Many-sorted formulas**, with fixed-point variables of the sorts `Γ`. A formula is evaluated at an element of a
sort; a fixed point, a quantifier, a constructor argument and a singleton's member declare their sorts. -/
inductive SFormula (Srt : Type) : List Srt → Type where
  | top {Γ : List Srt} : SFormula Srt Γ
  | bot {Γ : List Srt} : SFormula Srt Γ
  | and {Γ : List Srt} : SFormula Srt Γ → SFormula Srt Γ → SFormula Srt Γ
  | or {Γ : List Srt} : SFormula Srt Γ → SFormula Srt Γ → SFormula Srt Γ
  | var {Γ : List Srt} : Fin Γ.length → SFormula Srt Γ
  | mu {Γ : List Srt} (sort : Srt) : SFormula Srt (sort :: Γ) → SFormula Srt Γ
  | nu {Γ : List Srt} (sort : Srt) : SFormula Srt (sort :: Γ) → SFormula Srt Γ
  | possibly {Γ : List Srt} : StepLabel → SFormula Srt Γ → SFormula Srt Γ
  | necessarily {Γ : List Srt} : StepLabel → SFormula Srt Γ → SFormula Srt Γ
  | sometimeBefore {Γ : List Srt} : StepLabel → SFormula Srt Γ → SFormula Srt Γ
  | alwaysBefore {Γ : List Srt} : StepLabel → SFormula Srt Γ → SFormula Srt Γ
  | built {Γ : List Srt} : String → SFormulas Srt Γ → SFormula Srt Γ
  | everyBuilt {Γ : List Srt} : String → SFormulas Srt Γ → SFormula Srt Γ
  | split {Γ : List Srt} : CollType → SFormula Srt Γ → SFormula Srt Γ → SFormula Srt Γ
  | everySplit {Γ : List Srt} : CollType → SFormula Srt Γ → SFormula Srt Γ → SFormula Srt Γ
  | empty {Γ : List Srt} : CollType → SFormula Srt Γ
  | nonEmpty {Γ : List Srt} : CollType → SFormula Srt Γ
  | single {Γ : List Srt} : CollType → Srt → SFormula Srt Γ → SFormula Srt Γ
  | everySingle {Γ : List Srt} : CollType → Srt → SFormula Srt Γ → SFormula Srt Γ
  | is {Γ : List Srt} : Pattern → SFormula Srt Γ
  | isNot {Γ : List Srt} : Pattern → SFormula Srt Γ
  | someOf {Γ : List Srt} : Srt → SFormula Srt Γ → SFormula Srt Γ
  | everyOf {Γ : List Srt} : Srt → SFormula Srt Γ → SFormula Srt Γ
  | inRelation {Γ : List Srt} : String → SFormula Srt Γ
  | notInRelation {Γ : List Srt} : String → SFormula Srt Γ

/-- Formulas for a constructor's arguments, each with its sort. -/
inductive SFormulas (Srt : Type) : List Srt → Type where
  | nil {Γ : List Srt} : SFormulas Srt Γ
  | cons {Γ : List Srt} : Srt → SFormula Srt Γ → SFormulas Srt Γ → SFormulas Srt Γ
end

namespace SortedStructure

variable {Srt : Type} (M : SortedStructure.{u} Srt)

mutual
/-- **Satisfaction of a many-sorted formula** at an element, in an environment for its fixed-point variables. -/
def ssat : {Γ : List Srt} → Env M.Element Γ.length → SFormula Srt Γ → M.Element → Prop
  | _, _, .top, _ => True
  | _, _, .bot, _ => False
  | _, env, .and left right, element => ssat env left element ∧ ssat env right element
  | _, env, .or left right, element => ssat env left element ∨ ssat env right element
  | Γ, env, .var index, element => element.1 = Γ.get index ∧ element ∈ env index
  | Γ, env, .mu sort inner, element => element.1 = sort ∧
      ∀ closed : Set M.Element, (∀ other : M.Element, other.1 = sort →
        ssat (Γ := sort :: Γ) (env.extend closed) inner other → other ∈ closed) → element ∈ closed
  | Γ, env, .nu sort inner, element => element.1 = sort ∧
      ∃ invariant : Set M.Element, element ∈ invariant ∧
        ∀ other ∈ invariant, other.1 = sort ∧ ssat (Γ := sort :: Γ) (env.extend invariant) inner other
  | _, env, .possibly label formula, ⟨sort, element⟩ =>
      ∃ next, M.step element label next ∧ ssat env formula ⟨sort, next⟩
  | _, env, .necessarily label formula, ⟨sort, element⟩ =>
      ∀ next, M.step element label next → ssat env formula ⟨sort, next⟩
  | _, env, .sometimeBefore label formula, ⟨sort, element⟩ =>
      ∃ previous, M.step previous label element ∧ ssat env formula ⟨sort, previous⟩
  | _, env, .alwaysBefore label formula, ⟨sort, element⟩ =>
      ∀ previous, M.step previous label element → ssat env formula ⟨sort, previous⟩
  | _, env, .built constructor arguments, ⟨_, element⟩ =>
      ∃ parts, M.built element constructor parts ∧ ssatAll env arguments parts
  | _, env, .everyBuilt constructor arguments, ⟨_, element⟩ =>
      ∀ parts, M.built element constructor parts → ssatSome env arguments parts
  | _, env, .split kind left right, ⟨sort, element⟩ =>
      ∃ first second, M.split element kind first second ∧ ssat env left ⟨sort, first⟩ ∧ ssat env right ⟨sort, second⟩
  | _, env, .everySplit kind left right, ⟨sort, element⟩ =>
      ∀ first second, M.split element kind first second → ssat env left ⟨sort, first⟩ ∨ ssat env right ⟨sort, second⟩
  | _, _, .empty kind, ⟨_, element⟩ => M.empty element kind
  | _, _, .nonEmpty kind, ⟨_, element⟩ => ¬ M.empty element kind
  | _, env, .single kind memberSort formula, ⟨_, element⟩ =>
      ∃ member, M.single element kind member ∧ member.1 = memberSort ∧ ssat env formula member
  | _, env, .everySingle kind memberSort formula, ⟨_, element⟩ =>
      ∀ member, M.single element kind member → member.1 = memberSort → ssat env formula member
  | _, _, .is term, ⟨_, element⟩ => M.named element term
  | _, _, .isNot term, ⟨_, element⟩ => ¬ M.named element term
  | _, env, .someOf sort formula, _ => ∃ witness : M.Carrier sort, ssat env formula ⟨sort, witness⟩
  | _, env, .everyOf sort formula, _ => ∀ witness : M.Carrier sort, ssat env formula ⟨sort, witness⟩
  | _, _, .inRelation relation, ⟨_, element⟩ => M.inRelation element relation
  | _, _, .notInRelation relation, ⟨_, element⟩ => ¬ M.inRelation element relation

/-- Each argument formula holds at the corresponding part, which has its sort, and the lengths agree. -/
def ssatAll : {Γ : List Srt} → Env M.Element Γ.length → SFormulas Srt Γ → List M.Element → Prop
  | _, _, .nil, [] => True
  | _, env, .cons sort formula formulas, part :: parts =>
      part.1 = sort ∧ ssat env formula part ∧ ssatAll env formulas parts
  | _, _, _, _ => False

/-- Some argument formula holds at the corresponding part if it has its sort, or the lengths differ. -/
def ssatSome : {Γ : List Srt} → Env M.Element Γ.length → SFormulas Srt Γ → List M.Element → Prop
  | _, _, .nil, [] => False
  | _, env, .cons sort formula formulas, part :: parts =>
      (part.1 = sort → ssat env formula part) ∨ ssatSome env formulas parts
  | _, _, _, _ => True
end

end SortedStructure

/-! ## The sorted structure of a one-sorted structure -/

variable {Srt : Type} {Carrier : Type u} (T : NativeStructure Carrier) (toType : Srt → TypeExpr)

/-- **The sorted structure of a one-sorted structure**, given the type of each sort: the elements of a sort are the
elements typed at its type, related as the one-sorted structure relates them. -/
def restrict : SortedStructure.{u} Srt where
  Carrier sort := {element : Carrier // T.typed element (toType sort)}
  step first label second := T.step first.1 label second.1
  built element constructor parts := T.built element.1 constructor (parts.map fun part => part.2.1)
  split element kind first second := T.split element.1 kind first.1 second.1
  empty element kind := T.empty element.1 kind
  single element kind member := T.single element.1 kind member.2.1
  named element term := T.named element.1 term
  inRelation element relation := T.inRelation element.1 relation

/-! ## The guarded translation -/

mutual
/-- **The guarded translation** of a many-sorted formula at a sort, assuming the element has the sort: each position
is guarded by its sort. -/
def core [DecidableEq Srt] : {Γ : List Srt} → SFormula Srt Γ → Srt → Formula Γ.length
  | _, .top, _ => .top
  | _, .bot, _ => .bot
  | _, .and left right, sort => .and (core left sort) (core right sort)
  | _, .or left right, sort => .or (core left sort) (core right sort)
  | Γ, .var index, sort => if Γ.get index = sort then .var index else .bot
  | _, .mu bound inner, sort => if bound = sort then .mu (.and (.typed (toType sort)) (core inner sort)) else .bot
  | _, .nu bound inner, sort => if bound = sort then .nu (.and (.typed (toType sort)) (core inner sort)) else .bot
  | _, .possibly label formula, sort => .possibly label (.and (.typed (toType sort)) (core formula sort))
  | _, .necessarily label formula, sort => .necessarily label (.or (.untyped (toType sort)) (core formula sort))
  | _, .sometimeBefore label formula, sort => .sometimeBefore label (.and (.typed (toType sort)) (core formula sort))
  | _, .alwaysBefore label formula, sort => .alwaysBefore label (.or (.untyped (toType sort)) (core formula sort))
  | _, .built constructor arguments, _ => .built constructor (coreGuarded arguments)
  | _, .everyBuilt constructor arguments, _ => .everyBuilt constructor (coreUnguarded arguments)
  | _, .split kind left right, sort =>
      .split kind (.and (.typed (toType sort)) (core left sort)) (.and (.typed (toType sort)) (core right sort))
  | _, .everySplit kind left right, sort =>
      .everySplit kind (.or (.untyped (toType sort)) (core left sort)) (.or (.untyped (toType sort)) (core right sort))
  | _, .empty kind, _ => .empty kind
  | _, .nonEmpty kind, _ => .nonEmpty kind
  | _, .single kind memberSort formula, _ =>
      .single kind (.and (.typed (toType memberSort)) (core formula memberSort))
  | _, .everySingle kind memberSort formula, _ =>
      .everySingle kind (.or (.untyped (toType memberSort)) (core formula memberSort))
  | _, .is term, _ => .is term
  | _, .isNot term, _ => .isNot term
  | _, .someOf sort formula, _ => .someOf (toType sort) (core formula sort)
  | _, .everyOf sort formula, _ => .everyOf (toType sort) (core formula sort)
  | _, .inRelation relation, _ => .inRelation relation
  | _, .notInRelation relation, _ => .notInRelation relation

/-- Argument formulas, each guarded by its sort. -/
def coreGuarded [DecidableEq Srt] : {Γ : List Srt} → SFormulas Srt Γ → Formulas Γ.length
  | _, .nil => .nil
  | _, .cons sort formula formulas => .cons (.and (.typed (toType sort)) (core formula sort)) (coreGuarded formulas)

/-- Argument formulas, each read at the elements of its sort only. -/
def coreUnguarded [DecidableEq Srt] : {Γ : List Srt} → SFormulas Srt Γ → Formulas Γ.length
  | _, .nil => .nil
  | _, .cons sort formula formulas => .cons (.or (.untyped (toType sort)) (core formula sort)) (coreUnguarded formulas)
end

/-- **The translation of a many-sorted formula at a sort**: the element has the sort, and the guarded translation holds. -/
def guard [DecidableEq Srt] {Γ : List Srt} (formula : SFormula Srt Γ) (sort : Srt) : Formula Γ.length :=
  .and (.typed (toType sort)) (core toType formula sort)

/-! ## The reduction is exact -/

/-- **Corresponding environments**: a variable's one-sorted set and its sorted set agree on the elements of its sort. -/
def Corresponds {Γ : List Srt} (oneEnv : Env Carrier Γ.length) (env : Env (restrict T toType).Element Γ.length) : Prop :=
  ∀ index (element : (restrict T toType).Element), element.1 = Γ.get index → (element.2.1 ∈ oneEnv index ↔ element ∈ env index)

variable {T toType}

theorem Corresponds.extend {Γ : List Srt} {oneEnv : Env Carrier Γ.length} {env : Env (restrict T toType).Element Γ.length}
    (related : Corresponds T toType oneEnv env) (sort : Srt) {oneSet : Set Carrier} {set : Set (restrict T toType).Element}
    (agree : ∀ element : (restrict T toType).Element, element.1 = sort → (element.2.1 ∈ oneSet ↔ element ∈ set)) :
    Corresponds (Γ := sort :: Γ) T toType (oneEnv.extend oneSet) (env.extend set) := by
  intro index
  refine Fin.cases ?_ (fun index' => ?_) index
  · intro element sortIs
    simp only [Env.extend, Fin.cons_zero]
    exact agree element sortIs
  · intro element sortIs
    simp only [Env.extend, Fin.cons_succ]
    exact related index' element sortIs

/-- An element of a sort, from an element of the one-sorted carrier typed at it. -/
def lift (sort : Srt) (element : Carrier) (typed : T.typed element (toType sort)) : (restrict T toType).Element :=
  ⟨sort, element, typed⟩

theorem element_eta (element : (restrict T toType).Element) : element = lift element.1 element.2.1 element.2.2 := rfl

variable [DecidableEq Srt]

mutual
/-- **The guarded translation is exact**: in corresponding environments, a many-sorted formula holds at an element of a
sort exactly when its guarded translation holds at the element in the one-sorted structure. -/
theorem core_iff : ∀ {Γ : List Srt} (formula : SFormula Srt Γ) {oneEnv : Env Carrier Γ.length}
    {env : Env (restrict T toType).Element Γ.length}, Corresponds T toType oneEnv env → ∀ element : (restrict T toType).Element,
      ((restrict T toType).ssat env formula element ↔ T.sat oneEnv (core toType formula element.1) element.2.1)
  | _, .top, _, _, _, _ => Iff.rfl
  | _, .bot, _, _, _, _ => Iff.rfl
  | _, .and left right, _, _, related, element =>
    and_congr (core_iff left related element) (core_iff right related element)
  | _, .or left right, _, _, related, element =>
    or_congr (core_iff left related element) (core_iff right related element)
  | Γ, .var index, _, _, related, element => by
    show element.1 = Γ.get index ∧ element ∈ _ ↔ T.sat _ (if Γ.get index = element.1 then .var index else .bot) _
    by_cases same : Γ.get index = element.1
    · rw [if_pos same]
      exact ⟨fun ⟨_, member⟩ => (related index element same.symm).mpr member,
        fun member => ⟨same.symm, (related index element same.symm).mp member⟩⟩
    · rw [if_neg same]
      exact ⟨fun ⟨sortIs, _⟩ => same sortIs.symm, fun impossible => impossible.elim⟩
  | _, .mu bound inner, oneEnv, env, related, ⟨sort, element, typed⟩ => by
    show sort = bound ∧ _ ↔ T.sat _ (if bound = sort then _ else .bot) element
    by_cases same : bound = sort
    · subst same
      rw [if_pos rfl]
      constructor
      · rintro ⟨-, least⟩ oneSet closedUnder
        have agree : ∀ other : (restrict T toType).Element, other.1 = bound →
            (other.2.1 ∈ oneSet ↔ other ∈ {other : (restrict T toType).Element | other.2.1 ∈ oneSet}) :=
          fun _ _ => Iff.rfl
        refine least {other | other.2.1 ∈ oneSet} ?_
        rintro ⟨otherSort, other, otherTyped⟩ (sortIs : otherSort = bound) holds
        have sortIs' : bound = otherSort := sortIs.symm
        subst sortIs'
        exact closedUnder other ⟨otherTyped,
          (core_iff inner (related.extend bound agree) (lift bound other otherTyped)).mp holds⟩
      · intro least
        refine ⟨rfl, fun set closedUnder => ?_⟩
        let oneSet : Set Carrier := {other | ∃ typed : T.typed other (toType bound), lift bound other typed ∈ set}
        have agree : ∀ other : (restrict T toType).Element, other.1 = bound → (other.2.1 ∈ oneSet ↔ other ∈ set) := by
          rintro ⟨otherSort, other, otherTyped⟩ (sortIs : otherSort = bound)
          subst sortIs
          exact ⟨fun ⟨_, member⟩ => member, fun member => ⟨otherTyped, member⟩⟩
        obtain ⟨_, member⟩ := least oneSet fun other ⟨otherTyped, holds⟩ =>
          ⟨otherTyped, closedUnder (lift bound other otherTyped) rfl
            ((core_iff inner (related.extend bound agree) (lift bound other otherTyped)).mpr holds)⟩
        exact member
    · rw [if_neg same]
      exact ⟨fun ⟨sortIs, _⟩ => same sortIs.symm, fun impossible => impossible.elim⟩
  | _, .nu bound inner, oneEnv, env, related, ⟨sort, element, typed⟩ => by
    show sort = bound ∧ _ ↔ T.sat _ (if bound = sort then _ else .bot) element
    by_cases same : bound = sort
    · subst same
      rw [if_pos rfl]
      constructor
      · rintro ⟨-, set, member, preserved⟩
        let oneSet : Set Carrier := {other | ∃ typed : T.typed other (toType bound), lift bound other typed ∈ set}
        have agree : ∀ other : (restrict T toType).Element, other.1 = bound → (other.2.1 ∈ oneSet ↔ other ∈ set) := by
          rintro ⟨otherSort, other, otherTyped⟩ (sortIs : otherSort = bound)
          subst sortIs
          exact ⟨fun ⟨_, member⟩ => member, fun member => ⟨otherTyped, member⟩⟩
        refine ⟨oneSet, ⟨typed, member⟩, fun other ⟨otherTyped, otherMember⟩ => ⟨otherTyped, ?_⟩⟩
        exact (core_iff inner (related.extend bound agree) (lift bound other otherTyped)).mp
          (preserved _ otherMember).2
      · rintro ⟨oneSet, member, preserved⟩
        let set : Set (restrict T toType).Element := {other | other.1 = bound ∧ other.2.1 ∈ oneSet}
        have agree : ∀ other : (restrict T toType).Element, other.1 = bound → (other.2.1 ∈ oneSet ↔ other ∈ set) :=
          fun other sortIs => ⟨fun inside => ⟨sortIs, inside⟩, fun inside => inside.2⟩
        refine ⟨rfl, set, ⟨rfl, member⟩, ?_⟩
        rintro ⟨otherSort, other, otherTyped⟩ ⟨(sortIs : otherSort = bound), otherMember⟩
        refine ⟨sortIs, ?_⟩
        have sortIs' : bound = otherSort := sortIs.symm
        subst sortIs'
        obtain ⟨-, holds⟩ := preserved _ otherMember
        exact (core_iff inner (related.extend bound agree) (lift bound other otherTyped)).mpr holds
    · rw [if_neg same]
      exact ⟨fun ⟨sortIs, _⟩ => same sortIs.symm, fun impossible => impossible.elim⟩
  | _, .possibly label formula, _, _, related, ⟨sort, element, typed⟩ => by
    constructor
    · rintro ⟨⟨next, nextTyped⟩, step, holds⟩
      exact ⟨next, step, nextTyped, (core_iff formula related (lift sort next nextTyped)).mp holds⟩
    · rintro ⟨next, step, nextTyped, holds⟩
      exact ⟨⟨next, nextTyped⟩, step, (core_iff formula related (lift sort next nextTyped)).mpr holds⟩
  | _, .necessarily label formula, _, _, related, ⟨sort, element, typed⟩ => by
    constructor
    · intro every next step
      by_cases nextTyped : T.typed next (toType sort)
      · exact Or.inr ((core_iff formula related (lift sort next nextTyped)).mp (every ⟨next, nextTyped⟩ step))
      · exact Or.inl nextTyped
    · intro every next step
      rcases every next.1 step with untyped | holds
      · exact absurd next.2 untyped
      · exact (core_iff formula related (lift sort next.1 next.2)).mpr holds
  | _, .sometimeBefore label formula, _, _, related, ⟨sort, element, typed⟩ => by
    constructor
    · rintro ⟨⟨previous, previousTyped⟩, step, holds⟩
      exact ⟨previous, step, previousTyped, (core_iff formula related (lift sort previous previousTyped)).mp holds⟩
    · rintro ⟨previous, step, previousTyped, holds⟩
      exact ⟨⟨previous, previousTyped⟩, step, (core_iff formula related (lift sort previous previousTyped)).mpr holds⟩
  | _, .alwaysBefore label formula, _, _, related, ⟨sort, element, typed⟩ => by
    constructor
    · intro every previous step
      by_cases previousTyped : T.typed previous (toType sort)
      · exact Or.inr ((core_iff formula related (lift sort previous previousTyped)).mp
          (every ⟨previous, previousTyped⟩ step))
      · exact Or.inl previousTyped
    · intro every previous step
      rcases every previous.1 step with untyped | holds
      · exact absurd previous.2 untyped
      · exact (core_iff formula related (lift sort previous.1 previous.2)).mpr holds
  | _, .built constructor arguments, _, _, related, ⟨sort, element, typed⟩ => by
    constructor
    · rintro ⟨parts, isBuilt, all⟩
      exact ⟨_, isBuilt, (coreGuarded_iff arguments related _).mpr ⟨parts, rfl, all⟩⟩
    · rintro ⟨parts, isBuilt, all⟩
      obtain ⟨sorted, rfl, all'⟩ := (coreGuarded_iff arguments related parts).mp all
      exact ⟨sorted, isBuilt, all'⟩
  | _, .everyBuilt constructor arguments, _, _, related, ⟨sort, element, typed⟩ => by
    constructor
    · intro every parts isBuilt
      refine (coreUnguarded_iff arguments related parts).mpr fun sorted mapped => every sorted ?_
      show T.built element constructor (sorted.map fun part => part.2.1)
      rw [mapped]
      exact isBuilt
    · intro every sorted isBuilt
      exact (coreUnguarded_iff arguments related _).mp (every _ isBuilt) sorted rfl
  | _, .split kind left right, _, _, related, ⟨sort, element, typed⟩ => by
    constructor
    · rintro ⟨⟨first, firstTyped⟩, ⟨second, secondTyped⟩, isSplit, leftHolds, rightHolds⟩
      exact ⟨first, second, isSplit, ⟨firstTyped, (core_iff left related (lift sort first firstTyped)).mp leftHolds⟩,
        ⟨secondTyped, (core_iff right related (lift sort second secondTyped)).mp rightHolds⟩⟩
    · rintro ⟨first, second, isSplit, ⟨firstTyped, leftHolds⟩, ⟨secondTyped, rightHolds⟩⟩
      exact ⟨⟨first, firstTyped⟩, ⟨second, secondTyped⟩, isSplit,
        (core_iff left related (lift sort first firstTyped)).mpr leftHolds,
        (core_iff right related (lift sort second secondTyped)).mpr rightHolds⟩
  | _, .everySplit kind left right, _, _, related, ⟨sort, element, typed⟩ => by
    constructor
    · intro every first second isSplit
      by_cases firstTyped : T.typed first (toType sort)
      · by_cases secondTyped : T.typed second (toType sort)
        · rcases every ⟨first, firstTyped⟩ ⟨second, secondTyped⟩ isSplit with leftHolds | rightHolds
          · exact Or.inl (Or.inr ((core_iff left related (lift sort first firstTyped)).mp leftHolds))
          · exact Or.inr (Or.inr ((core_iff right related (lift sort second secondTyped)).mp rightHolds))
        · exact Or.inr (Or.inl secondTyped)
      · exact Or.inl (Or.inl firstTyped)
    · intro every first second isSplit
      rcases every first.1 second.1 isSplit with (untyped | leftHolds) | (untyped | rightHolds)
      · exact absurd first.2 untyped
      · exact Or.inl ((core_iff left related (lift sort first.1 first.2)).mpr leftHolds)
      · exact absurd second.2 untyped
      · exact Or.inr ((core_iff right related (lift sort second.1 second.2)).mpr rightHolds)
  | _, .empty _, _, _, _, ⟨_, _, _⟩ => Iff.rfl
  | _, .nonEmpty _, _, _, _, ⟨_, _, _⟩ => Iff.rfl
  | _, .single kind memberSort formula, _, _, related, ⟨sort, element, typed⟩ => by
    constructor
    · rintro ⟨⟨memberSort', member, memberTyped⟩, isSingle, (sortIs : memberSort' = memberSort), holds⟩
      subst sortIs
      exact ⟨member, isSingle, memberTyped, (core_iff formula related (lift memberSort' member memberTyped)).mp holds⟩
    · rintro ⟨member, isSingle, memberTyped, holds⟩
      exact ⟨lift memberSort member memberTyped, isSingle, rfl,
        (core_iff formula related (lift memberSort member memberTyped)).mpr holds⟩
  | _, .everySingle kind memberSort formula, _, _, related, ⟨sort, element, typed⟩ => by
    constructor
    · intro every member isSingle
      by_cases memberTyped : T.typed member (toType memberSort)
      · exact Or.inr ((core_iff formula related (lift memberSort member memberTyped)).mp
          (every (lift memberSort member memberTyped) isSingle rfl))
      · exact Or.inl memberTyped
    · rintro every ⟨memberSort', member, memberTyped⟩ isSingle (sortIs : memberSort' = memberSort)
      subst sortIs
      rcases every member isSingle with untyped | holds
      · exact absurd memberTyped untyped
      · exact (core_iff formula related (lift memberSort' member memberTyped)).mpr holds
  | _, .is _, _, _, _, ⟨_, _, _⟩ => Iff.rfl
  | _, .isNot _, _, _, _, ⟨_, _, _⟩ => Iff.rfl
  | _, .someOf witnessSort formula, _, _, related, _ => by
    constructor
    · rintro ⟨⟨witness, witnessTyped⟩, holds⟩
      exact ⟨witness, witnessTyped, (core_iff formula related (lift witnessSort witness witnessTyped)).mp holds⟩
    · rintro ⟨witness, witnessTyped, holds⟩
      exact ⟨⟨witness, witnessTyped⟩, (core_iff formula related (lift witnessSort witness witnessTyped)).mpr holds⟩
  | _, .everyOf witnessSort formula, _, _, related, _ => by
    constructor
    · intro every witness witnessTyped
      exact (core_iff formula related (lift witnessSort witness witnessTyped)).mp (every ⟨witness, witnessTyped⟩)
    · intro every witness
      exact (core_iff formula related (lift witnessSort witness.1 witness.2)).mpr (every witness.1 witness.2)
  | _, .inRelation _, _, _, _, ⟨_, _, _⟩ => Iff.rfl
  | _, .notInRelation _, _, _, _, ⟨_, _, _⟩ => Iff.rfl

/-- The guarded argument formulas hold at a list of elements exactly when, read at some sorts for them, the sorted
argument formulas do. -/
theorem coreGuarded_iff : ∀ {Γ : List Srt} (arguments : SFormulas Srt Γ) {oneEnv : Env Carrier Γ.length}
    {env : Env (restrict T toType).Element Γ.length}, Corresponds T toType oneEnv env → ∀ parts : List Carrier,
      (T.satAll oneEnv (coreGuarded toType arguments) parts ↔
        ∃ sorted : List (restrict T toType).Element, sorted.map (fun part => part.2.1) = parts ∧
          (restrict T toType).ssatAll env arguments sorted)
  | _, .nil, _, _, _, [] => ⟨fun _ => ⟨[], rfl, trivial⟩, fun _ => trivial⟩
  | _, .nil, _, _, _, _ :: _ => ⟨fun impossible => impossible.elim, by
      rintro ⟨_ | ⟨_, _⟩, mapped, all⟩
      · cases mapped
      · exact all.elim⟩
  | _, .cons _ _ _, _, _, _, [] => ⟨fun impossible => impossible.elim, by
      rintro ⟨_ | ⟨_, _⟩, mapped, all⟩
      · exact all.elim
      · cases mapped⟩
  | _, .cons sort formula formulas, _, _, related, part :: parts => by
    constructor
    · rintro ⟨⟨partTyped, holds⟩, rest⟩
      obtain ⟨sorted, mapped, restAll⟩ := (coreGuarded_iff formulas related parts).mp rest
      exact ⟨lift sort part partTyped :: sorted, by rw [List.map_cons, mapped]; rfl,
        rfl, (core_iff formula related (lift sort part partTyped)).mpr holds, restAll⟩
    · rintro ⟨_ | ⟨⟨partSort, part', partTyped⟩, sorted⟩, mapped, all⟩
      · cases mapped
      · simp only [List.map_cons, List.cons.injEq] at mapped
        obtain ⟨rfl, mapped⟩ := mapped
        obtain ⟨(sortIs : partSort = sort), holds, restAll⟩ := all
        subst sortIs
        exact ⟨⟨partTyped, (core_iff formula related (lift partSort part' partTyped)).mp holds⟩,
          (coreGuarded_iff formulas related parts).mpr ⟨sorted, mapped, restAll⟩⟩

/-- The argument formulas read at their sorts hold somewhere along a list of elements exactly when, at every reading of
them at sorts, some sorted argument formula does. -/
theorem coreUnguarded_iff : ∀ {Γ : List Srt} (arguments : SFormulas Srt Γ) {oneEnv : Env Carrier Γ.length}
    {env : Env (restrict T toType).Element Γ.length}, Corresponds T toType oneEnv env → ∀ parts : List Carrier,
      (T.satSome oneEnv (coreUnguarded toType arguments) parts ↔
        ∀ sorted : List (restrict T toType).Element, sorted.map (fun part => part.2.1) = parts →
          (restrict T toType).ssatSome env arguments sorted)
  | _, .nil, _, _, _, [] => ⟨fun impossible => impossible.elim, fun every => every [] rfl⟩
  | _, .nil, _, _, _, _ :: _ => ⟨fun _ sorted mapped => (by
      cases sorted with
      | nil => cases mapped
      | cons _ _ => trivial), fun _ => trivial⟩
  | _, .cons _ _ _, _, _, _, [] => ⟨fun _ sorted mapped => (by
      cases sorted with
      | nil => trivial
      | cons _ _ => cases mapped), fun _ => trivial⟩
  | _, .cons sort formula formulas, oneEnv, _, related, part :: parts => by
    constructor
    · rintro (here | later) sorted mapped
      · cases sorted with
        | nil => cases mapped
        | cons first sorted =>
          simp only [List.map_cons, List.cons.injEq] at mapped
          obtain ⟨partIs, -⟩ := mapped
          refine Or.inl fun (sortIs : first.1 = sort) => ?_
          obtain ⟨firstSort, first', firstTyped⟩ := first
          simp only at partIs sortIs
          subst partIs sortIs
          rcases here with untyped | holds
          · exact absurd firstTyped untyped
          · exact (core_iff formula related (lift firstSort first' firstTyped)).mpr holds
      · cases sorted with
        | nil => cases mapped
        | cons first sorted =>
          simp only [List.map_cons, List.cons.injEq] at mapped
          exact Or.inr ((coreUnguarded_iff formulas related parts).mp later sorted mapped.2)
    · intro every
      by_cases partTyped : T.typed part (toType sort)
      · by_cases holds : T.sat oneEnv (core toType formula sort) part
        · exact Or.inl (Or.inr holds)
        · refine Or.inr ((coreUnguarded_iff formulas related parts).mpr fun sorted mapped => ?_)
          rcases every (lift sort part partTyped :: sorted) (by rw [List.map_cons, mapped]; rfl) with here | later
          · exact absurd ((core_iff formula related (lift sort part partTyped)).mp (here rfl)) holds
          · exact later
      · exact Or.inl (Or.inl partTyped)
end

/-- **The translation at a sort holds exactly at the elements of the sort where the formula holds.** -/
theorem guard_iff {Γ : List Srt} (formula : SFormula Srt Γ) {oneEnv : Env Carrier Γ.length}
    {env : Env (restrict T toType).Element Γ.length} (related : Corresponds T toType oneEnv env) (sort : Srt) (element : Carrier) :
    T.sat oneEnv (guard toType formula sort) element ↔
      ∃ typed : T.typed element (toType sort), (restrict T toType).ssat env formula (lift sort element typed) := by
  constructor
  · rintro ⟨typed, holds⟩
    exact ⟨typed, (core_iff formula related (lift sort element typed)).mpr holds⟩
  · rintro ⟨typed, holds⟩
    exact ⟨typed, (core_iff formula related (lift sort element typed)).mp holds⟩

/-- **For closed formulas**: the translation at a sort holds at an element exactly when the element has the sort and
the formula holds there. -/
theorem guard_iff_closed (formula : SFormula Srt []) (sort : Srt) (element : Carrier) :
    T.sat Env.closed (guard toType formula sort) element ↔
      ∃ typed : T.typed element (toType sort), (restrict T toType).ssat Env.closed formula (lift sort element typed) :=
  guard_iff formula (fun index => index.elim0) sort element

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySorted
