import Mettapedia.OSLF.MeTTaIL.DerivedContexts
import Mettapedia.OSLF.MeTTaIL.PatternLexOrder
import Mathlib.Data.List.InsertIdx
import Mathlib.Data.List.Perm.Basic
import Mettapedia.OSLF.MeTTaIL.CollectionLaws
import Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
import Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution
import Mettapedia.OSLF.MeTTaIL.SetFree

/-!
# Canonical bags

A bag constructor's carrier is unordered: its terms are multisets, and the order in which a
collection lists its elements carries no meaning. A set constructor's carrier is unordered and
without repetition: its terms are finite sets, and how often a collection lists an element
carries no meaning either. `canon` chooses one presentation: bottom up, the elements of every
unordered collection are sorted by the injective structural serialization
(`PatternLexOrder.sortLex`, the order a MeTTa runtime evaluates), a set's repetitions are
removed, and vectors keep their order (`arrange`).

`BagStep` permutes the elements of one bag, or re-presents one set by any list of the same
elements, in any context: under constructors, binders, substitution nodes and inside other
collections. The congruence it generates is exactly equality of canonical forms:

- `canon_iff`: `canon p = canon q` exactly when `p` and `q` are related by finitely many
  such steps (`Relation.EqvGen BagStep`);
- `canon_idempotent`: a canonical form is canonical;
- `canon_freeFvarNames`: canonical forms keep their free names.

Negative control: a vector is never reordered (`vec_not_reordered`).

## Matching modulo permutation

Repeated metavariables compared by `canonCompare` (equal canonical forms) make matching
invariant under permutation (`matchAtWith_same`): on subjects with equal canonical forms, every
match has a counterpart whose captures are pairwise permutation-equal (`AssignSame`), for
patterns that decompose no set (`setFree`). The literal comparison does not have this property:
a recovered value may be lowered out of binders, and lowering can unsort a canonical bag, so two
presentations of one multiset can compare unequal. A pattern that decomposes a set does not have
it either: a bag match of `{X, Y}` against the presentation `{a, a}` has no counterpart at `{a}`,
so matching inside sets is a separate matter from their canonical forms.

## Permutations commute with capture

A permutation commutes with the operations a capture performs on its target: context
substitution maps it to a permutation (`BagStep.substitute`), scoping is unchanged
(`BagStep.wellScoped`), and an exact round trip `substitute τ (substitute σ t) = t` holds for a
term exactly when it holds for its permutation (`BagStep.roundTrip`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags

open Syntax PatternLexOrder

/-- Collections whose element order carries no meaning. -/
def Unordered : CollType → Bool
  | .vec => false
  | .hashBag => true
  | .hashSet => true

/-- A bag's elements in canonical order, a set's in canonical order without repetition, a
vector's as listed. -/
def arrange (kind : CollType) (elements : List Pattern) : List Pattern :=
  match kind with
  | .vec => elements
  | .hashBag => sortLex elements
  | .hashSet => (sortLex elements).dedup

theorem arrange_vec (elements : List Pattern) : arrange .vec elements = elements := rfl
theorem arrange_bag (elements : List Pattern) : arrange .hashBag elements = sortLex elements := rfl
theorem arrange_set (elements : List Pattern) : arrange .hashSet elements = (sortLex elements).dedup := rfl

/-- What a collection kind forgets about its elements' list: nothing for a vector, the order for
a bag, the order and the repetitions for a set. -/
def Presents : CollType → List Pattern → List Pattern → Prop
  | .vec, left, right => left = right
  | .hashBag, left, right => left.Perm right
  | .hashSet, left, right => ∀ a, a ∈ left ↔ a ∈ right

theorem members_map {left right : List Pattern} (same : ∀ a, a ∈ left ↔ a ∈ right) (f : Pattern → Pattern) :
    ∀ a, a ∈ left.map f ↔ a ∈ right.map f := fun a => by
  simp only [List.mem_map]
  exact ⟨fun ⟨b, member, image⟩ => ⟨b, (same b).mp member, image⟩,
    fun ⟨b, member, image⟩ => ⟨b, (same b).mpr member, image⟩⟩

theorem members_flatMap {left right : List Pattern} (same : ∀ a, a ∈ left ↔ a ∈ right) (f : Pattern → List Pattern) :
    ∀ a, a ∈ left.flatMap f ↔ a ∈ right.flatMap f := fun a => by
  simp only [List.mem_flatMap]
  exact ⟨fun ⟨b, member, inside⟩ => ⟨b, (same b).mp member, inside⟩,
    fun ⟨b, member, inside⟩ => ⟨b, (same b).mpr member, inside⟩⟩

theorem Presents.map {kind : CollType} {left right : List Pattern} (presents : Presents kind left right)
    (f : Pattern → Pattern) : Presents kind (left.map f) (right.map f) := by
  cases kind with
  | vec => exact congrArg (List.map f) presents
  | hashBag => exact List.Perm.map f presents
  | hashSet => exact members_map presents f

theorem Presents.mem {kind : CollType} {left right : List Pattern} (presents : Presents kind left right) :
    ∀ a, a ∈ left ↔ a ∈ right := by
  cases kind with
  | vec => intro a; rw [presents]
  | hashBag => exact fun a => presents.mem_iff
  | hashSet => exact presents

theorem presents_of_perm {kind : CollType} (unordered : Unordered kind = true) {left right : List Pattern}
    (permutation : left.Perm right) : Presents kind left right := by
  cases kind with
  | vec => simp [Unordered] at unordered
  | hashBag => exact permutation
  | hashSet => exact fun a => permutation.mem_iff

/-- **Arranging forgets exactly what the kind forgets.** -/
theorem arrange_eq_of_presents {kind : CollType} {left right : List Pattern} (presents : Presents kind left right) :
    arrange kind left = arrange kind right := by
  cases kind with
  | vec => exact presents
  | hashBag => exact sortLex_eq_of_perm presents
  | hashSet =>
    show (sortLex left).dedup = (sortLex right).dedup
    refine List.Perm.eq_of_pairwise' ((sortLex_pairwise left).sublist (List.dedup_sublist _))
      ((sortLex_pairwise right).sublist (List.dedup_sublist _)) ?_
    rw [List.perm_ext_iff_of_nodup (List.nodup_dedup _) (List.nodup_dedup _)]
    intro a
    rw [List.mem_dedup, List.mem_dedup, (sortLex_perm left).mem_iff, (sortLex_perm right).mem_iff]
    exact presents a

theorem presents_of_arrange_eq {kind : CollType} {left right : List Pattern} (same : arrange kind left = arrange kind right) :
    Presents kind left right := by
  cases kind with
  | vec => exact same
  | hashBag =>
    exact (sortLex_perm left).symm.trans ((show sortLex left = sortLex right from same) ▸ sortLex_perm right)
  | hashSet =>
    intro a
    exact ((List.mem_dedup.trans (sortLex_perm left).mem_iff).symm.trans (Iff.of_eq (congrArg (a ∈ ·) same))).trans
      (List.mem_dedup.trans (sortLex_perm right).mem_iff)

theorem arrange_mem {kind : CollType} {elements : List Pattern} (a : Pattern) : a ∈ arrange kind elements ↔ a ∈ elements := by
  cases kind with
  | vec => exact Iff.rfl
  | hashBag => exact (sortLex_perm elements).mem_iff
  | hashSet => exact List.mem_dedup.trans (sortLex_perm elements).mem_iff

theorem Presents.of_eq {kind : CollType} {left right : List Pattern} (same : left = right) : Presents kind left right := by
  cases kind with
  | vec => exact same
  | hashBag => exact same ▸ List.Perm.refl _
  | hashSet => exact fun a => by rw [same]

theorem Presents.refl (kind : CollType) (elements : List Pattern) : Presents kind elements elements := Presents.of_eq rfl

theorem presents_eq_of_ordered {kind : CollType} (ordered : Unordered kind = false) {left right : List Pattern}
    (presents : Presents kind left right) : left = right := by
  cases kind with
  | vec => exact presents
  | hashBag => simp [Unordered] at ordered
  | hashSet => simp [Unordered] at ordered

/-- Presenting alike survives the same surroundings. -/
theorem Presents.surround {kind : CollType} (before after : List Pattern) {left right : List Pattern}
    (presents : Presents kind left right) : Presents kind (before ++ (left ++ after)) (before ++ (right ++ after)) := by
  cases kind with
  | vec => rw [presents]; exact rfl
  | hashBag => exact List.Perm.append_left _ (List.Perm.append_right _ presents)
  | hashSet => intro a; simp only [List.mem_append]; exact or_congr Iff.rfl (or_congr (presents a) Iff.rfl)

/-- **The canonical presentation**: every unordered collection sorted, bottom up. -/
def canon : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply label arguments => .apply label (arguments.map canon)
  | .lambda binder body => .lambda binder (canon body)
  | .multiLambda arity binders body => .multiLambda arity binders (canon body)
  | .subst body replacement => .subst (canon body) (canon replacement)
  | .collection kind elements rest => .collection kind (arrange kind (elements.map canon)) rest
decreasing_by all_goals sizeOf_pattern_dec

/-- One permutation of an unordered collection's elements, or one re-presentation of a set by a
list of the same elements, in any context. -/
inductive BagStep : Pattern → Pattern → Prop where
  | permute {kind : CollType} {elements permuted : List Pattern} {rest : Option String} :
      Unordered kind = true → elements.Perm permuted →
      BagStep (.collection kind elements rest) (.collection kind permuted rest)
  | members {elements others : List Pattern} {rest : Option String} :
      (∀ a, a ∈ elements ↔ a ∈ others) →
      BagStep (.collection .hashSet elements rest) (.collection .hashSet others rest)
  | apply {label : String} {before after : List Pattern} {argument changed : Pattern} :
      BagStep argument changed →
      BagStep (.apply label (before ++ argument :: after)) (.apply label (before ++ changed :: after))
  | lambda {binder : Option String} {body changed : Pattern} :
      BagStep body changed → BagStep (.lambda binder body) (.lambda binder changed)
  | multiLambda {arity : Nat} {binders : List String} {body changed : Pattern} :
      BagStep body changed → BagStep (.multiLambda arity binders body) (.multiLambda arity binders changed)
  | substBody {body changed replacement : Pattern} :
      BagStep body changed → BagStep (.subst body replacement) (.subst changed replacement)
  | substReplacement {body replacement changed : Pattern} :
      BagStep replacement changed → BagStep (.subst body replacement) (.subst body changed)
  | element {kind : CollType} {before after : List Pattern} {element changed : Pattern} {rest : Option String} :
      BagStep element changed →
      BagStep (.collection kind (before ++ element :: after) rest) (.collection kind (before ++ changed :: after) rest)

/-- An intrinsic collection step remains an intrinsic step in every
structural one-hole context. Contextual execution authority is separate. -/
theorem BagStep.fill (context : DerivedContexts.OneHoleContext) {left right : Pattern}
    (step : BagStep left right) : BagStep (context.fill left) (context.fill right) := by
  induction context with
  | hole => exact step
  | apply _ _ _ _ ih => exact .apply ih
  | lambda _ _ ih => exact .lambda ih
  | multiLambda _ _ _ ih => exact .multiLambda ih
  | substBody _ _ ih => exact .substBody ih
  | substReplacement _ _ ih => exact .substReplacement ih
  | collection _ _ _ _ _ ih => exact .element ih

#print axioms BagStep.fill

/-! ## Permutations keep the canonical form -/

theorem arrange_perm {kind : CollType} (unordered : Unordered kind = true) {left right : List Pattern}
    (permutation : left.Perm right) : arrange kind left = arrange kind right :=
  arrange_eq_of_presents (presents_of_perm unordered permutation)

theorem canon_collection (kind : CollType) (elements : List Pattern) (rest : Option String) :
    canon (.collection kind elements rest) = .collection kind (arrange kind (elements.map canon)) rest := by
  rw [canon]

theorem canon_apply (label : String) (arguments : List Pattern) :
    canon (.apply label arguments) = .apply label (arguments.map canon) := by
  rw [canon]

/-- **One step keeps the canonical form.** -/
theorem BagStep.canon_eq {left right : Pattern} (step : BagStep left right) : canon left = canon right := by
  induction step with
  | permute unordered permutation =>
    rw [canon_collection, canon_collection, arrange_perm unordered (permutation.map canon)]
  | members same =>
    rw [canon_collection, canon_collection, arrange_eq_of_presents (kind := .hashSet) (members_map same canon)]
  | apply _ ih => simp only [canon_apply, List.map_append, List.map_cons, ih]
  | lambda _ ih => simp only [canon, ih]
  | multiLambda _ ih => simp only [canon, ih]
  | substBody _ ih => simp only [canon, ih]
  | substReplacement _ ih => simp only [canon, ih]
  | element _ ih => simp only [canon_collection, List.map_append, List.map_cons, ih]

theorem eqvGen_canon_eq {left right : Pattern} (related : Relation.EqvGen BagStep left right) :
    canon left = canon right := by
  induction related with
  | rel _ _ step => exact step.canon_eq
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-! ## Every term reaches its canonical form by permutations -/

private theorem lift {f : Pattern → Pattern} (step : ∀ {a b : Pattern}, BagStep a b → BagStep (f a) (f b))
    {a b : Pattern} (related : Relation.EqvGen BagStep a b) : Relation.EqvGen BagStep (f a) (f b) := by
  induction related with
  | rel _ _ inner => exact .rel _ _ (step inner)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-- Relate a list to its image element by element, inside any list context. -/
private theorem along (wrap : List Pattern → Pattern)
    (inside : ∀ (before after : List Pattern) {a b : Pattern}, BagStep a b →
      BagStep (wrap (before ++ a :: after)) (wrap (before ++ b :: after))) :
    ∀ (before items : List Pattern), (∀ item ∈ items, Relation.EqvGen BagStep item (canon item)) →
      Relation.EqvGen BagStep (wrap (before ++ items)) (wrap (before ++ items.map canon))
  | before, [], _ => by simpa using Relation.EqvGen.refl _
  | before, item :: rest, each => by
    have first : Relation.EqvGen BagStep (wrap (before ++ item :: rest)) (wrap (before ++ canon item :: rest)) :=
      lift (f := fun x => wrap (before ++ x :: rest)) (fun step => inside before rest step) (each item (by simp))
    have later := along wrap inside (before ++ [canon item]) rest (fun other member => each other (by simp [member]))
    simp only [List.append_assoc, List.singleton_append] at later
    simp only [List.map_cons]
    exact .trans _ _ _ first later

/-- **Every term is related to its canonical form by permutations.** -/
theorem to_canon : ∀ pattern : Pattern, Relation.EqvGen BagStep pattern (canon pattern)
  | .bvar index => by rw [canon]; exact .refl _
  | .fvar name => by rw [canon]; exact .refl _
  | .apply label arguments => by
    rw [canon_apply]
    have each : ∀ item ∈ arguments, Relation.EqvGen BagStep item (canon item) := fun item member =>
      have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
      to_canon item
    simpa using along (fun items => .apply label items) (fun before after _ _ step => .apply step) [] arguments each
  | .lambda binder body => by
    rw [canon]; exact lift (f := .lambda binder) (fun step => .lambda step) (to_canon body)
  | .multiLambda arity binders body => by
    rw [canon]; exact lift (f := .multiLambda arity binders) (fun step => .multiLambda step) (to_canon body)
  | .subst body replacement => by
    rw [canon]
    exact .trans _ _ _ (lift (f := fun x => .subst x replacement) (fun step => .substBody step) (to_canon body))
      (lift (f := fun x => .subst (canon body) x) (fun step => .substReplacement step) (to_canon replacement))
  | .collection kind elements rest => by
    rw [canon_collection]
    have each : ∀ item ∈ elements, Relation.EqvGen BagStep item (canon item) := fun item member =>
      have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
      to_canon item
    have mapped : Relation.EqvGen BagStep (.collection kind elements rest)
        (.collection kind (elements.map canon) rest) := by
      simpa using along (fun items => .collection kind items rest) (fun before after _ _ step => .element step) []
        elements each
    cases kind with
    | vec => simpa [arrange_vec] using mapped
    | hashBag => exact .trans _ _ _ mapped (.rel _ _ (.permute rfl (sortLex_perm _).symm))
    | hashSet =>
      exact .trans _ _ _ mapped (.rel _ _ (.members fun a =>
        (List.mem_dedup.trans (sortLex_perm _).mem_iff).symm))
termination_by pattern => sizeOf pattern

/-- **Canonical forms decide the congruence generated by permutations and set re-presentations.** -/
theorem canon_iff (left right : Pattern) :
    canon left = canon right ↔ Relation.EqvGen BagStep left right := by
  constructor
  · intro same
    have toRight := to_canon right
    rw [← same] at toRight
    exact .trans _ _ _ (to_canon left) (.symm _ _ toRight)
  · exact eqvGen_canon_eq

/-- **A canonical form is canonical.** -/
theorem canon_idempotent (pattern : Pattern) : canon (canon pattern) = canon pattern :=
  eqvGen_canon_eq (.symm _ _ (to_canon pattern))

/-! ## Canonical forms keep free names -/

theorem BagStep.freeFvarNames_mem {left right : Pattern} (step : BagStep left right) (name : String) :
    name ∈ left.freeFvarNames ↔ name ∈ right.freeFvarNames := by
  induction step with
  | permute _ permutation =>
    simp only [Pattern.freeFvarNames, List.mem_append, List.mem_flatMap]
    constructor <;> rintro (⟨item, member, inside⟩ | inRest)
    · exact .inl ⟨item, permutation.subset member, inside⟩
    · exact .inr inRest
    · exact .inl ⟨item, permutation.symm.subset member, inside⟩
    · exact .inr inRest
  | members same =>
    simp only [Pattern.freeFvarNames, List.mem_append, List.mem_flatMap]
    constructor <;> rintro (⟨item, member, inside⟩ | inRest)
    · exact .inl ⟨item, (same item).mp member, inside⟩
    · exact .inr inRest
    · exact .inl ⟨item, (same item).mpr member, inside⟩
    · exact .inr inRest
  | apply _ ih => simp [Pattern.freeFvarNames, List.mem_flatMap, ih]
  | lambda _ ih => simp [Pattern.freeFvarNames, ih]
  | multiLambda _ ih => simp [Pattern.freeFvarNames, ih]
  | substBody _ ih => simp [Pattern.freeFvarNames, ih]
  | substReplacement _ ih => simp [Pattern.freeFvarNames, ih]
  | element _ ih => simp [Pattern.freeFvarNames, List.mem_flatMap, ih]

/-- **Canonical forms keep their free names.** -/
theorem canon_freeFvarNames (pattern : Pattern) (name : String) :
    name ∈ (canon pattern).freeFvarNames ↔ name ∈ pattern.freeFvarNames := by
  suffices keep : ∀ {a b : Pattern}, Relation.EqvGen BagStep a b → (name ∈ a.freeFvarNames ↔ name ∈ b.freeFvarNames) from
    (keep (to_canon pattern)).symm
  intro a b related
  induction related with
  | rel _ _ step => exact step.freeFvarNames_mem name
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-! ## Controls -/

/-- Two presentations of one bag have one canonical form. -/
example : canon (.collection .hashBag [.fvar "b", .fvar "a"] none) =
    canon (.collection .hashBag [.fvar "a", .fvar "b"] none) :=
  (canon_iff _ _).mpr (.rel _ _ (.permute rfl (List.Perm.swap _ _ [])))

/-- A set holding an element twice and the set holding it once have one canonical form. -/
example : canon (.collection .hashSet [.bvar 0, .bvar 0] none) = canon (.collection .hashSet [.bvar 0] none) :=
  (canon_iff _ _).mpr (.rel _ _ (.members fun _ => by simp))

/-- Negative control: a bag keeps how often it holds an element. -/
theorem bag_keeps_repetition : canon (.collection .hashBag [.bvar 0, .bvar 0] none) ≠
    canon (.collection .hashBag [.bvar 0] none) := by
  intro same
  rw [canon_collection, canon_collection] at same
  have lengths := congrArg List.length (Pattern.collection.inj same).2.1
  simp [arrange_bag, (sortLex_perm _).length_eq] at lengths

/-- Negative control: a vector is never reordered. -/
theorem vec_not_reordered : canon (.collection .vec [.fvar "b", .fvar "a"] none) ≠
    canon (.collection .vec [.fvar "a", .fvar "b"] none) := by
  simp [canon, arrange]

/-! ## Permutations commute with capture -/

section Capture

open RuleBinding

/-- **Context substitution maps a permutation to a permutation.** -/
theorem BagStep.substitute {left right : Pattern} (step : BagStep left right) :
    ∀ assignment : ContextSubstitution.Assignment,
      BagStep (ContextSubstitution.substitute assignment left) (ContextSubstitution.substitute assignment right) := by
  induction step with
  | permute unordered permutation =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    exact .permute unordered (permutation.map _)
  | members same =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    exact .members (members_map same _)
  | apply _ ih =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_append,
      List.map_cons]
    exact .apply (ih assignment)
  | lambda _ ih => intro assignment; simp only [ContextSubstitution.substitute]; exact .lambda (ih _)
  | multiLambda _ ih => intro assignment; simp only [ContextSubstitution.substitute]; exact .multiLambda (ih _)
  | substBody _ ih => intro assignment; simp only [ContextSubstitution.substitute]; exact .substBody (ih _)
  | substReplacement _ ih =>
    intro assignment; simp only [ContextSubstitution.substitute]; exact .substReplacement (ih _)
  | element _ ih =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_append,
      List.map_cons]
    exact .element (ih assignment)

private theorem wellScopedList_eq_all (depth : Nat) :
    ∀ items : List Pattern, Pattern.isWellScopedListAt depth items = items.all (Pattern.isWellScopedAt depth)
  | [] => rfl
  | item :: rest => by simp [Pattern.isWellScopedListAt, wellScopedList_eq_all depth rest]

/-- **Scoping is unchanged by a permutation.** -/
theorem BagStep.wellScoped {left right : Pattern} (step : BagStep left right) :
    ∀ depth, left.isWellScopedAt depth = right.isWellScopedAt depth := by
  induction step with
  | permute _ permutation =>
    intro depth
    simp only [Pattern.isWellScopedAt, wellScopedList_eq_all]
    exact Bool.eq_iff_iff.mpr (by simp only [List.all_eq_true]; exact ⟨fun h x m => h x (permutation.symm.subset m),
      fun h x m => h x (permutation.subset m)⟩)
  | members same =>
    intro depth
    simp only [Pattern.isWellScopedAt, wellScopedList_eq_all]
    exact Bool.eq_iff_iff.mpr (by simp only [List.all_eq_true]; exact ⟨fun h x m => h x ((same x).mpr m),
      fun h x m => h x ((same x).mp m)⟩)
  | apply _ ih =>
    intro depth
    simp only [Pattern.isWellScopedAt, wellScopedList_eq_all, List.all_append, List.all_cons, ih depth]
  | lambda _ ih => intro depth; simp only [Pattern.isWellScopedAt, ih]
  | multiLambda _ ih => intro depth; simp only [Pattern.isWellScopedAt, ih]
  | substBody _ ih => intro depth; simp only [Pattern.isWellScopedAt, ih]
  | substReplacement _ ih => intro depth; simp only [Pattern.isWellScopedAt, ih]
  | element _ ih =>
    intro depth
    simp only [Pattern.isWellScopedAt, wellScopedList_eq_all, List.all_append, List.all_cons, ih depth]

private theorem map_eq_self_iff {f : Pattern → Pattern} {items : List Pattern} :
    items.map f = items ↔ ∀ item ∈ items, f item = item := by
  induction items with
  | nil => simp
  | cons head tail ih => simp [ih]

private theorem map_middle_eq (f : Pattern → Pattern) (before after : List Pattern) (x y : Pattern) :
    before.map f ++ x :: after.map f = before ++ y :: after ↔
      before.map f = before ∧ x = y ∧ after.map f = after := by
  constructor
  · intro same
    obtain ⟨first, rest⟩ := List.append_inj same (by simp)
    simp only [List.cons.injEq] at rest
    exact ⟨first, rest.1, rest.2⟩
  · rintro ⟨first, rfl, rest⟩
    rw [first, rest]

/-- **An exact round trip holds for a term exactly when it holds for its permutation.** -/
theorem BagStep.roundTrip {left right : Pattern} (step : BagStep left right) :
    ∀ first second : ContextSubstitution.Assignment,
      ContextSubstitution.substitute second (ContextSubstitution.substitute first left) = left ↔
        ContextSubstitution.substitute second (ContextSubstitution.substitute first right) = right := by
  induction step with
  | permute _ permutation =>
    intro first second
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_map,
      Pattern.collection.injEq, true_and, and_true, map_eq_self_iff, Function.comp_apply]
    exact ⟨fun h x m => h x (permutation.symm.subset m), fun h x m => h x (permutation.subset m)⟩
  | members same =>
    intro first second
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_map,
      Pattern.collection.injEq, true_and, and_true, map_eq_self_iff, Function.comp_apply]
    exact ⟨fun h x m => h x ((same x).mpr m), fun h x m => h x ((same x).mp m)⟩
  | apply _ ih =>
    intro first second
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_map,
      List.map_append, List.map_cons, Pattern.apply.injEq, true_and]
    rw [map_middle_eq, map_middle_eq, ih first second]
  | lambda _ ih =>
    intro first second
    simp only [ContextSubstitution.substitute, Pattern.lambda.injEq, true_and, ih]
  | multiLambda _ ih =>
    intro first second
    simp only [ContextSubstitution.substitute, Pattern.multiLambda.injEq, true_and, ih]
  | substBody _ ih =>
    intro first second
    simp only [ContextSubstitution.substitute, Pattern.subst.injEq, ih]
  | substReplacement _ ih =>
    intro first second
    simp only [ContextSubstitution.substitute, Pattern.subst.injEq, ih]
  | element _ ih =>
    intro first second
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_map,
      List.map_append, List.map_cons, Pattern.collection.injEq, true_and, and_true]
    rw [map_middle_eq, map_middle_eq, ih first second]


/-- A permutation is undone by the inverse permutation; a re-presentation by the reverse one. -/
theorem BagStep.symm {left right : Pattern} (step : BagStep left right) : BagStep right left := by
  induction step with
  | permute unordered permutation => exact .permute unordered permutation.symm
  | members same => exact .members fun a => (same a).symm
  | apply _ ih => exact .apply ih
  | lambda _ ih => exact .lambda ih
  | multiLambda _ ih => exact .multiLambda ih
  | substBody _ ih => exact .substBody ih
  | substReplacement _ ih => exact .substReplacement ih
  | element _ ih => exact .element ih

set_option linter.unnecessarySeqFocus false in
/-- What a successful instantiation is. (Some case splits close the goal in `simp`, others
need the iff split, so the combinators stay uniform.) -/
theorem instantiateValue?_eq_some_iff (value : ContextualValue) (ambient depth : Nat) (arguments : List Pattern)
    (result : Pattern) :
    instantiateValue? value ambient depth arguments = some result ↔
      value.ambient = ambient ∧ arguments.length = value.dependencies.length ∧
        value.body.isWellScopedAt (value.dependencies.length + ambient) = true ∧
        (arguments.all fun argument => argument.isWellScopedAt (depth + ambient)) = true ∧
        ContextSubstitution.substitute (occurrenceAssignment value.dependencies.length depth arguments) value.body =
          result ∧
        result.isWellScopedAt (depth + ambient) = true := by
  unfold instantiateValue?
  by_cases sameAmbient : value.ambient = ambient <;>
  by_cases sameLength : arguments.length = value.dependencies.length <;>
  by_cases scopedBody : value.body.isWellScopedAt (value.dependencies.length + ambient) = true <;>
  by_cases scopedArguments : (arguments.all fun argument => argument.isWellScopedAt (depth + ambient)) = true <;>
  simp [sameAmbient, sameLength, scopedBody, scopedArguments] <;>
  constructor <;> intro h <;> (try obtain ⟨_, rfl⟩ := h) <;> simp_all

/-- **Recovering a value from a permuted target** succeeds exactly when it succeeds from the
original target, and the recovered bodies differ by the same permutation. -/
theorem recoverValue?_bagStep {target permuted : Pattern} (step : BagStep target permuted)
    (dependencies : List TypeExpr) (ambient depth : Nat) (arguments : List Pattern) (value : ContextualValue)
    (found : recoverValue? dependencies ambient depth arguments target = some value) :
    ∃ recovered, recoverValue? dependencies ambient depth arguments permuted = some recovered ∧
      recovered.dependencies = value.dependencies ∧ recovered.ambient = value.ambient ∧
      BagStep value.body recovered.body := by
  unfold recoverValue? at found ⊢
  have scopeSame := step.wellScoped (depth + ambient)
  by_cases targetScoped : target.isWellScopedAt (depth + ambient) = true
  · have permutedScoped : permuted.isWellScopedAt (depth + ambient) = true := scopeSame ▸ targetScoped
    simp only [targetScoped, permutedScoped, Bool.not_true, Bool.false_eq_true, if_false, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at found ⊢
    obtain ⟨indices, spine, found⟩ := found
    by_cases sameLength : indices.length = dependencies.length
    · simp only [sameLength, bne_self_eq_false, Bool.false_eq_true, if_false] at found
      have bodyStep : BagStep
          (ContextSubstitution.substitute (recoveryAssignment depth dependencies.length ambient indices) target)
          (ContextSubstitution.substitute (recoveryAssignment depth dependencies.length ambient indices) permuted) :=
        step.substitute (recoveryAssignment depth dependencies.length ambient indices)
      by_cases forward : instantiateValue? (ContextualValue.mk dependencies ambient (ContextSubstitution.substitute (recoveryAssignment depth dependencies.length ambient indices) target))
          ambient depth arguments = some target
      · simp only [forward, beq_self_eq_true, if_true, Option.some.injEq] at found
        obtain ⟨sameAmbient, lengthOk, bodyScoped, argumentsScoped, roundTrip, _⟩ :=
          (instantiateValue?_eq_some_iff _ _ _ _ _).mp forward
        have imageForward : instantiateValue? (ContextualValue.mk dependencies ambient (ContextSubstitution.substitute (recoveryAssignment depth dependencies.length ambient indices) permuted))
            ambient depth arguments = some permuted := by
          apply (instantiateValue?_eq_some_iff _ _ _ _ _).mpr
          refine ⟨sameAmbient, lengthOk, ?_, argumentsScoped, ?_, permutedScoped⟩
          · rw [← bodyStep.wellScoped]; exact bodyScoped
          · exact (step.roundTrip _ _).mp roundTrip
        refine ⟨(ContextualValue.mk dependencies ambient (ContextSubstitution.substitute (recoveryAssignment depth dependencies.length ambient indices) permuted)), ⟨indices, spine, ?_⟩, ?_, ?_, ?_⟩
        · simp only [sameLength, bne_self_eq_false, Bool.false_eq_true, if_false, imageForward, beq_self_eq_true,
            if_true]
        · rw [← found]
        · rw [← found]
        · rw [← found]; exact bodyStep
      · have notForward : (instantiateValue? (ContextualValue.mk dependencies ambient (ContextSubstitution.substitute (recoveryAssignment depth dependencies.length ambient indices) target))
            ambient depth arguments == some target) = false := by
          simpa using forward
        simp only [notForward, Bool.false_eq_true, if_false, reduceCtorEq] at found
    · have notLength : (indices.length != dependencies.length) = true := by simpa using sameLength
      simp only [notLength, if_true, reduceCtorEq] at found
  · simp only [targetScoped, Bool.not_false, if_true, reduceCtorEq] at found

/-! ## Equal canonical forms, node by node -/

/-- Equal canonical forms: the congruence generated by permutations and set re-presentations
(`canon_iff`). -/
def Same (left right : Pattern) : Prop := canon left = canon right

theorem perm_of_sortLex_eq {left right : List Pattern} (same : sortLex left = sortLex right) : left.Perm right :=
  (sortLex_perm left).symm.trans (same ▸ sortLex_perm right)

theorem same_bvar {index : Nat} {other : Pattern} (same : Same (.bvar index) other) : other = .bvar index := by
  unfold Same at same
  cases other <;> simp_all [canon]

theorem same_fvar {name : String} {other : Pattern} (same : Same (.fvar name) other) : other = .fvar name := by
  unfold Same at same
  cases other <;> simp_all [canon]

theorem same_apply {label : String} {arguments : List Pattern} {other : Pattern}
    (same : Same (.apply label arguments) other) :
    ∃ others, other = .apply label others ∧ arguments.map canon = others.map canon := by
  unfold Same at same
  cases other <;> simp_all [canon]

theorem same_lambda {binder : Option String} {body : Pattern} {other : Pattern}
    (same : Same (.lambda binder body) other) :
    ∃ otherBinder otherBody, other = .lambda otherBinder otherBody ∧ Same body otherBody := by
  unfold Same at same
  cases other <;> simp_all [canon, Same]

theorem same_multiLambda {arity : Nat} {binders : List String} {body : Pattern} {other : Pattern}
    (same : Same (.multiLambda arity binders body) other) :
    ∃ otherBinders otherBody, other = .multiLambda arity otherBinders otherBody ∧ Same body otherBody := by
  unfold Same at same
  cases other <;> simp_all [canon, Same]

theorem same_subst {body replacement : Pattern} {other : Pattern}
    (same : Same (.subst body replacement) other) :
    ∃ otherBody otherReplacement, other = .subst otherBody otherReplacement ∧
      Same body otherBody ∧ Same replacement otherReplacement := by
  unfold Same at same
  cases other <;> simp_all [canon, Same]

theorem same_collection {kind : CollType} {elements : List Pattern} {rest : Option String} {other : Pattern}
    (same : Same (.collection kind elements rest) other) :
    ∃ others, other = .collection kind others rest ∧
      arrange kind (elements.map canon) = arrange kind (others.map canon) := by
  unfold Same at same
  cases other with
  | collection otherKind others otherRest =>
    simp only [canon_collection, Pattern.collection.injEq] at same
    obtain ⟨rfl, arranged, rfl⟩ := same
    exact ⟨others, rfl, arranged⟩
  | _ => simp [canon] at same

theorem arrange_eq {kind : CollType} {left right : List Pattern} (same : arrange kind left = arrange kind right) :
    Presents kind left right :=
  presents_of_arrange_eq same

/-- Equal canonical forms are a permutation-generated congruence: one direction of `canon_iff`
as a statement about the relation. -/
theorem same_iff (left right : Pattern) : Same left right ↔ Relation.EqvGen BagStep left right :=
  canon_iff left right

/-! ## Captures modulo permutation -/

/-- Contextual values with equal contexts and permutation-equal bodies. -/
def ValueSame (left right : ContextualValue) : Prop :=
  left.dependencies = right.dependencies ∧ left.ambient = right.ambient ∧ Same left.body right.body

/-- Assignments that bind the same names, in order, to `ValueSame` values. -/
def AssignSame (left right : ScopedRuleMatching.Assignment) : Prop :=
  List.Forall₂ (fun first second => first.1 = second.1 ∧ ValueSame first.2 second.2) left right

/-- **Comparison of repeated metavariables modulo permutation**: equal canonical forms. -/
def canonCompare (_name : String) (left right : Pattern) : Bool := canon left == canon right

private theorem reflTransGen_reverse {left right : Pattern} (chain : Relation.ReflTransGen BagStep left right) :
    Relation.ReflTransGen BagStep right left := by
  induction chain with
  | refl => exact .refl
  | tail _ step ih => exact Relation.ReflTransGen.head step.symm ih

theorem eqvGen_reflTransGen {left right : Pattern} (related : Relation.EqvGen BagStep left right) :
    Relation.ReflTransGen BagStep left right := by
  induction related with
  | rel _ _ step => exact .single step
  | refl => exact .refl
  | symm _ _ _ ih => exact reflTransGen_reverse ih
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **Recovering from a permutation-equal target.** -/
theorem recoverValue?_same {target other : Pattern} (same : Same target other)
    (dependencies : List TypeExpr) (ambient depth : Nat) (arguments : List Pattern) (value : ContextualValue)
    (found : recoverValue? dependencies ambient depth arguments target = some value) :
    ∃ recovered, recoverValue? dependencies ambient depth arguments other = some recovered ∧
      ValueSame value recovered := by
  have chain := eqvGen_reflTransGen ((canon_iff _ _).mp same)
  clear same
  induction chain with
  | refl => exact ⟨value, found, rfl, rfl, rfl⟩
  | tail _ step ih =>
    obtain ⟨middle, middleFound, sameDeps, sameAmbient, sameBody⟩ := ih
    obtain ⟨recovered, recoveredFound, deps', ambient', bodyStep⟩ :=
      recoverValue?_bagStep step dependencies ambient depth arguments middle middleFound
    exact ⟨recovered, recoveredFound, sameDeps.trans deps'.symm, sameAmbient.trans ambient'.symm,
      sameBody.trans (eqvGen_canon_eq (.rel _ _ bodyStep))⟩

theorem lookup_same {left right : ScopedRuleMatching.Assignment} (same : AssignSame left right) (name : String) :
    (ScopedRuleMatching.lookup left name = none ∧ ScopedRuleMatching.lookup right name = none) ∨
      ∃ first second, ScopedRuleMatching.lookup left name = some first ∧
        ScopedRuleMatching.lookup right name = some second ∧ ValueSame first second := by
  induction same with
  | nil => exact .inl ⟨rfl, rfl⟩
  | @cons first second restLeft restRight entry _ ih =>
    obtain ⟨sameName, sameValue⟩ := entry
    by_cases here : first.1 = name
    · refine .inr ⟨first.2, second.2, ?_, ?_, sameValue⟩
      · simp [ScopedRuleMatching.lookup, List.find?, here]
      · simp [ScopedRuleMatching.lookup, List.find?, ← sameName, here]
    · have there : (second.1 == name) = false := by simpa [← sameName] using here
      have firstThere : (first.1 == name) = false := by simpa using here
      simpa [ScopedRuleMatching.lookup, List.find?, there, firstThere] using ih

/-- **Extending or checking an assignment modulo permutation.** -/
theorem assignWith_same {left right : ScopedRuleMatching.Assignment} (same : AssignSame left right)
    (name : String) {value other : ContextualValue} (sameValue : ValueSame value other)
    {extended : ScopedRuleMatching.Assignment}
    (accepted : ScopedRuleMatching.assignWith canonCompare left name value = some extended) :
    ∃ otherExtended, ScopedRuleMatching.assignWith canonCompare right name other = some otherExtended ∧
      AssignSame extended otherExtended := by
  obtain ⟨sameDeps, sameAmbient, sameBody⟩ := sameValue
  unfold ScopedRuleMatching.assignWith at accepted ⊢
  rcases lookup_same same name with ⟨leftNone, rightNone⟩ | ⟨prior, otherPrior, leftSome, rightSome, priorSame⟩
  · simp only [leftNone, Option.some.injEq] at accepted
    subst accepted
    simp only [rightNone, Option.some.injEq, exists_eq_left']
    exact List.Forall₂.cons ⟨rfl, sameDeps, sameAmbient, sameBody⟩ same
  · obtain ⟨priorDeps, priorAmbient, priorBody⟩ := priorSame
    simp only [leftSome] at accepted
    simp only [rightSome]
    have test : (prior.dependencies == value.dependencies && prior.ambient == value.ambient &&
        canonCompare name prior.body value.body) =
      (otherPrior.dependencies == other.dependencies && otherPrior.ambient == other.ambient &&
        canonCompare name otherPrior.body other.body) := by
      simp only [canonCompare, ← priorDeps, ← priorAmbient, ← sameDeps, ← sameAmbient]
      unfold Same at priorBody sameBody
      rw [priorBody, sameBody]
    split at accepted
    · rename_i passed
      simp only [Option.some.injEq] at accepted
      subst accepted
      rw [test] at passed
      simp only [passed, if_true, Option.some.injEq, exists_eq_left']
      exact same
    · cases accepted

/-- **Capturing a permutation-equal target**, with comparison modulo permutation. -/
theorem captureWith?_same (rule : RewriteRule) (spec : RuleBindingSpec) (ambient depth : Nat)
    (site : RulePatternSite) (path : List Nat) {left right : ScopedRuleMatching.Assignment}
    (same : AssignSame left right) (name : String) {target other : Pattern} (sameTarget : Same target other)
    {extended : ScopedRuleMatching.Assignment}
    (accepted : ScopedRuleMatching.captureWith? canonCompare rule spec ambient depth site path left name target =
      some extended) :
    ∃ otherExtended, ScopedRuleMatching.captureWith? canonCompare rule spec ambient depth site path right name other =
        some otherExtended ∧ AssignSame extended otherExtended := by
  unfold ScopedRuleMatching.captureWith? at accepted ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at accepted ⊢
  obtain ⟨dependencies, depsFound, arguments, argsFound, value, valueFound, assigned⟩ := accepted
  obtain ⟨recovered, recoveredFound, valueSame⟩ :=
    recoverValue?_same sameTarget dependencies ambient depth arguments value valueFound
  obtain ⟨otherExtended, otherAssigned, assignSame⟩ := assignWith_same same name valueSame assigned
  exact ⟨otherExtended, ⟨dependencies, depsFound, arguments, argsFound, recovered, recoveredFound, otherAssigned⟩,
    assignSame⟩

/-! ## Matching modulo permutation -/

open ScopedRuleMatching in
/-- A selected element of one bag has a partner in a permutation-equal bag, and the remainders
stay permutation-equal. -/
theorem select_partner {targets others : List Pattern} (perm : (targets.map canon).Perm (others.map canon))
    {selected : Nat} (within : selected < targets.length) :
    ∃ partner, ∃ partnerWithin : partner < others.length, Same targets[selected] others[partner] ∧
      ((targets.eraseIdx selected).map canon).Perm ((others.eraseIdx partner).map canon) := by
  have member : canon targets[selected] ∈ others.map canon :=
    perm.subset (List.mem_map.mpr ⟨_, List.getElem_mem within, rfl⟩)
  obtain ⟨partner, partnerWithin, same⟩ := List.getElem_of_mem member
  simp only [List.getElem_map] at same
  refine ⟨partner, by simpa using partnerWithin, same.symm, ?_⟩
  rw [← List.eraseIdx_map, ← List.eraseIdx_map]
  refine (List.perm_eraseIdx_of_getElem?_eq ?_).mpr perm
  simp [List.getElem?_eq_getElem within, List.getElem?_eq_getElem (by simpa using partnerWithin), same]

theorem forall₂_same_of_map {targets others : List Pattern} (same : targets.map canon = others.map canon) :
    List.Forall₂ Same targets others := by
  induction targets generalizing others with
  | nil => cases others <;> simp_all
  | cons head tail ih =>
    cases others with
    | nil => simp at same
    | cons otherHead otherTail =>
      simp only [List.map_cons, List.cons.injEq] at same
      exact .cons same.1 (ih same.2)

theorem forall₂_same_map {targets others : List Pattern} (same : List.Forall₂ Same targets others) :
    targets.map canon = others.map canon := by
  induction same with
  | nil => rfl
  | cons head _ ih => simp only [List.map_cons, ih]; exact congrArg (· :: _) head

variable (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)

mutual
/-- **Matching modulo permutation**: on permutation-equal subjects, with repeated metavariables
compared modulo permutation, every match has a counterpart whose captures are permutation-equal. -/
theorem matchAtWith_same : ∀ (pattern : Pattern) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (left right : ScopedRuleMatching.Assignment) (target other : Pattern),
    setFree pattern = true → AssignSame left right → Same target other →
    ∀ found ∈ ScopedRuleMatching.matchAtWith canonCompare rule spec ambient site path depth left pattern target,
      ∃ otherFound ∈ ScopedRuleMatching.matchAtWith canonCompare rule spec ambient site path depth right pattern other,
        AssignSame found otherFound
  | .fvar name, site, path, depth, left, right, target, other, free, same, sameTarget => by
    intro found member
    simp only [ScopedRuleMatching.matchAtWith, Option.mem_toList] at member ⊢
    obtain ⟨otherFound, otherCaptured, assignSame⟩ :=
      captureWith?_same rule spec ambient depth site path same name sameTarget member
    exact ⟨otherFound, otherCaptured, assignSame⟩
  | .bvar expected, site, path, depth, left, right, target, other, free, same, sameTarget => by
    intro found member
    cases target with
    | bvar actual =>
      rw [same_bvar sameTarget]
      simp only [ScopedRuleMatching.matchAtWith] at member ⊢
      split at member
      · simp only [List.mem_singleton] at member; subst member
        rename_i equal; simp only [equal, if_true, List.mem_singleton, exists_eq_left]; exact same
      · cases member
    | _ => simp [ScopedRuleMatching.matchAtWith] at member
  | .apply constructor patterns, site, path, depth, left, right, target, other, free, same, sameTarget => by
    intro found member
    cases target with
    | apply actual targets =>
      obtain ⟨others, rfl, mapped⟩ := same_apply sameTarget
      simp only [ScopedRuleMatching.matchAtWith] at member ⊢
      split at member
      · rename_i equal
        simp only [equal, if_true]
        exact matchArgsAtWith_same patterns site path depth left right 0 targets others
          (setFreeList_iff.mp (by simpa [setFree] using free)) same (forall₂_same_of_map mapped) found member
      · cases member
    | _ => simp [ScopedRuleMatching.matchAtWith] at member
  | .lambda display body, site, path, depth, left, right, target, other, free, same, sameTarget => by
    intro found member
    cases target with
    | lambda actualDisplay targetBody =>
      obtain ⟨otherDisplay, otherBody, rfl, sameBody⟩ := same_lambda sameTarget
      simp only [ScopedRuleMatching.matchAtWith] at member ⊢
      exact matchAtWith_same body site (path ++ [0]) (depth + 1) left right targetBody otherBody
        (by simpa [setFree] using free) same sameBody found member
    | _ => simp [ScopedRuleMatching.matchAtWith] at member
  | .multiLambda arity display body, site, path, depth, left, right, target, other, free, same, sameTarget => by
    intro found member
    cases target with
    | multiLambda actualArity actualDisplay targetBody =>
      obtain ⟨otherDisplay, otherBody, rfl, sameBody⟩ := same_multiLambda sameTarget
      simp only [ScopedRuleMatching.matchAtWith] at member ⊢
      split at member
      · rename_i equal
        simp only [equal, if_true]
        exact matchAtWith_same body site (path ++ [0]) (depth + arity) left right targetBody otherBody
          (by simpa [setFree] using free) same sameBody found member
      · cases member
    | _ => simp [ScopedRuleMatching.matchAtWith] at member
  | .subst body replacement, site, path, depth, left, right, target, other, free, same, sameTarget => by
    intro found member
    have parts : setFree body = true ∧ setFree replacement = true := by simpa [setFree] using free
    cases target with
    | subst targetBody targetReplacement =>
      obtain ⟨otherBody, otherReplacement, rfl, sameBody, sameReplacement⟩ := same_subst sameTarget
      simp only [ScopedRuleMatching.matchAtWith, List.mem_flatMap] at member ⊢
      obtain ⟨middle, middleMember, foundMember⟩ := member
      obtain ⟨otherMiddle, otherMiddleMember, middleSame⟩ :=
        matchAtWith_same body site (path ++ [0]) (depth + 1) left right targetBody otherBody parts.1 same sameBody
          middle middleMember
      obtain ⟨otherFound, otherFoundMember, foundSame⟩ :=
        matchAtWith_same replacement site (path ++ [1]) depth middle otherMiddle targetReplacement otherReplacement
          parts.2 middleSame sameReplacement found foundMember
      exact ⟨otherFound, ⟨otherMiddle, otherMiddleMember, otherFoundMember⟩, foundSame⟩
    | _ => simp [ScopedRuleMatching.matchAtWith] at member
  | .collection kind patterns rest, site, path, depth, left, right, target, other, free, same, sameTarget => by
    intro found member
    obtain ⟨notSet, elementsFree⟩ := setFree_collection free
    cases target with
    | collection actualKind targets actualRest =>
      obtain ⟨others, rfl, arranged⟩ := same_collection sameTarget
      unfold ScopedRuleMatching.matchAtWith at member ⊢
      split at member
      · rename_i admitted
        simp only [admitted, if_true]
        have kindEq : kind = actualKind := by simpa using (Bool.and_eq_true _ _).mp admitted |>.1
        subst kindEq
        split at member
        · rename_i isVec
          have vecKind : kind = .vec := by simpa using isVec
          subst vecKind
          have mapped : targets.map canon = others.map canon := arrange_eq arranged
          simp only [beq_self_eq_true, ↓reduceIte]
          cases rest with
          | none =>
            exact matchArgsAtWith_same patterns site path depth left right 0 targets others elementsFree same
              (forall₂_same_of_map mapped) found member
          | some name =>
            simp only [List.mem_filterMap] at member ⊢
            obtain ⟨middle, middleMember, captured⟩ := member
            have pointwise := forall₂_same_of_map mapped
            have takeSame : List.Forall₂ Same (targets.take patterns.length) (others.take patterns.length) :=
              forall₂_same_of_map (by rw [List.map_take, List.map_take, mapped])
            obtain ⟨otherMiddle, otherMiddleMember, middleSame⟩ :=
              matchArgsAtWith_same patterns site path depth left right 0 _ _ elementsFree same takeSame middle
                middleMember
            have dropSame : Same (.collection .vec (targets.drop patterns.length) none)
                (.collection .vec (others.drop patterns.length) none) := by
              unfold Same
              simp only [canon_collection, arrange_vec]
              rw [List.map_drop, List.map_drop, mapped]
            simp only [ScopedRuleMatching.captureRestWith?] at captured ⊢
            obtain ⟨otherFound, otherCaptured, foundSame⟩ :=
              captureWith?_same rule spec ambient depth site (path ++ [patterns.length]) middleSame name dropSame
                captured
            exact ⟨otherFound, ⟨otherMiddle, otherMiddleMember, otherCaptured⟩, foundSame⟩
        · rename_i notVec
          have unordered : Unordered kind = true := by
            cases kind <;> simp_all [Unordered]
          have isNotVec : (kind == CollType.vec) = false := by simpa using notVec
          have perm : (targets.map canon).Perm (others.map canon) := by
            have presents := arrange_eq arranged
            cases kind with
            | vec => simp at isNotVec
            | hashBag => exact presents
            | hashSet => exact absurd rfl notSet
          simp only [isNotVec, Bool.false_eq_true, if_false]
          exact matchBagAtWith_same patterns site path depth left right 0 rest kind targets others elementsFree
            unordered same perm found member
      · cases member
    | _ => simp [ScopedRuleMatching.matchAtWith] at member
termination_by pattern => sizeOf pattern

theorem matchArgsAtWith_same : ∀ (patterns : List Pattern) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (left right : ScopedRuleMatching.Assignment) (index : Nat) (targets others : List Pattern),
    (∀ pattern ∈ patterns, setFree pattern = true) → AssignSame left right → List.Forall₂ Same targets others →
    ∀ found ∈ ScopedRuleMatching.matchArgsAtWith canonCompare rule spec ambient site path depth left index patterns
        targets,
      ∃ otherFound ∈ ScopedRuleMatching.matchArgsAtWith canonCompare rule spec ambient site path depth right index
          patterns others,
        AssignSame found otherFound
  | [], site, path, depth, left, right, index, targets, others, _, same, pointwise => by
    intro found member
    cases pointwise with
    | nil =>
      simp only [ScopedRuleMatching.matchArgsAtWith, List.mem_singleton] at member ⊢
      exact ⟨right, rfl, member ▸ same⟩
    | cons _ _ => simp [ScopedRuleMatching.matchArgsAtWith] at member
  | pattern :: patterns, site, path, depth, left, right, index, targets, others, free, same, pointwise => by
    intro found member
    cases pointwise with
    | nil => simp [ScopedRuleMatching.matchArgsAtWith] at member
    | @cons target other targets others headSame tailSame =>
      simp only [ScopedRuleMatching.matchArgsAtWith, List.mem_flatMap] at member ⊢
      obtain ⟨middle, middleMember, foundMember⟩ := member
      obtain ⟨otherMiddle, otherMiddleMember, middleSame⟩ :=
        matchAtWith_same pattern site (path ++ [index]) depth left right target other (free pattern List.mem_cons_self)
          same headSame middle middleMember
      obtain ⟨otherFound, otherFoundMember, foundSame⟩ :=
        matchArgsAtWith_same patterns site path depth middle otherMiddle (index + 1) targets others
          (fun other member => free other (List.mem_cons_of_mem _ member)) middleSame tailSame found foundMember
      exact ⟨otherFound, ⟨otherMiddle, otherMiddleMember, otherFoundMember⟩, foundSame⟩
termination_by patterns => sizeOf patterns

theorem matchBagAtWith_same : ∀ (patterns : List Pattern) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (left right : ScopedRuleMatching.Assignment) (index : Nat) (rest : Option String) (kind : CollType)
    (targets others : List Pattern), (∀ pattern ∈ patterns, setFree pattern = true) → Unordered kind = true →
    AssignSame left right → (targets.map canon).Perm (others.map canon) →
    ∀ found ∈ ScopedRuleMatching.matchBagAtWith canonCompare rule spec ambient site path depth left index patterns
        rest kind targets,
      ∃ otherFound ∈ ScopedRuleMatching.matchBagAtWith canonCompare rule spec ambient site path depth right index
          patterns rest kind others,
        AssignSame found otherFound
  | [], site, path, depth, left, right, index, none, kind, targets, others, _, _, same, perm => by
    intro found member
    simp only [ScopedRuleMatching.matchBagAtWith] at member ⊢
    split at member
    · rename_i empty
      have otherEmpty : others.isEmpty = true := by
        have := perm.length_eq; simp only [List.length_map] at this
        simp only [List.isEmpty_iff] at empty ⊢; subst empty; exact List.length_eq_zero_iff.mp this.symm
      simp only [List.mem_singleton] at member; subst member
      simp only [otherEmpty, if_true, List.mem_singleton, exists_eq_left]; exact same
    · cases member
  | [], site, path, depth, left, right, index, some name, kind, targets, others, _, unordered, same, perm => by
    intro found member
    simp only [ScopedRuleMatching.matchBagAtWith, Option.mem_toList, ScopedRuleMatching.captureRestWith?]
      at member ⊢
    have collected : Same (.collection kind targets none) (.collection kind others none) := by
      unfold Same; simp only [canon_collection, arrange_perm unordered perm]
    obtain ⟨otherFound, otherCaptured, foundSame⟩ :=
      captureWith?_same rule spec ambient depth site (path ++ [index]) same name collected member
    exact ⟨otherFound, otherCaptured, foundSame⟩
  | pattern :: patterns, site, path, depth, left, right, index, rest, kind, targets, others, free, unordered, same,
      perm => by
    intro found member
    simp only [ScopedRuleMatching.matchBagAtWith, List.mem_flatMap] at member ⊢
    obtain ⟨⟨target, selected⟩, selectedMember, middle, middleMember, foundMember⟩ := member
    obtain ⟨within, atSelected⟩ := List.mem_zipIdx' selectedMember
    obtain ⟨partner, partnerWithin, partnerSame, remainder⟩ := select_partner perm within
    rw [← atSelected] at partnerSame
    obtain ⟨otherMiddle, otherMiddleMember, middleSame⟩ :=
      matchAtWith_same pattern site (path ++ [index]) depth left right target others[partner]
        (free pattern List.mem_cons_self) same partnerSame middle middleMember
    obtain ⟨otherFound, otherFoundMember, foundSame⟩ :=
      matchBagAtWith_same patterns site path depth middle otherMiddle (index + 1) rest kind
        (targets.eraseIdx selected) (others.eraseIdx partner) (fun other member => free other (List.mem_cons_of_mem _ member))
        unordered middleSame remainder found foundMember
    refine ⟨otherFound, ⟨(others[partner], partner), ?_, otherMiddle, otherMiddleMember, otherFoundMember⟩, foundSame⟩
    exact List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem partnerWithin])
termination_by patterns => sizeOf patterns
end

/-! ## Permutation-equality is a congruence that operations respect -/

theorem same_refl (pattern : Pattern) : Same pattern pattern := rfl

theorem Same.symm {left right : Pattern} (same : Same left right) : Same right left := Eq.symm same

theorem Same.trans {first second third : Pattern} (one : Same first second) (two : Same second third) :
    Same first third := Eq.trans one two

theorem same_of_bagStep {left right : Pattern} (step : BagStep left right) : Same left right := step.canon_eq

theorem same_apply_congr (label : String) {left right : List Pattern} (pointwise : List.Forall₂ Same left right) :
    Same (.apply label left) (.apply label right) := by
  unfold Same; rw [canon_apply, canon_apply, forall₂_same_map pointwise]

theorem same_collection_congr (kind : CollType) {left right : List Pattern} (rest : Option String)
    (pointwise : List.Forall₂ Same left right) : Same (.collection kind left rest) (.collection kind right rest) := by
  unfold Same; rw [canon_collection, canon_collection, forall₂_same_map pointwise]

theorem same_lambda_congr (binder : Option String) {left right : Pattern} (same : Same left right) :
    Same (.lambda binder left) (.lambda binder right) := by
  unfold Same at same ⊢; simp only [canon, same]

theorem same_multiLambda_congr (arity : Nat) (binders : List String) {left right : Pattern} (same : Same left right) :
    Same (.multiLambda arity binders left) (.multiLambda arity binders right) := by
  unfold Same at same ⊢; simp only [canon, same]

theorem same_subst_congr {body body' replacement replacement' : Pattern} (sameBody : Same body body')
    (sameReplacement : Same replacement replacement') : Same (.subst body replacement) (.subst body' replacement') := by
  unfold Same at sameBody sameReplacement ⊢; simp only [canon, sameBody, sameReplacement]

/-- A map that sends each permutation to a permutation-equal pair respects permutation-equality. -/
theorem same_map {f : Pattern → Pattern} (compatible : ∀ {a b : Pattern}, BagStep a b → Same (f a) (f b))
    {left right : Pattern} (same : Same left right) : Same (f left) (f right) := by
  have chain := eqvGen_reflTransGen ((canon_iff _ _).mp same)
  clear same
  induction chain with
  | refl => rfl
  | tail _ step ih => exact ih.trans (compatible step)

theorem BagStep.liftBVars {left right : Pattern} (step : BagStep left right) :
    ∀ cutoff shift, BagStep (Substitution.liftBVars cutoff shift left) (Substitution.liftBVars cutoff shift right) := by
  induction step with
  | permute unordered permutation =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map]
    exact .permute unordered (permutation.map _)
  | members same =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map]
    exact .members (members_map same _)
  | apply _ ih =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, List.map_append, List.map_cons]
    exact .apply (ih cutoff shift)
  | lambda _ ih => intro cutoff shift; simp only [Substitution.liftBVars]; exact .lambda (ih _ _)
  | multiLambda _ ih => intro cutoff shift; simp only [Substitution.liftBVars]; exact .multiLambda (ih _ _)
  | substBody _ ih => intro cutoff shift; simp only [Substitution.liftBVars]; exact .substBody (ih _ _)
  | substReplacement _ ih => intro cutoff shift; simp only [Substitution.liftBVars]; exact .substReplacement (ih _ _)
  | element _ ih =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, List.map_append, List.map_cons]
    exact .element (ih cutoff shift)

theorem BagStep.instantiateBVarAt {left right : Pattern} (step : BagStep left right) :
    ∀ depth replacement, BagStep (Substitution.instantiateBVarAt depth replacement left)
      (Substitution.instantiateBVarAt depth replacement right) := by
  induction step with
  | permute unordered permutation =>
    intro depth replacement
    rw [Substitution.instantiateBVarAt, Substitution.instantiateBVarAt]
    exact .permute unordered (permutation.map _)
  | members same =>
    intro depth replacement
    rw [Substitution.instantiateBVarAt, Substitution.instantiateBVarAt]
    exact .members (members_map same _)
  | apply _ ih =>
    intro depth replacement
    rw [Substitution.instantiateBVarAt, Substitution.instantiateBVarAt]
    simp only [List.map_append, List.map_cons]
    exact .apply (ih depth replacement)
  | lambda _ ih =>
    intro depth replacement; rw [Substitution.instantiateBVarAt, Substitution.instantiateBVarAt]; exact .lambda (ih _ _)
  | multiLambda _ ih =>
    intro depth replacement; rw [Substitution.instantiateBVarAt, Substitution.instantiateBVarAt]
    exact .multiLambda (ih _ _)
  | substBody _ ih =>
    intro depth replacement; rw [Substitution.instantiateBVarAt, Substitution.instantiateBVarAt]
    exact .substBody (ih _ _)
  | substReplacement _ ih =>
    intro depth replacement; rw [Substitution.instantiateBVarAt, Substitution.instantiateBVarAt]
    exact .substReplacement (ih _ _)
  | element _ ih =>
    intro depth replacement
    rw [Substitution.instantiateBVarAt, Substitution.instantiateBVarAt]
    simp only [List.map_append, List.map_cons]
    exact .element (ih depth replacement)

/-- Binder elimination with permutation-equal replacements gives permutation-equal results. -/
theorem instantiateBVarAt_same_replacement {replacement other : Pattern} (same : Same replacement other) :
    ∀ (body : Pattern) (depth : Nat), Same (Substitution.instantiateBVarAt depth replacement body)
      (Substitution.instantiateBVarAt depth other body)
  | .bvar index, depth => by
    rw [Substitution.instantiateBVarAt, Substitution.instantiateBVarAt]
    split
    · rfl
    · split
      · exact same_map (fun step => same_of_bagStep (step.liftBVars 0 depth)) same
      · rfl
  | .fvar name, depth => by rw [Substitution.instantiateBVarAt, Substitution.instantiateBVarAt]; rfl
  | .apply label arguments, depth => by
    rw [Substitution.instantiateBVarAt, Substitution.instantiateBVarAt]
    apply same_apply_congr
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro item member
    have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
    exact instantiateBVarAt_same_replacement same item depth
  | .lambda binder body, depth => by
    rw [Substitution.instantiateBVarAt, Substitution.instantiateBVarAt]
    exact same_lambda_congr _ (instantiateBVarAt_same_replacement same body (depth + 1))
  | .multiLambda arity binders body, depth => by
    rw [Substitution.instantiateBVarAt, Substitution.instantiateBVarAt]
    exact same_multiLambda_congr _ _ (instantiateBVarAt_same_replacement same body (depth + arity))
  | .subst body nested, depth => by
    rw [Substitution.instantiateBVarAt, Substitution.instantiateBVarAt]
    exact same_subst_congr (instantiateBVarAt_same_replacement same body (depth + 1))
      (instantiateBVarAt_same_replacement same nested depth)
  | .collection kind elements rest, depth => by
    rw [Substitution.instantiateBVarAt, Substitution.instantiateBVarAt]
    apply same_collection_congr
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro item member
    have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
    exact instantiateBVarAt_same_replacement same item depth
termination_by body => sizeOf body

/-- **Ordinary binder elimination respects permutation-equality in both arguments.** -/
theorem instantiateBVar_same {replacement replacement' body body' : Pattern} (sameReplacement : Same replacement replacement')
    (sameBody : Same body body') :
    Same (Substitution.instantiateBVar replacement body) (Substitution.instantiateBVar replacement' body') :=
  (instantiateBVarAt_same_replacement sameReplacement body 0).trans
    (same_map (fun step => same_of_bagStep (step.instantiateBVarAt 0 replacement')) sameBody)

/-- **Instantiating permutation-equal values.** -/
theorem instantiateValue?_same {value other : ContextualValue} (same : ValueSame value other)
    (ambient depth : Nat) (arguments : List Pattern) (result : Pattern)
    (found : instantiateValue? value ambient depth arguments = some result) :
    ∃ otherResult, instantiateValue? other ambient depth arguments = some otherResult ∧ Same result otherResult := by
  obtain ⟨sameDeps, sameAmbient, sameBody⟩ := same
  obtain ⟨ambientOk, lengthOk, bodyScoped, argumentsScoped, substituted, resultScoped⟩ :=
    (instantiateValue?_eq_some_iff _ _ _ _ _).mp found
  have chain := eqvGen_reflTransGen ((canon_iff _ _).mp sameBody)
  have scopedAlong : ∀ {a b : Pattern}, Relation.ReflTransGen BagStep a b → ∀ d, a.isWellScopedAt d = b.isWellScopedAt d := by
    intro a b chain d
    induction chain with
    | refl => rfl
    | tail _ step ih => exact ih.trans (step.wellScoped d)
  let image := ContextSubstitution.substitute (occurrenceAssignment other.dependencies.length depth arguments) other.body
  have imageSame : Same result image := by
    show Same result
      (ContextSubstitution.substitute (occurrenceAssignment other.dependencies.length depth arguments) other.body)
    rw [← substituted, ← sameDeps]
    exact same_map (fun step => same_of_bagStep (step.substitute _)) sameBody
  have imageChain : Relation.ReflTransGen BagStep result image :=
    eqvGen_reflTransGen ((canon_iff _ _).mp imageSame)
  refine ⟨image, (instantiateValue?_eq_some_iff _ _ _ _ _).mpr ⟨sameAmbient ▸ ambientOk, sameDeps ▸ lengthOk, ?_,
    argumentsScoped, rfl, ?_⟩, imageSame⟩
  · rw [← sameDeps, ← scopedAlong chain]; exact bodyScoped
  · rw [← scopedAlong imageChain]; exact resultScoped

/-- Splicing a permutation-equal residual into a collection after pointwise-equal elements. -/
theorem same_splice (kind : CollType) {explicit explicit' residual residual' : List Pattern}
    (pointwise : List.Forall₂ Same explicit explicit')
    (arranged : arrange kind (residual.map canon) = arrange kind (residual'.map canon)) :
    Same (.collection kind (explicit ++ residual) none) (.collection kind (explicit' ++ residual') none) := by
  unfold Same
  rw [canon_collection, canon_collection]
  congr 1
  apply arrange_eq_of_presents
  have front := forall₂_same_map pointwise
  have back := arrange_eq arranged
  simp only [List.map_append, front]
  cases kind with
  | vec => rw [show residual.map canon = residual'.map canon from back]; exact rfl
  | hashBag => exact List.Perm.append_left _ back
  | hashSet => intro a; simp only [List.mem_append]; exact or_congr Iff.rfl (back a)

mutual
/-- **Instantiating a right side with permutation-equal captures** gives permutation-equal
results, for any binder operation that respects permutation-equality. -/
theorem instantiateWith?_same (operation : Pattern → Pattern → Pattern)
    (respects : ∀ {a a' b b' : Pattern}, Same a a' → Same b b' → Same (operation a b) (operation a' b')) :
    ∀ (pattern : Pattern) (site : RulePatternSite) (path : List Nat) (depth : Nat)
      (left right : ScopedRuleMatching.Assignment) (result : Pattern), AssignSame left right →
      ScopedRuleMatching.instantiateWith? operation rule spec ambient site path depth left pattern = some result →
      ∃ otherResult, ScopedRuleMatching.instantiateWith? operation rule spec ambient site path depth right pattern =
        some otherResult ∧ Same result otherResult
  | .fvar name, site, path, depth, left, right, result, same, found => by
    rw [ScopedRuleMatching.instantiateWith?] at found ⊢
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at found ⊢
    obtain ⟨value, valueFound, arguments, argumentsFound, instantiated⟩ := found
    rcases lookup_same same name with ⟨leftNone, _⟩ | ⟨first, second, leftSome, rightSome, valueSame⟩
    · rw [leftNone] at valueFound; cases valueFound
    · rw [leftSome, Option.some.injEq] at valueFound
      subst valueFound
      obtain ⟨otherResult, otherFound, resultSame⟩ :=
        instantiateValue?_same valueSame ambient depth arguments result instantiated
      exact ⟨otherResult, ⟨second, rightSome, arguments, argumentsFound, otherFound⟩, resultSame⟩
  | .bvar index, site, path, depth, left, right, result, same, found => by
    rw [ScopedRuleMatching.instantiateWith?] at found ⊢
    exact ⟨result, found, rfl⟩
  | .apply constructor arguments, site, path, depth, left, right, result, same, found => by
    rw [ScopedRuleMatching.instantiateWith?] at found ⊢
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
    obtain ⟨results, resultsFound, rfl⟩ := found
    obtain ⟨otherResults, otherFound, pointwise⟩ :=
      instantiateArgsWith?_same operation respects arguments site path depth left right 0 results same resultsFound
    exact ⟨_, ⟨otherResults, otherFound, rfl⟩, same_apply_congr _ pointwise⟩
  | .lambda binder body, site, path, depth, left, right, result, same, found => by
    rw [ScopedRuleMatching.instantiateWith?] at found ⊢
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
    obtain ⟨inner, innerFound, rfl⟩ := found
    obtain ⟨otherInner, otherFound, innerSame⟩ :=
      instantiateWith?_same operation respects body site (path ++ [0]) (depth + 1) left right inner same innerFound
    exact ⟨_, ⟨otherInner, otherFound, rfl⟩, same_lambda_congr _ innerSame⟩
  | .multiLambda arity binders body, site, path, depth, left, right, result, same, found => by
    rw [ScopedRuleMatching.instantiateWith?] at found ⊢
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
    obtain ⟨inner, innerFound, rfl⟩ := found
    obtain ⟨otherInner, otherFound, innerSame⟩ :=
      instantiateWith?_same operation respects body site (path ++ [0]) (depth + arity) left right inner same innerFound
    exact ⟨_, ⟨otherInner, otherFound, rfl⟩, same_multiLambda_congr _ _ innerSame⟩
  | .subst body replacement, site, path, depth, left, right, result, same, found => by
    rw [ScopedRuleMatching.instantiateWith?] at found ⊢
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
    obtain ⟨body', bodyFound, replacement', replacementFound, rfl⟩ := found
    obtain ⟨otherBody, otherBodyFound, bodySame⟩ :=
      instantiateWith?_same operation respects body site (path ++ [0]) (depth + 1) left right body' same bodyFound
    obtain ⟨otherReplacement, otherReplacementFound, replacementSame⟩ :=
      instantiateWith?_same operation respects replacement site (path ++ [1]) depth left right replacement' same
        replacementFound
    exact ⟨_, ⟨otherBody, otherBodyFound, otherReplacement, otherReplacementFound, rfl⟩,
      respects replacementSame bodySame⟩
  | .collection kind elements rest, site, path, depth, left, right, result, same, found => by
    rw [ScopedRuleMatching.instantiateWith?] at found ⊢
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at found ⊢
    obtain ⟨explicit, explicitFound, finish⟩ := found
    obtain ⟨otherExplicit, otherExplicitFound, pointwise⟩ :=
      instantiateArgsWith?_same operation respects elements site path depth left right 0 explicit same explicitFound
    cases rest with
    | none =>
      simp only [Option.some.injEq] at finish
      subst finish
      exact ⟨_, ⟨otherExplicit, otherExplicitFound, rfl⟩, same_collection_congr _ _ pointwise⟩
    | some name =>
      simp only [Option.bind_eq_some_iff] at finish
      obtain ⟨value, valueFound, arguments, argumentsFound, produced, instantiated, finish⟩ := finish
      rcases lookup_same same name with ⟨leftNone, _⟩ | ⟨first, second, leftSome, rightSome, valueSame⟩
      · rw [leftNone] at valueFound; cases valueFound
      rw [leftSome, Option.some.injEq] at valueFound
      subst valueFound
      obtain ⟨otherProduced, otherInstantiated, producedSame⟩ :=
        instantiateValue?_same valueSame ambient depth arguments produced instantiated
      · cases produced with
        | collection actualKind residual residualRest =>
          cases residualRest with
          | some _ => simp at finish
          | none =>
            obtain ⟨otherResidual, rfl, arranged⟩ := same_collection producedSame
            simp only at finish
            split at finish
            · rename_i sameKind
              simp only [Option.some.injEq] at finish
              subst finish
              have kindEq : actualKind = kind := by simpa using sameKind
              subst kindEq
              refine ⟨_, ⟨otherExplicit, otherExplicitFound, ?_⟩, same_splice actualKind pointwise arranged⟩
              simp only [Option.bind_eq_some_iff]
              exact ⟨second, rightSome, arguments, argumentsFound, by simp [otherInstantiated]⟩
            · cases finish
        | _ => simp at finish
termination_by pattern => sizeOf pattern

theorem instantiateArgsWith?_same (operation : Pattern → Pattern → Pattern)
    (respects : ∀ {a a' b b' : Pattern}, Same a a' → Same b b' → Same (operation a b) (operation a' b')) :
    ∀ (patterns : List Pattern) (site : RulePatternSite) (path : List Nat) (depth : Nat)
      (left right : ScopedRuleMatching.Assignment) (index : Nat) (results : List Pattern), AssignSame left right →
      ScopedRuleMatching.instantiateArgsWith? operation rule spec ambient site path depth left index patterns =
        some results →
      ∃ otherResults, ScopedRuleMatching.instantiateArgsWith? operation rule spec ambient site path depth right index
        patterns = some otherResults ∧ List.Forall₂ Same results otherResults
  | [], site, path, depth, left, right, index, results, same, found => by
    rw [ScopedRuleMatching.instantiateArgsWith?] at found ⊢
    simp only [Option.some.injEq] at found
    subst found
    exact ⟨[], rfl, .nil⟩
  | pattern :: patterns, site, path, depth, left, right, index, results, same, found => by
    rw [ScopedRuleMatching.instantiateArgsWith?] at found ⊢
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
    obtain ⟨head, headFound, tail, tailFound, rfl⟩ := found
    obtain ⟨otherHead, otherHeadFound, headSame⟩ :=
      instantiateWith?_same operation respects pattern site (path ++ [index]) depth left right head same headFound
    obtain ⟨otherTail, otherTailFound, tailSame⟩ :=
      instantiateArgsWith?_same operation respects patterns site path depth left right (index + 1) tail same tailFound
    exact ⟨_, ⟨otherHead, otherHeadFound, otherTail, otherTailFound, rfl⟩, .cons headSame tailSame⟩
termination_by patterns => sizeOf patterns
end

/-- **An unconditional rule's steps from permutation-equal terms are permutation-equal**: every
result from one term has a permutation-equal result from the other. -/
theorem applyRule_same_unconditional (relEnv : Engine.RelationEnv) (lang : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (unconditional : rule.premises = []) (setFreeLeft : setFree rule.left = true)
    {term other : Pattern} (same : Same term other) {result : Pattern}
    (stepped : result ∈ ScopedRuleExecution.applyRuleComparedWithAt canonCompare Substitution.instantiateBVar
      relEnv lang ambient rule term) :
    ∃ otherResult ∈ ScopedRuleExecution.applyRuleComparedWithAt canonCompare Substitution.instantiateBVar
      relEnv lang ambient rule other, Same result otherResult := by
  obtain ⟨spec, captured, assignment, bindings, admitted, matched, completed, reduced⟩ :=
    (ScopedRuleExecution.mem_applyRuleComparedWithAt_iff _ _ _ _ _ _ _ _).mp stepped
  simp only [ScopedRuleExecution.completeAssignments, unconditional, List.mem_singleton] at completed
  rw [completed] at reduced
  obtain ⟨otherCaptured, otherMatched, capturedSame⟩ :=
    matchAtWith_same rule spec ambient rule.left .left [] 0 [] [] term other setFreeLeft List.Forall₂.nil same captured
      matched
  obtain ⟨otherResult, otherReduced, resultSame⟩ :=
    instantiateWith?_same rule spec ambient Substitution.instantiateBVar (fun a b => instantiateBVar_same a b)
      rule.right .right [] 0 captured otherCaptured result capturedSame reduced
  refine ⟨otherResult, (ScopedRuleExecution.mem_applyRuleComparedWithAt_iff _ _ _ _ _ _ _ _).mpr
    ⟨spec, otherCaptured, otherCaptured, bindings, admitted, otherMatched, ?_, otherReduced⟩, resultSame⟩
  simp [ScopedRuleExecution.completeAssignments, unconditional]

/-! ## The collection laws as steps -/

open CollectionLaws in
/-- One law move, in any context: a permutation of an unordered collection, a re-presentation
of a set by the same elements, the splicing of a nested collection of a flattening kind, or the
removal of a declared unit. -/
inductive LawStep (laws : List Laws) : Pattern → Pattern → Prop where
  | permute {kind : CollType} {elements permuted : List Pattern} {rest : Option String} :
      Unordered kind = true → elements.Perm permuted →
      LawStep laws (.collection kind elements rest) (.collection kind permuted rest)
  | members {elements others : List Pattern} {rest : Option String} :
      (∀ a, a ∈ elements ↔ a ∈ others) →
      LawStep laws (.collection .hashSet elements rest) (.collection .hashSet others rest)
  | flatten {kind : CollType} {law : Laws} {before inner after : List Pattern} {rest : Option String} :
      lawFor laws kind = some law →
      LawStep laws (.collection kind (before ++ .collection kind inner none :: after) rest)
        (.collection kind (before ++ inner ++ after) rest)
  | unit {kind : CollType} {law : Laws} {label : String} {before after : List Pattern} {rest : Option String} :
      lawFor laws kind = some law → law.unit = some label →
      LawStep laws (.collection kind (before ++ .apply label [] :: after) rest) (.collection kind (before ++ after) rest)
  | apply {label : String} {before after : List Pattern} {argument changed : Pattern} :
      LawStep laws argument changed →
      LawStep laws (.apply label (before ++ argument :: after)) (.apply label (before ++ changed :: after))
  | lambda {binder : Option String} {body changed : Pattern} :
      LawStep laws body changed → LawStep laws (.lambda binder body) (.lambda binder changed)
  | multiLambda {arity : Nat} {binders : List String} {body changed : Pattern} :
      LawStep laws body changed →
      LawStep laws (.multiLambda arity binders body) (.multiLambda arity binders changed)
  | substBody {body changed replacement : Pattern} :
      LawStep laws body changed → LawStep laws (.subst body replacement) (.subst changed replacement)
  | substReplacement {body replacement changed : Pattern} :
      LawStep laws replacement changed → LawStep laws (.subst body replacement) (.subst body changed)
  | element {kind : CollType} {before after : List Pattern} {element changed : Pattern} {rest : Option String} :
      LawStep laws element changed →
      LawStep laws (.collection kind (before ++ element :: after) rest) (.collection kind (before ++ changed :: after) rest)

/-- A permutation is a law move. -/
theorem BagStep.lawStep (laws : List CollectionLaws.Laws) {left right : Pattern} (step : BagStep left right) :
    LawStep laws left right := by
  induction step with
  | permute unordered permutation => exact .permute unordered permutation
  | members same => exact .members same
  | apply _ ih => exact .apply ih
  | lambda _ ih => exact .lambda ih
  | multiLambda _ ih => exact .multiLambda ih
  | substBody _ ih => exact .substBody ih
  | substReplacement _ ih => exact .substReplacement ih
  | element _ ih => exact .element ih

private theorem liftLaw (laws : List CollectionLaws.Laws) {f : Pattern → Pattern}
    (step : ∀ {a b : Pattern}, LawStep laws a b → LawStep laws (f a) (f b))
    {a b : Pattern} (related : Relation.EqvGen (LawStep laws) a b) : Relation.EqvGen (LawStep laws) (f a) (f b) := by
  induction related with
  | rel _ _ inner => exact .rel _ _ (step inner)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

private theorem alongLaw (laws : List CollectionLaws.Laws) (g : Pattern → Pattern) (wrap : List Pattern → Pattern)
    (inside : ∀ (before after : List Pattern) {a b : Pattern}, LawStep laws a b →
      LawStep laws (wrap (before ++ a :: after)) (wrap (before ++ b :: after))) :
    ∀ (before items : List Pattern), (∀ item ∈ items, Relation.EqvGen (LawStep laws) item (g item)) →
      Relation.EqvGen (LawStep laws) (wrap (before ++ items)) (wrap (before ++ items.map g))
  | before, [], _ => by simpa using Relation.EqvGen.refl _
  | before, item :: rest, each => by
    have first : Relation.EqvGen (LawStep laws) (wrap (before ++ item :: rest)) (wrap (before ++ g item :: rest)) :=
      liftLaw laws (f := fun x => wrap (before ++ x :: rest)) (fun step => inside before rest step) (each item (by simp))
    have later := alongLaw laws g wrap inside (before ++ [g item]) rest (fun other member => each other (by simp [member]))
    simp only [List.append_assoc, List.singleton_append] at later
    simp only [List.map_cons]
    exact .trans _ _ _ first later

open CollectionLaws in
/-- Splicing every element of a collection of a flattening kind is a sequence of law moves. -/
private theorem spliced (laws : List Laws) {kind : CollType} {law : Laws} (found : lawFor laws kind = some law)
    (rest : Option String) : ∀ (before items : List Pattern),
      Relation.EqvGen (LawStep laws) (.collection kind (before ++ items) rest)
        (.collection kind (before ++ items.flatMap (splice law)) rest)
  | before, [] => by simpa using Relation.EqvGen.refl _
  | before, item :: tail => by
    have kindIs : law.kind = kind := by
      have := List.find?_some found; simpa using this
    rw [List.flatMap_cons]
    cases item with
    | collection actual inner innerRest =>
      cases innerRest with
      | none =>
        by_cases same : actual = law.kind
        · rw [show actual = kind from same.trans kindIs]
          have move : LawStep laws (.collection kind (before ++ .collection kind inner none :: tail) rest)
              (.collection kind (before ++ inner ++ tail) rest) := .flatten found
          have later := spliced laws found rest (before ++ inner) tail
          have spl : splice law (.collection kind inner none) = inner := by simp [splice, kindIs]
          rw [spl]
          simp only [List.append_assoc] at later move ⊢
          exact .trans _ _ _ (.rel _ _ move) later
        · have later := spliced laws found rest (before ++ [.collection actual inner none]) tail
          simp only [splice, same, if_false, List.append_assoc, List.singleton_append] at later ⊢
          exact later
      | some name =>
        have later := spliced laws found rest (before ++ [.collection actual inner (some name)]) tail
        simp only [splice, List.append_assoc, List.singleton_append] at later ⊢
        exact later
    | apply label arguments =>
      cases arguments with
      | nil =>
        by_cases unit : law.unit = some label
        · have move : LawStep laws (.collection kind (before ++ .apply label [] :: tail) rest)
              (.collection kind (before ++ tail) rest) := .unit found unit
          have later := spliced laws found rest before tail
          simp only [splice, unit, if_true, List.nil_append] at later ⊢
          exact .trans _ _ _ (.rel _ _ move) later
        · have later := spliced laws found rest (before ++ [.apply label []]) tail
          simp only [splice, unit, if_false, List.append_assoc, List.singleton_append] at later ⊢
          exact later
      | cons first others =>
        have later := spliced laws found rest (before ++ [.apply label (first :: others)]) tail
        simp only [splice, List.append_assoc, List.singleton_append] at later ⊢
        exact later
    | bvar index =>
      have later := spliced laws found rest (before ++ [.bvar index]) tail
      simp only [splice, List.append_assoc, List.singleton_append] at later ⊢; exact later
    | fvar name =>
      have later := spliced laws found rest (before ++ [.fvar name]) tail
      simp only [splice, List.append_assoc, List.singleton_append] at later ⊢; exact later
    | lambda binder body =>
      have later := spliced laws found rest (before ++ [.lambda binder body]) tail
      simp only [splice, List.append_assoc, List.singleton_append] at later ⊢; exact later
    | multiLambda arity binders body =>
      have later := spliced laws found rest (before ++ [.multiLambda arity binders body]) tail
      simp only [splice, List.append_assoc, List.singleton_append] at later ⊢; exact later
    | subst body replacement =>
      have later := spliced laws found rest (before ++ [.subst body replacement]) tail
      simp only [splice, List.append_assoc, List.singleton_append] at later ⊢; exact later

open CollectionLaws in
/-- **The collection-law normal form is sound**: every term is related to it by law moves. -/
theorem to_normalize (laws : List Laws) : ∀ pattern : Pattern,
    Relation.EqvGen (LawStep laws) pattern (normalize laws pattern)
  | .bvar index => by rw [normalize]; exact .refl _
  | .fvar name => by rw [normalize]; exact .refl _
  | .apply label arguments => by
    rw [normalize]
    have each : ∀ item ∈ arguments, Relation.EqvGen (LawStep laws) item (normalize laws item) := fun item member =>
      have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
      to_normalize laws item
    simpa using alongLaw laws (normalize laws) (fun items => .apply label items) (fun before after _ _ step => .apply step)
      [] arguments each
  | .lambda binder body => by
    rw [normalize]; exact liftLaw laws (f := .lambda binder) (fun step => .lambda step) (to_normalize laws body)
  | .multiLambda arity binders body => by
    rw [normalize]
    exact liftLaw laws (f := .multiLambda arity binders) (fun step => .multiLambda step) (to_normalize laws body)
  | .subst body replacement => by
    rw [normalize]
    exact .trans _ _ _ (liftLaw laws (f := fun x => .subst x replacement) (fun step => .substBody step) (to_normalize laws body))
      (liftLaw laws (f := fun x => .subst (normalize laws body) x) (fun step => .substReplacement step)
        (to_normalize laws replacement))
  | .collection kind elements rest => by
    rw [normalize]
    have each : ∀ item ∈ elements, Relation.EqvGen (LawStep laws) item (normalize laws item) := fun item member =>
      have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
      to_normalize laws item
    have mapped : Relation.EqvGen (LawStep laws) (.collection kind elements rest)
        (.collection kind (elements.map (normalize laws)) rest) := by
      simpa using alongLaw laws (normalize laws) (fun items => .collection kind items rest)
        (fun before after _ _ step => .element step) [] elements each
    split
    · rename_i law found
      exact .trans _ _ _ mapped (by simpa using spliced laws found rest [] (elements.map (normalize laws)))
    · exact mapped
termination_by pattern => sizeOf pattern

/-- **The full normal form** for the collection laws: flattened, units removed, bags sorted. -/
def lawNormal (laws : List CollectionLaws.Laws) (pattern : Pattern) : Pattern := canon (CollectionLaws.normalize laws pattern)

/-- **The full normal form is sound.** -/
theorem to_lawNormal (laws : List CollectionLaws.Laws) (pattern : Pattern) :
    Relation.EqvGen (LawStep laws) pattern (lawNormal laws pattern) := by
  have asLaw : ∀ {a b : Pattern}, Relation.EqvGen BagStep a b → Relation.EqvGen (LawStep laws) a b := by
    intro a b related
    induction related with
    | rel _ _ step => exact .rel _ _ (step.lawStep laws)
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ first second => exact .trans _ _ _ first second
  exact .trans _ _ _ (to_normalize laws pattern) (asLaw (to_canon _))

open CollectionLaws in
theorem normalize_collection (laws : List Laws) (kind : CollType) (elements : List Pattern) (rest : Option String) :
    normalize laws (.collection kind elements rest) =
      match lawFor laws kind with
      | some law => .collection kind ((elements.map (normalize laws)).flatMap (splice law)) rest
      | none => .collection kind (elements.map (normalize laws)) rest := by
  rw [normalize]; rfl

open CollectionLaws in
/-- **Splicing pieces with one canonical form gives pieces the law's kind presents alike**: equal
for a vector, a permutation for a bag, the same elements for a set. -/
theorem splice_same_presents (law : Laws) {left right : Pattern} (same : Same left right) :
    Presents law.kind ((splice law left).map canon) ((splice law right).map canon) := by
  cases left with
  | collection kind elements rest =>
    obtain ⟨others, rfl, arranged⟩ := same_collection same
    cases rest with
    | none =>
      by_cases match_ : kind = law.kind
      · subst match_
        simp only [splice, if_true]
        exact arrange_eq arranged
      · simp only [splice, match_, if_false, List.map_cons, List.map_nil]
        rw [show canon (.collection kind elements none) = canon (.collection kind others none) from same]
        exact Presents.refl _ _
    | some name =>
      simp only [splice, List.map_cons, List.map_nil]
      rw [show canon (.collection kind elements (some name)) = canon (.collection kind others (some name)) from same]
      exact Presents.refl _ _
  | apply label arguments =>
    obtain ⟨others, rfl, mapped⟩ := same_apply same
    cases arguments with
    | nil =>
      cases others with
      | nil => exact Presents.refl _ _
      | cons _ _ => simp at mapped
    | cons first tail =>
      cases others with
      | nil => simp at mapped
      | cons otherFirst otherTail =>
        simp only [splice, List.map_cons, List.map_nil]
        rw [show canon (.apply label (first :: tail)) = canon (.apply label (otherFirst :: otherTail)) from same]
        exact Presents.refl _ _
  | bvar index => rw [same_bvar same]; exact Presents.refl _ _
  | fvar name => rw [same_fvar same]; exact Presents.refl _ _
  | lambda binder body =>
    obtain ⟨otherBinder, otherBody, rfl, _⟩ := same_lambda same
    simp only [splice, List.map_cons, List.map_nil]
    rw [show canon (.lambda binder body) = canon (.lambda otherBinder otherBody) from same]
    exact Presents.refl _ _
  | multiLambda arity binders body =>
    obtain ⟨otherBinders, otherBody, rfl, _⟩ := same_multiLambda same
    simp only [splice, List.map_cons, List.map_nil]
    rw [show canon (.multiLambda arity binders body) = canon (.multiLambda arity otherBinders otherBody) from same]
    exact Presents.refl _ _
  | subst body replacement =>
    obtain ⟨otherBody, otherReplacement, rfl, _⟩ := same_subst same
    simp only [splice, List.map_cons, List.map_nil]
    rw [show canon (.subst body replacement) = canon (.subst otherBody otherReplacement) from same]
    exact Presents.refl _ _

open CollectionLaws in
/-- For a bag kind, splicing permutation-equal pieces gives permutation-equal canonical pieces. -/
theorem splice_same (law : Laws) (bag : law.kind = .hashBag) {left right : Pattern} (same : Same left right) :
    ((splice law left).map canon).Perm ((splice law right).map canon) := by
  have presents := splice_same_presents law same
  rw [bag] at presents
  exact presents

open CollectionLaws in
/-- For an ordered flattening kind, splicing permutation-equal pieces gives equal canonical pieces. -/
theorem splice_same_eq (law : Laws) (ordered : Unordered law.kind = false) {left right : Pattern}
    (same : Same left right) : (splice law left).map canon = (splice law right).map canon :=
  presents_eq_of_ordered ordered (splice_same_presents law same)

/-- Collections whose canonical elements the kind presents alike have one canonical form. -/
theorem canon_collection_of_presents (kind : CollType) (rest : Option String) {left right : List Pattern}
    (presents : Presents kind (left.map canon) (right.map canon)) :
    canon (.collection kind left rest) = canon (.collection kind right rest) := by
  rw [canon_collection, canon_collection, arrange_eq_of_presents presents]

theorem canon_collection_of (kind : CollType) (rest : Option String) {left right : List Pattern}
    (unordered : Unordered kind = true → (left.map canon).Perm (right.map canon))
    (ordered : Unordered kind = false → left.map canon = right.map canon) :
    canon (.collection kind left rest) = canon (.collection kind right rest) := by
  apply canon_collection_of_presents
  cases mode : Unordered kind
  · cases kind with
    | vec => exact ordered mode
    | hashBag => simp [Unordered] at mode
    | hashSet => simp [Unordered] at mode
  · exact presents_of_perm mode (unordered mode)

private theorem map_middle_congr (f : Pattern → Pattern) (before after : List Pattern) {x y : Pattern}
    (same : f x = f y) : (before ++ x :: after).map f = (before ++ y :: after).map f := by
  simp [same]

open CollectionLaws in
/-- **Every law move keeps the full normal form.** -/
theorem LawStep.lawNormal_eq (laws : List Laws) {left right : Pattern} (step : LawStep laws left right) :
    lawNormal laws left = lawNormal laws right := by
  unfold lawNormal
  induction step with
  | @permute kind elements permuted rest unordered permutation =>
    rw [normalize_collection, normalize_collection]
    split
    · rename_i law _
      apply canon_collection_of kind rest
      · intro _; exact ((permutation.map _).flatMap_right _).map canon
      · intro ordered; rw [unordered] at ordered; cases ordered
    · apply canon_collection_of kind rest
      · intro _; exact (permutation.map _).map canon
      · intro ordered; rw [unordered] at ordered; cases ordered
  | @members elements others rest same =>
    rw [normalize_collection, normalize_collection]
    split
    · rename_i law _
      exact canon_collection_of_presents .hashSet rest
        (members_map (members_flatMap (members_map same _) (splice law)) canon)
    · exact canon_collection_of_presents .hashSet rest (members_map (members_map same _) canon)
  | @flatten kind law before inner after rest found =>
    have kindIs : law.kind = kind := lawFor_kind found
    congr 1
    rw [normalize_collection, normalize_collection, found]
    simp only [List.map_append, List.map_cons, List.flatMap_append, List.flatMap_cons]
    rw [normalize_collection, found]
    simp [splice, kindIs]
  | @unit kind law label before after rest found isUnit =>
    congr 1
    rw [normalize_collection, normalize_collection, found]
    simp only [List.map_append, List.map_cons, List.flatMap_append, List.flatMap_cons]
    rw [normalize]
    simp [splice, isUnit]
  | @apply label before after argument changed _ ih =>
    rw [normalize, normalize, canon_apply, canon_apply]
    simp only [List.map_map]
    congr 1
    exact map_middle_congr (canon ∘ normalize laws) before after (by simpa using ih)
  | lambda _ ih => simp only [normalize, canon, ih]
  | multiLambda _ ih => simp only [normalize, canon, ih]
  | substBody _ ih => simp only [normalize, canon, ih]
  | substReplacement _ ih => simp only [normalize, canon, ih]
  | @element kind before after element changed rest _ ih =>
    rw [normalize_collection, normalize_collection]
    split
    · rename_i law found
      have kindIs : law.kind = kind := lawFor_kind found
      apply canon_collection_of_presents kind rest
      simp only [List.map_append, List.map_cons, List.flatMap_append, List.flatMap_cons, List.map_append]
      have presents := splice_same_presents law ih
      rw [kindIs] at presents
      exact Presents.surround _ _ presents
    · apply canon_collection_of_presents kind rest
      simp only [List.map_map]
      exact Presents.of_eq (map_middle_congr (canon ∘ normalize laws) before after (by simpa using ih))

/-- **The full normal form decides the collection laws**: two terms have one normal form exactly
when finitely many law moves relate them. -/
theorem lawNormal_iff (laws : List CollectionLaws.Laws) (left right : Pattern) :
    lawNormal laws left = lawNormal laws right ↔ Relation.EqvGen (LawStep laws) left right := by
  constructor
  · intro same
    have toRight := to_lawNormal laws right
    rw [← same] at toRight
    exact .trans _ _ _ (to_lawNormal laws left) (.symm _ _ toRight)
  · intro related
    induction related with
    | rel _ _ step => exact step.lawNormal_eq laws
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ first second => exact first.trans second

/-! ## Scope extrusion as a move -/

open CollectionLaws in
/-- A standard-form move, in any context: a law move, or one declared scope extrusion
`{(B ^x.P), ...rest} = (B ^x.{P, ...rest})` read left to right (the rest moves under the binder
with its indices lifted). -/
inductive StandardStep (laws : List Laws) (extrusions : List Extrusion) : Pattern → Pattern → Prop where
  | law {left right : Pattern} : LawStep laws left right → StandardStep laws extrusions left right
  | extrude {extrusion : Extrusion} {display : Option String} {body : Pattern} {others : List Pattern} :
      extrusion ∈ extrusions →
      StandardStep laws extrusions (.collection extrusion.kind (.apply extrusion.binder [.lambda display body] :: others) none)
        (.apply extrusion.binder [.lambda display (.collection extrusion.kind (body :: others.map (Substitution.liftBVars 0 1)) none)])
  | apply {label : String} {before after : List Pattern} {argument changed : Pattern} :
      StandardStep laws extrusions argument changed →
      StandardStep laws extrusions (.apply label (before ++ argument :: after)) (.apply label (before ++ changed :: after))
  | lambda {binder : Option String} {body changed : Pattern} :
      StandardStep laws extrusions body changed →
      StandardStep laws extrusions (.lambda binder body) (.lambda binder changed)
  | multiLambda {arity : Nat} {binders : List String} {body changed : Pattern} :
      StandardStep laws extrusions body changed →
      StandardStep laws extrusions (.multiLambda arity binders body) (.multiLambda arity binders changed)
  | substBody {body changed replacement : Pattern} :
      StandardStep laws extrusions body changed →
      StandardStep laws extrusions (.subst body replacement) (.subst changed replacement)
  | substReplacement {body replacement changed : Pattern} :
      StandardStep laws extrusions replacement changed →
      StandardStep laws extrusions (.subst body replacement) (.subst body changed)
  | element {kind : CollType} {before after : List Pattern} {element changed : Pattern} {rest : Option String} :
      StandardStep laws extrusions element changed →
      StandardStep laws extrusions (.collection kind (before ++ element :: after) rest)
        (.collection kind (before ++ changed :: after) rest)

open CollectionLaws in
private theorem liftStandard (laws : List Laws) (extrusions : List Extrusion) {f : Pattern → Pattern}
    (step : ∀ {a b : Pattern}, StandardStep laws extrusions a b → StandardStep laws extrusions (f a) (f b))
    {a b : Pattern} (related : Relation.EqvGen (StandardStep laws extrusions) a b) :
    Relation.EqvGen (StandardStep laws extrusions) (f a) (f b) := by
  induction related with
  | rel _ _ inner => exact .rel _ _ (step inner)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

open CollectionLaws in
private theorem ofLaw (laws : List Laws) (extrusions : List Extrusion) {a b : Pattern}
    (related : Relation.EqvGen (LawStep laws) a b) : Relation.EqvGen (StandardStep laws extrusions) a b := by
  induction related with
  | rel _ _ step => exact .rel _ _ (.law step)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

open CollectionLaws in
/-- Splicing a hoisted body's own elements is flattening. -/
private theorem bodyItems_flatten (laws : List Laws) {kind : CollType} {law : Laws} (found : lawFor laws kind = some law)
    (before after : List Pattern) (body : Pattern) :
    Relation.EqvGen (LawStep laws) (.collection kind (before ++ body :: after) none)
      (.collection kind (before ++ bodyItems kind body ++ after) none) := by
  unfold bodyItems
  split
  · rename_i actual elements
    by_cases same : actual = kind
    · subst same
      simp only [if_true]
      exact .rel _ _ (.flatten found)
    · simp only [same, if_false, List.singleton_append, List.append_assoc]
      exact .refl _
  · simp only [List.singleton_append, List.append_assoc]
    exact .refl _

open CollectionLaws in
/-- **Hoisting is a sequence of standard moves**, for an extrusion over an unordered kind that
flattens. -/
theorem to_hoist (laws : List Laws) (extrusions : List Extrusion) {extrusion : Extrusion}
    (declared : extrusion ∈ extrusions) (unordered : Unordered extrusion.kind = true)
    {law : Laws} (flattens : lawFor laws extrusion.kind = some law) :
    ∀ (fuel : Nat) (done todo : List Pattern),
      Relation.EqvGen (StandardStep laws extrusions) (.collection extrusion.kind (done ++ todo) none)
        (hoist extrusion fuel done todo)
  | 0, done, todo => by unfold hoist; exact .refl _
  | fuel + 1, done, [] => by unfold hoist; simpa using Relation.EqvGen.refl _
  | fuel + 1, done, item :: todo => by
    unfold hoist
    split
    · rename_i label display body
      split
      · rename_i isBinder
        subst isBinder
        -- bring the binder element to the front, extrude, then rearrange under the binder
        have front : Relation.EqvGen (StandardStep laws extrusions)
            (.collection extrusion.kind (done ++ .apply extrusion.binder [.lambda display body] :: todo) none)
            (.collection extrusion.kind (.apply extrusion.binder [.lambda display body] :: (done ++ todo)) none) :=
          .rel _ _ (.law (.permute unordered (List.perm_middle)))
        have out : Relation.EqvGen (StandardStep laws extrusions)
            (.collection extrusion.kind (.apply extrusion.binder [.lambda display body] :: (done ++ todo)) none)
            (.apply extrusion.binder [.lambda display (.collection extrusion.kind
              (body :: (done ++ todo).map (Substitution.liftBVars 0 1)) none)]) :=
          .rel _ _ (.extrude declared)
        have arrange : Relation.EqvGen (StandardStep laws extrusions)
            (.collection extrusion.kind (body :: (done ++ todo).map (Substitution.liftBVars 0 1)) none)
            (.collection extrusion.kind (done.map (Substitution.liftBVars 0 1) ++
              (bodyItems extrusion.kind body ++ todo.map (Substitution.liftBVars 0 1))) none) := by
          have moved : Relation.EqvGen (StandardStep laws extrusions)
              (.collection extrusion.kind (body :: (done ++ todo).map (Substitution.liftBVars 0 1)) none)
              (.collection extrusion.kind (done.map (Substitution.liftBVars 0 1) ++ body ::
                todo.map (Substitution.liftBVars 0 1)) none) := by
            refine .rel _ _ (.law (.permute unordered ?_))
            simp only [List.map_append]
            exact List.perm_middle.symm
          refine .trans _ _ _ moved ?_
          have spliced := ofLaw laws extrusions (bodyItems_flatten laws flattens
            (done.map (Substitution.liftBVars 0 1)) (todo.map (Substitution.liftBVars 0 1)) body)
          simpa only [List.append_assoc] using spliced
        have inner := to_hoist laws extrusions declared unordered flattens fuel
          (done.map (Substitution.liftBVars 0 1)) (bodyItems extrusion.kind body ++ todo.map (Substitution.liftBVars 0 1))
        have underBinder := liftStandard laws extrusions
          (f := fun x => .apply extrusion.binder [.lambda display x])
          (fun step => by simpa using (StandardStep.apply (before := []) (after := []) (StandardStep.lambda step)))
          (.trans _ _ _ arrange inner)
        exact .trans _ _ _ front (.trans _ _ _ out underBinder)
      · have later := to_hoist laws extrusions declared unordered flattens fuel (done ++ [.apply label [.lambda display body]]) todo
        simpa [List.append_assoc] using later
    · rename_i other _
      have later := to_hoist laws extrusions declared unordered flattens fuel (done ++ [item]) todo
      simpa [List.append_assoc] using later

open CollectionLaws in
private theorem alongStandard (laws : List Laws) (extrusions : List Extrusion) (g : Pattern → Pattern)
    (wrap : List Pattern → Pattern)
    (inside : ∀ (before after : List Pattern) {a b : Pattern}, StandardStep laws extrusions a b →
      StandardStep laws extrusions (wrap (before ++ a :: after)) (wrap (before ++ b :: after))) :
    ∀ (before items : List Pattern), (∀ item ∈ items, Relation.EqvGen (StandardStep laws extrusions) item (g item)) →
      Relation.EqvGen (StandardStep laws extrusions) (wrap (before ++ items)) (wrap (before ++ items.map g))
  | before, [], _ => by simpa using Relation.EqvGen.refl _
  | before, item :: rest, each => by
    have first : Relation.EqvGen (StandardStep laws extrusions) (wrap (before ++ item :: rest))
        (wrap (before ++ g item :: rest)) :=
      liftStandard laws extrusions (f := fun x => wrap (before ++ x :: rest)) (fun step => inside before rest step)
        (each item (by simp))
    have later := alongStandard laws extrusions g wrap inside (before ++ [g item]) rest
      (fun other member => each other (by simp [member]))
    simp only [List.append_assoc, List.singleton_append] at later
    simp only [List.map_cons]
    exact .trans _ _ _ first later

open CollectionLaws in
/-- Every declared extrusion is over an unordered kind that flattens. -/
def ExtrusionsFlatten (laws : List Laws) (extrusions : List Extrusion) : Prop :=
  ∀ extrusion ∈ extrusions, Unordered extrusion.kind = true ∧ ∃ law, lawFor laws extrusion.kind = some law

open CollectionLaws in
/-- **Scope extrusion run bottom up is a sequence of standard moves.** -/
theorem to_extrude (laws : List Laws) (extrusions : List Extrusion) (flatten : ExtrusionsFlatten laws extrusions) :
    ∀ pattern : Pattern, Relation.EqvGen (StandardStep laws extrusions) pattern (extrude extrusions pattern)
  | .bvar index => by rw [extrude]; exact .refl _
  | .fvar name => by rw [extrude]; exact .refl _
  | .apply label arguments => by
    rw [extrude]
    have each : ∀ item ∈ arguments, Relation.EqvGen (StandardStep laws extrusions) item (extrude extrusions item) :=
      fun item member =>
        have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
          have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
        to_extrude laws extrusions flatten item
    simpa using alongStandard laws extrusions (extrude extrusions) (fun items => .apply label items)
      (fun before after _ _ step => .apply step) [] arguments each
  | .lambda binder body => by
    rw [extrude]
    exact liftStandard laws extrusions (f := .lambda binder) (fun step => .lambda step) (to_extrude laws extrusions flatten body)
  | .multiLambda arity binders body => by
    rw [extrude]
    exact liftStandard laws extrusions (f := .multiLambda arity binders) (fun step => .multiLambda step)
      (to_extrude laws extrusions flatten body)
  | .subst body replacement => by
    rw [extrude]
    exact .trans _ _ _
      (liftStandard laws extrusions (f := fun x => .subst x replacement) (fun step => .substBody step)
        (to_extrude laws extrusions flatten body))
      (liftStandard laws extrusions (f := fun x => .subst (extrude extrusions body) x) (fun step => .substReplacement step)
        (to_extrude laws extrusions flatten replacement))
  | .collection kind elements rest => by
    rw [extrude.eq_def]
    simp only
    have each : ∀ item ∈ elements, Relation.EqvGen (StandardStep laws extrusions) item (extrude extrusions item) :=
      fun item member =>
        have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
          have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
        to_extrude laws extrusions flatten item
    have mapped : Relation.EqvGen (StandardStep laws extrusions) (.collection kind elements rest)
        (.collection kind (elements.map (extrude extrusions)) rest) := by
      simpa using alongStandard laws extrusions (extrude extrusions) (fun items => .collection kind items rest)
        (fun before after _ _ step => .element step) [] elements each
    cases rest with
    | some name => exact mapped
    | none =>
      dsimp only
      split
      · rename_i extrusion found
        have kindIs : extrusion.kind = kind := by simpa using List.find?_some found
        have declared : extrusion ∈ extrusions := List.mem_of_find?_eq_some found
        obtain ⟨unordered, law, flattens⟩ := flatten extrusion declared
        subst kindIs
        have hoisted := to_hoist laws extrusions declared unordered flattens
          (2 * ((elements.map (extrude extrusions)).map PatternTreeSize.nodes).sum +
            (elements.map (extrude extrusions)).length + 1) [] (elements.map (extrude extrusions))
        simp only [List.nil_append] at hoisted
        exact .trans _ _ _ mapped hoisted
      · exact mapped
termination_by pattern => sizeOf pattern

open CollectionLaws in
/-- **The standard form is sound**: every term is related to its standard form by standard moves
(law moves and declared scope extrusions). -/
theorem to_standardForm (laws : List Laws) (extrusions : List Extrusion) (flatten : ExtrusionsFlatten laws extrusions)
    (pattern : Pattern) :
    Relation.EqvGen (StandardStep laws extrusions) pattern (standardForm laws extrusions pattern) :=
  .trans _ _ _ (ofLaw laws extrusions (to_normalize laws pattern)) (to_extrude laws extrusions flatten _)

end Capture

end Mettapedia.OSLF.MeTTaIL.CanonicalBags
