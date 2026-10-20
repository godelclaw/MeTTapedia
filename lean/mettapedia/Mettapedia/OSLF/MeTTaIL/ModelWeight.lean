import Mettapedia.OSLF.MeTTaIL.WrapperNormal
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# A weight for the model's normal forms

The weight of a term counts its nodes, a collection twice. Each normal form of the model's laws is
either the term itself or strictly lighter: splicing a nested collection removes a collection node,
dropping a unit removes a node, collapsing a singleton removes a collection node, replacing an empty
collection by the unit trades a collection node for a constant, and collapsing a quote-drop pair removes
two nodes; the canonical form keeps the weight of a bag and drops a set's repetitions, so it never adds
weight (`weight_canon_le`). A term that every normal form keeps is a model normal form
(`normal_of_fixed`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Wrappers

open Syntax CollectionLaws CanonicalBags ReflectiveSubstitution QuoteDrop

/-- The weight of a term: its nodes, a collection twice. -/
def weight : Pattern → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .apply _ arguments => 1 + (arguments.map weight).sum
  | .lambda _ body => 1 + weight body
  | .multiLambda _ _ body => 1 + weight body
  | .subst body replacement => 1 + weight body + weight replacement
  | .collection _ elements _ => 2 + (elements.map weight).sum
decreasing_by all_goals sizeOf_pattern_dec

theorem weight_apply (label : String) (arguments : List Pattern) :
    weight (.apply label arguments) = 1 + (arguments.map weight).sum := by rw [weight]

theorem weight_collection (kind : CollType) (elements : List Pattern) (rest : Option String) :
    weight (.collection kind elements rest) = 2 + (elements.map weight).sum := by rw [weight]

theorem weight_lambda (binder : Option String) (body : Pattern) : weight (.lambda binder body) = 1 + weight body := by
  rw [weight]

theorem weight_multiLambda (arity : Nat) (binders : List String) (body : Pattern) :
    weight (.multiLambda arity binders body) = 1 + weight body := by rw [weight]

theorem weight_subst (body replacement : Pattern) :
    weight (.subst body replacement) = 1 + weight body + weight replacement := by rw [weight]

/-- A map that keeps each element or makes it lighter keeps the list or makes its weight smaller. -/
theorem map_keeps_or_lighter {f : Pattern → Pattern} :
    ∀ {items : List Pattern}, (∀ item ∈ items, f item = item ∨ weight (f item) < weight item) →
      items.map f = items ∨ ((items.map f).map weight).sum < (items.map weight).sum
  | [], _ => .inl rfl
  | item :: rest, each => by
    have later := map_keeps_or_lighter (f := f) (items := rest) fun other member => each other (by simp [member])
    rcases each item (by simp) with same | lighter
    · rcases later with sameRest | lighterRest
      · exact .inl (by simp [same, sameRest])
      · exact .inr (by simp only [List.map_cons, List.sum_cons, same]; omega)
    · right
      simp only [List.map_cons, List.sum_cons]
      rcases later with sameRest | lighterRest
      · rw [sameRest]; omega
      · omega

theorem map_keeps_or_lighter_le {f : Pattern → Pattern} {items : List Pattern}
    (each : ∀ item ∈ items, f item = item ∨ weight (f item) < weight item) :
    ((items.map f).map weight).sum ≤ (items.map weight).sum := by
  rcases map_keeps_or_lighter each with same | lighter
  · rw [same]
  · exact lighter.le

theorem pair_keeps_or_lighter {first first' second second' : Pattern}
    (firstStep : first' = first ∨ weight first' < weight first)
    (secondStep : second' = second ∨ weight second' < weight second) :
    (first' = first ∧ second' = second) ∨ weight first' + weight second' < weight first + weight second := by
  rcases firstStep with same | lighter <;> rcases secondStep with same' | lighter'
  · exact .inl ⟨same, same'⟩
  · right; rw [same]; omega
  · right; rw [same']; omega
  · right; omega

/-! ## The canonical form adds no weight -/

/-- Arranging keeps a bag's or a vector's weight and drops a set's repetitions. -/
theorem weight_arrange_le (kind : CollType) (items : List Pattern) :
    ((arrange kind items).map weight).sum ≤ (items.map weight).sum := by
  cases kind with
  | vec => exact le_rfl
  | hashBag => exact (((PatternLexOrder.sortLex_perm items).map weight).sum_eq).le
  | hashSet =>
    calc ((arrange .hashSet items).map weight).sum
        ≤ ((PatternLexOrder.sortLex items).map weight).sum :=
          List.Sublist.sum_le_sum ((List.dedup_sublist _).map weight) (fun _ _ => Nat.zero_le _)
      _ = (items.map weight).sum := ((PatternLexOrder.sortLex_perm items).map weight).sum_eq

theorem weight_canon_le : ∀ pattern : Pattern, weight (canon pattern) ≤ weight pattern
  | .bvar index => by rw [canon]
  | .fvar name => by rw [canon]
  | .apply label arguments => by
    rw [canon, weight_apply, weight_apply, List.map_map]
    have each : (arguments.map (weight ∘ canon)).sum ≤ (arguments.map weight).sum :=
      List.sum_le_sum fun item member =>
        have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
          have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
        weight_canon_le item
    omega
  | .lambda binder body => by
    rw [canon, weight_lambda, weight_lambda]; have := weight_canon_le body; omega
  | .multiLambda arity binders body => by
    rw [canon, weight_multiLambda, weight_multiLambda]; have := weight_canon_le body; omega
  | .subst body replacement => by
    rw [canon, weight_subst, weight_subst]
    have := weight_canon_le body; have := weight_canon_le replacement; omega
  | .collection kind elements rest => by
    rw [canon, weight_collection, weight_collection]
    have arranged := weight_arrange_le kind (elements.map canon)
    rw [List.map_map] at arranged
    have each : (elements.map (weight ∘ canon)).sum ≤ (elements.map weight).sum :=
      List.sum_le_sum fun item member =>
        have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
          have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
        weight_canon_le item
    omega
termination_by pattern => sizeOf pattern

/-! ## The law normal form -/

/-- Splicing keeps an element or makes the parent lighter. -/
theorem splice_keeps_or_lighter (law : Laws) (item : Pattern) :
    splice law item = [item] ∨ ((splice law item).map weight).sum < weight item := by
  cases item with
  | collection kind elements rest =>
    cases rest with
    | none =>
      by_cases same : kind = law.kind
      · right; simp only [splice, same, if_true, weight_collection]; omega
      · left; simp [splice, same]
    | some name => left; simp [splice]
  | apply label arguments =>
    cases arguments with
    | nil =>
      by_cases unit : law.unit = some label
      · right; simp [splice, unit, weight_apply]
      · left; simp [splice, unit]
    | cons first rest => left; simp [splice]
  | _ => left; simp [splice]

theorem flatMap_splice_keeps_or_lighter (law : Laws) :
    ∀ items : List Pattern, items.flatMap (splice law) = items ∨
      ((items.flatMap (splice law)).map weight).sum < (items.map weight).sum
  | [] => .inl rfl
  | item :: rest => by
    have later := flatMap_splice_keeps_or_lighter law rest
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    rcases splice_keeps_or_lighter law item with same | lighter
    · rw [same]
      rcases later with sameRest | lighterRest
      · exact .inl (by simp [sameRest])
      · right; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · right
      rcases later with sameRest | lighterRest
      · rw [sameRest]; omega
      · omega

/-- **The law normal form keeps a term or makes it lighter.** -/
theorem normalize_keeps_or_lighter (laws : List Laws) :
    ∀ pattern : Pattern, normalize laws pattern = pattern ∨ weight (normalize laws pattern) < weight pattern
  | .bvar index => by rw [normalize]; exact .inl rfl
  | .fvar name => by rw [normalize]; exact .inl rfl
  | .apply label arguments => by
    rw [normalize]
    have each : ∀ item ∈ arguments, normalize laws item = item ∨ weight (normalize laws item) < weight item :=
      fun item member =>
        have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
          have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
        normalize_keeps_or_lighter laws item
    rcases map_keeps_or_lighter each with same | lighter
    · exact .inl (by rw [same])
    · right; rw [weight_apply, weight_apply]; omega
  | .lambda binder body => by
    rw [normalize]
    rcases normalize_keeps_or_lighter laws body with same | lighter
    · exact .inl (by rw [same])
    · right; rw [weight_lambda, weight_lambda]; omega
  | .multiLambda arity binders body => by
    rw [normalize]
    rcases normalize_keeps_or_lighter laws body with same | lighter
    · exact .inl (by rw [same])
    · right; rw [weight_multiLambda, weight_multiLambda]; omega
  | .subst body replacement => by
    rw [normalize]
    rcases pair_keeps_or_lighter (normalize_keeps_or_lighter laws body) (normalize_keeps_or_lighter laws replacement) with ⟨same, same'⟩ | lighter
    · exact .inl (by rw [same, same'])
    · right; rw [weight_subst, weight_subst]; omega
  | .collection kind elements rest => by
    have each : ∀ item ∈ elements, normalize laws item = item ∨ weight (normalize laws item) < weight item :=
      fun item member =>
        have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
          have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
        normalize_keeps_or_lighter laws item
    rw [normalize]
    split
    · rename_i law _
      rcases map_keeps_or_lighter each with same | lighter <;>
        rcases flatMap_splice_keeps_or_lighter law (elements.map (normalize laws)) with spliced | lighterSplice
      · exact .inl (by rw [spliced, same])
      · right; rw [weight_collection, weight_collection, same]; rw [same] at lighterSplice; omega
      · right; rw [weight_collection, weight_collection, spliced]; omega
      · right; rw [weight_collection, weight_collection]; omega
    · rcases map_keeps_or_lighter each with same | lighter
      · exact .inl (by rw [same])
      · right; rw [weight_collection, weight_collection]; omega
termination_by pattern => sizeOf pattern

/-! ## The wrapper normal form -/

/-- **The wrapper normal form keeps a term or makes it lighter.** -/
theorem wrapperNormal_keeps_or_lighter (laws : List Laws) :
    ∀ pattern : Pattern, wrapperNormal laws pattern = pattern ∨ weight (wrapperNormal laws pattern) < weight pattern
  | .bvar index => by rw [wrapperNormal_bvar]; exact .inl rfl
  | .fvar name => by rw [wrapperNormal_fvar]; exact .inl rfl
  | .apply label arguments => by
    rw [wrapperNormal_apply]
    have each : ∀ item ∈ arguments, wrapperNormal laws item = item ∨ weight (wrapperNormal laws item) < weight item :=
      fun item member =>
        have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
          have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
        wrapperNormal_keeps_or_lighter laws item
    rcases map_keeps_or_lighter each with same | lighter
    · exact .inl (by rw [same])
    · right; rw [weight_apply, weight_apply]; omega
  | .lambda binder body => by
    rw [wrapperNormal_lambda]
    rcases wrapperNormal_keeps_or_lighter laws body with same | lighter
    · exact .inl (by rw [same])
    · right; rw [weight_lambda, weight_lambda]; omega
  | .multiLambda arity binders body => by
    rw [wrapperNormal_multiLambda]
    rcases wrapperNormal_keeps_or_lighter laws body with same | lighter
    · exact .inl (by rw [same])
    · right; rw [weight_multiLambda, weight_multiLambda]; omega
  | .subst body replacement => by
    rw [wrapperNormal_subst]
    rcases pair_keeps_or_lighter (wrapperNormal_keeps_or_lighter laws body) (wrapperNormal_keeps_or_lighter laws replacement) with ⟨same, same'⟩ | lighter
    · exact .inl (by rw [same, same'])
    · right; rw [weight_subst, weight_subst]; omega
  | .collection kind elements rest => by
    have each : ∀ item ∈ elements, wrapperNormal laws item = item ∨ weight (wrapperNormal laws item) < weight item :=
      fun item member =>
        have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
          have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
        wrapperNormal_keeps_or_lighter laws item
    have mapped : Pattern.collection kind (elements.map (wrapperNormal laws)) rest = .collection kind elements rest ∨
        weight (.collection kind (elements.map (wrapperNormal laws)) rest) < weight (.collection kind elements rest) := by
      rcases map_keeps_or_lighter each with same | lighter
      · exact .inl (by rw [same])
      · right; rw [weight_collection, weight_collection]; omega
    cases found : lawFor laws kind with
    | none => rw [wrapperNormal_plain found]; exact mapped
    | some law =>
      rw [wrapperNormal_law found]
      unfold wrapFinish
      split
      · rename_i item same
        right
        obtain ⟨element, rfl, rfl⟩ : ∃ element, elements = [element] ∧ item = wrapperNormal laws element := by
          match elements, same with
          | [element], same => exact ⟨element, rfl, by simpa using same.symm⟩
        have le := map_keeps_or_lighter_le each
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at le
        rw [weight_collection]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega
      · rename_i same
        have empty : elements = [] := by simpa using same
        subst empty
        split
        · right; simp [weight_apply, weight_collection]
        · exact .inl rfl
      · exact mapped

/-! ## The quote-drop normal form -/

variable {declaration : ReflectivePresentationDecl}

/-- **The quote-drop normal form keeps a term or makes it lighter.** -/
theorem normal_keeps_or_lighter :
    ∀ pattern : Pattern, normal declaration pattern = pattern ∨ weight (normal declaration pattern) < weight pattern
  | .bvar index => by rw [normal_bvar]; exact .inl rfl
  | .fvar name => by rw [normal_fvar]; exact .inl rfl
  | .apply label arguments => by
    rw [normal_apply]
    have each : ∀ item ∈ arguments, normal declaration item = item ∨ weight (normal declaration item) < weight item :=
      fun item member =>
        have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
          have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
        normal_keeps_or_lighter item
    rcases finish_cases (declaration := declaration) label (arguments.map (normal declaration)) with kept | ⟨name, shape, collapsed⟩
    · rw [kept]
      rcases map_keeps_or_lighter each with same | lighter
      · exact .inl (by rw [same])
      · right; rw [weight_apply, weight_apply]; omega
    · right
      rw [collapsed]
      have le := map_keeps_or_lighter_le each
      rw [shape] at le
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, weight_apply] at le
      rw [weight_apply]
      omega
  | .lambda binder body => by
    rw [normal_lambda]
    rcases normal_keeps_or_lighter body with same | lighter
    · exact .inl (by rw [same])
    · right; rw [weight_lambda, weight_lambda]; omega
  | .multiLambda arity binders body => by
    rw [normal_multiLambda]
    rcases normal_keeps_or_lighter body with same | lighter
    · exact .inl (by rw [same])
    · right; rw [weight_multiLambda, weight_multiLambda]; omega
  | .subst body replacement => by
    rw [normal_subst]
    rcases pair_keeps_or_lighter (normal_keeps_or_lighter body) (normal_keeps_or_lighter replacement) with ⟨same, same'⟩ | lighter
    · exact .inl (by rw [same, same'])
    · right; rw [weight_subst, weight_subst]; omega
  | .collection kind elements rest => by
    rw [normal_collection]
    have each : ∀ item ∈ elements, normal declaration item = item ∨ weight (normal declaration item) < weight item :=
      fun item member =>
        have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
          have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
        normal_keeps_or_lighter item
    rcases map_keeps_or_lighter each with same | lighter
    · exact .inl (by rw [same])
    · right; rw [weight_collection, weight_collection]; omega
termination_by pattern => sizeOf pattern

end Mettapedia.OSLF.MeTTaIL.Wrappers
