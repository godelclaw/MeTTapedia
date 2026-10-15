import Mettapedia.OSLF.MeTTaIL.GeneralPremiseProjectionTotality

/-!
# Finite collection and atomic-name capture refinements

A rest occurrence matches an actual finite residual collection. Its stored
body preserves the collection tag and has no symbolic tail. Atomic provider
outputs similarly retain an actual free atom. These representation facts
are stronger than ordinary sort declarations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching ContextSubstitution

def restCaptureNames : Pattern → List String
  | .fvar _ | .bvar _ => []
  | .apply _ arguments => arguments.flatMap restCaptureNames
  | .lambda _ body | .multiLambda _ _ body => restCaptureNames body
  | .subst body replacement => restCaptureNames body ++ restCaptureNames replacement
  | .collection _ elements rest => elements.flatMap restCaptureNames ++ rest.toList

def FiniteCaptureNames (assignment : ScopedRuleMatching.Assignment) (names : List String) : Prop :=
  ∀ name ∈ names, ∃ value kind elements,
    lookup assignment name = some value ∧ value.body = .collection kind elements none

def AtomicCaptureNames (assignment : ScopedRuleMatching.Assignment) (names : List String) : Prop :=
  ∀ name ∈ names, ∃ value atom,
    lookup assignment name = some value ∧ value.body = .fvar atom

theorem FiniteCaptureNames.extension {initial final : ScopedRuleMatching.Assignment}
    {names : List String} (before : FiniteCaptureNames initial names)
    (preserved : Extension initial final) : FiniteCaptureNames final names := by
  intro name member
  obtain ⟨value, kind, elements, found, shape⟩ := before name member
  exact ⟨value, kind, elements, preserved name value found, shape⟩

theorem FiniteCaptureNames.append {assignment : ScopedRuleMatching.Assignment}
    {left right : List String} (front : FiniteCaptureNames assignment left)
    (back : FiniteCaptureNames assignment right) : FiniteCaptureNames assignment (left ++ right) := by
  intro name member
  rcases List.mem_append.mp member with member | member
  · exact front name member
  · exact back name member

theorem AtomicCaptureNames.extension {initial final : ScopedRuleMatching.Assignment}
    {names : List String} (before : AtomicCaptureNames initial names)
    (preserved : Extension initial final) : AtomicCaptureNames final names := by
  intro name member
  obtain ⟨value, atom, found, shape⟩ := before name member
  exact ⟨value, atom, preserved name value found, shape⟩

theorem recoverValue_collection_shape {dependencies : List TypeExpr} {ambient depth : Nat}
    {arguments elements : List Pattern} {kind : CollType} {value : ContextualValue}
    (recovered : recoverValue? dependencies ambient depth arguments
      (.collection kind elements none) = some value) :
    ∃ stored, value.body = .collection kind stored none := by
  unfold recoverValue? at recovered
  split at recovered <;> try contradiction
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at recovered
  obtain ⟨indices, _, recovered⟩ := recovered
  split at recovered <;> try contradiction
  split at recovered <;> try contradiction
  cases Option.some.inj recovered
  exact ⟨_, rfl⟩

theorem recoverValue_atom_shape {dependencies : List TypeExpr} {ambient depth : Nat}
    {arguments : List Pattern} {atom : String} {value : ContextualValue}
    (recovered : recoverValue? dependencies ambient depth arguments (.fvar atom) = some value) :
    value.body = .fvar atom := by
  unfold recoverValue? at recovered
  split at recovered <;> try contradiction
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at recovered
  obtain ⟨indices, _, recovered⟩ := recovered
  split at recovered <;> try contradiction
  split at recovered <;> try contradiction
  cases Option.some.inj recovered
  rfl

theorem captureRest_finite {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : ScopedRuleMatching.Assignment}
    {name : String} {kind : CollType} {elements : List Pattern}
    (captured : captureRest? rule spec ambient depth site path initial name kind elements = some final) :
    FiniteCaptureNames final [name] := by
  obtain ⟨_, _, value, _, _, recovered, found, _, _⟩ :=
    GeneralScopedMatch.capture_interpretation (by simpa only [captureRest?] using captured)
  obtain ⟨stored, shape⟩ := recoverValue_collection_shape recovered
  intro queried member
  simp only [List.mem_singleton] at member
  subst queried
  exact ⟨value, kind, stored, found, shape⟩

theorem capture_atom {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : ScopedRuleMatching.Assignment}
    {name atom : String}
    (captured : capture? rule spec ambient depth site path initial name (.fvar atom) = some final) :
    AtomicCaptureNames final [name] := by
  obtain ⟨_, _, value, _, _, recovered, found, _, _⟩ :=
    GeneralScopedMatch.capture_interpretation captured
  intro queried member
  simp only [List.mem_singleton] at member
  subst queried
  exact ⟨value, atom, found, recoverValue_atom_shape recovered⟩

mutual
  theorem matching_finite_restCaptures {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
      {initial final : ScopedRuleMatching.Assignment} {schema target : Pattern}
      (matching : GeneralScopedMatch.Matches rule spec ambient site path depth initial schema target final) :
      FiniteCaptureNames final (restCaptureNames schema) := by
    cases matching with
    | capture _ => intro name member; simp [restCaptureNames] at member
    | bound => intro name member; simp [restCaptureNames] at member
    | constructor arguments =>
        simpa only [restCaptureNames] using matchingArguments_finite_restCaptures arguments
    | binder body => simpa only [restCaptureNames] using matching_finite_restCaptures body
    | binders body => simpa only [restCaptureNames] using matching_finite_restCaptures body
    | substitution body replacement =>
        simpa only [restCaptureNames] using
          ((matching_finite_restCaptures body).extension replacement.extends).append
            (matching_finite_restCaptures replacement)
    | bag _ bag => simpa only [restCaptureNames] using matchingBag_finite_restCaptures bag
    | vector arguments =>
        simpa only [restCaptureNames, Option.toList_none, List.append_nil] using
          matchingArguments_finite_restCaptures arguments
    | vectorRest arguments captured =>
        simpa only [restCaptureNames, Option.toList_some] using
          ((matchingArguments_finite_restCaptures arguments).extension
            (GeneralScopedMatch.capture_extends (by simpa only [captureRest?] using captured))).append
              (captureRest_finite captured)

  theorem matchingArguments_finite_restCaptures {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient depth index : Nat} {site : RulePatternSite} {path : List Nat}
      {initial final : ScopedRuleMatching.Assignment} {schemas targets : List Pattern}
      (matching : GeneralScopedMatch.Arguments rule spec ambient site path depth initial index schemas targets final) :
      FiniteCaptureNames final (schemas.flatMap restCaptureNames) := by
    cases matching with
    | nil => intro name member; simp at member
    | cons head tail =>
        simpa only [List.flatMap_cons] using
          ((matching_finite_restCaptures head).extension tail.extends).append
            (matchingArguments_finite_restCaptures tail)

  theorem matchingBag_finite_restCaptures {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient depth index : Nat} {site : RulePatternSite} {path : List Nat}
      {initial final : ScopedRuleMatching.Assignment} {schemas targets : List Pattern}
      {rest : Option String} {kind : CollType}
      (matching : GeneralScopedMatch.Bag rule spec ambient site path depth initial index schemas rest kind targets final) :
      FiniteCaptureNames final (schemas.flatMap restCaptureNames ++ rest.toList) := by
    cases matching with
    | nil => intro name member; simp at member
    | rest captured => simpa only [List.flatMap_nil, Option.toList_some, List.nil_append] using captureRest_finite captured
    | cons _ _ head tail =>
        simpa only [List.flatMap_cons, List.append_assoc] using
          ((matching_finite_restCaptures head).extension tail.extends).append
            (matchingBag_finite_restCaptures tail)
end

theorem instantiateValue_collection_shape {value : ContextualValue} {ambient depth : Nat}
    {arguments elements : List Pattern} {kind : CollType} {result : Pattern}
    (shape : value.body = .collection kind elements none)
    (read : instantiateValue? value ambient depth arguments = some result) :
    ∃ actualElements, result = .collection kind actualElements none := by
  unfold instantiateValue? at read
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  split at read <;> try contradiction
  dsimp only at read
  split at read <;> try contradiction
  cases Option.some.inj read
  rw [shape]
  exact ⟨_, rfl⟩

theorem FiniteCaptureNames.project {ambient : Nat} {assignment : ScopedRuleMatching.Assignment}
    {names : List String} (finite : FiniteCaptureNames assignment names)
    (values : RootValues ambient assignment) (name : String) (member : name ∈ names) :
    ∃ kind elements, finiteCollection? ambient assignment name = some (kind, elements) := by
  obtain ⟨value, kind, elements, found, shape⟩ := finite name member
  obtain ⟨actual, read⟩ := (values name value found).project 0
  obtain ⟨actualElements, actualShape⟩ := instantiateValue_collection_shape shape read
  refine ⟨kind, actualElements, ?_⟩
  simp only [finiteCollection?, Option.bind_eq_bind, found, read, actualShape, Option.bind_some,
    concreteCollection?]

theorem AtomicCaptureNames.project {ambient : Nat} {assignment : ScopedRuleMatching.Assignment}
    {names : List String} (atomic : AtomicCaptureNames assignment names)
    (values : RootValues ambient assignment) (name : String) (member : name ∈ names) :
    ∃ atom, freshnessName? ambient assignment name = some atom := by
  obtain ⟨value, atom, found, shape⟩ := atomic name member
  obtain ⟨actual, read⟩ := (values name value found).project 0
  have actualShape : actual = .fvar atom := by
    unfold instantiateValue? at read
    split at read <;> try contradiction
    split at read <;> try contradiction
    split at read <;> try contradiction
    split at read <;> try contradiction
    dsimp only at read
    split at read <;> try contradiction
    cases Option.some.inj read
    simp only [shape, ContextSubstitution.substitute]
  exact ⟨atom, by simp only [freshnessName?, found, read, actualShape]⟩

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
