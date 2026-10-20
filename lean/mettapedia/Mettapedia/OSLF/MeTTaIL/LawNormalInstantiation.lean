import Mettapedia.OSLF.MeTTaIL.LawNormalMatching

/-!
# Instantiation respects the collection laws

Law moves commute with context substitution and keep local scope, so instantiating a right side
with captures related by law moves gives results related by law moves
(`instantiateWith?_lawSame`), for every binder operation that respects them. Ordinary binder
elimination does (`instantiateBVar_lawSame`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags

open Syntax CollectionLaws RuleBinding

variable {laws : List Laws}

/-- Equality under the declared collection laws. -/
abbrev LawSame (laws : List Laws) (left right : Pattern) : Prop := Relation.EqvGen (LawStep laws) left right

/-- **Context substitution maps a law move to a law move.** -/
theorem LawStep.substitute {left right : Pattern} (step : LawStep laws left right) :
    ∀ assignment : ContextSubstitution.Assignment,
      LawStep laws (ContextSubstitution.substitute assignment left) (ContextSubstitution.substitute assignment right) := by
  induction step with
  | permute unordered permutation =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    exact .permute unordered (permutation.map _)
  | members same =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    exact .members (members_map same _)
  | flatten found =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_append,
      List.map_cons]
    exact .flatten found
  | unit found unit =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_append,
      List.map_cons, List.map_nil]
    exact .unit found unit
  | apply _ ih =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_append,
      List.map_cons]
    exact .apply (ih assignment)
  | lambda _ ih => intro assignment; simp only [ContextSubstitution.substitute]; exact .lambda (ih _)
  | multiLambda _ ih => intro assignment; simp only [ContextSubstitution.substitute]; exact .multiLambda (ih _)
  | substBody _ ih => intro assignment; simp only [ContextSubstitution.substitute]; exact .substBody (ih _)
  | substReplacement _ ih => intro assignment; simp only [ContextSubstitution.substitute]; exact .substReplacement (ih _)
  | element _ ih =>
    intro assignment
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, List.map_append,
      List.map_cons]
    exact .element (ih assignment)

private theorem wellScopedList_all (depth : Nat) :
    ∀ items : List Pattern, Pattern.isWellScopedListAt depth items = items.all (Pattern.isWellScopedAt depth)
  | [] => rfl
  | item :: rest => by simp [Pattern.isWellScopedListAt, wellScopedList_all depth rest]

/-- **A law move keeps local scope.** -/
theorem LawStep.wellScoped {left right : Pattern} (step : LawStep laws left right) :
    ∀ depth, left.isWellScopedAt depth = right.isWellScopedAt depth := by
  induction step with
  | permute _ permutation =>
    intro depth
    simp only [Pattern.isWellScopedAt, wellScopedList_all]
    exact Bool.eq_iff_iff.mpr (by simp only [List.all_eq_true]; exact ⟨fun h x m => h x (permutation.symm.subset m),
      fun h x m => h x (permutation.subset m)⟩)
  | members same =>
    intro depth
    simp only [Pattern.isWellScopedAt, wellScopedList_all]
    exact Bool.eq_iff_iff.mpr (by simp only [List.all_eq_true]; exact ⟨fun h x m => h x ((same x).mpr m),
      fun h x m => h x ((same x).mp m)⟩)
  | flatten _ =>
    intro depth
    simp only [Pattern.isWellScopedAt, wellScopedList_all, List.all_append, List.all_cons, Bool.and_assoc]
  | unit _ _ =>
    intro depth
    simp only [Pattern.isWellScopedAt, wellScopedList_all, List.all_append, List.all_cons, List.all_nil,
      Bool.true_and]
  | apply _ ih =>
    intro depth
    simp only [Pattern.isWellScopedAt, wellScopedList_all, List.all_append, List.all_cons, ih depth]
  | lambda _ ih => intro depth; simp only [Pattern.isWellScopedAt, ih]
  | multiLambda _ ih => intro depth; simp only [Pattern.isWellScopedAt, ih]
  | substBody _ ih => intro depth; simp only [Pattern.isWellScopedAt, ih]
  | substReplacement _ ih => intro depth; simp only [Pattern.isWellScopedAt, ih]
  | element _ ih =>
    intro depth
    simp only [Pattern.isWellScopedAt, wellScopedList_all, List.all_append, List.all_cons, ih depth]

theorem LawSame.wellScoped {left right : Pattern} (same : LawSame laws left right) (depth : Nat) :
    left.isWellScopedAt depth = right.isWellScopedAt depth := by
  induction same with
  | rel _ _ step => exact step.wellScoped depth
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem LawSame.lift {f : Pattern → Pattern} (step : ∀ {a b : Pattern}, LawStep laws a b → LawStep laws (f a) (f b))
    {a b : Pattern} (same : LawSame laws a b) : LawSame laws (f a) (f b) := by
  induction same with
  | rel _ _ inner => exact .rel _ _ (step inner)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem LawSame.substitute {left right : Pattern} (same : LawSame laws left right)
    (assignment : ContextSubstitution.Assignment) :
    LawSame laws (ContextSubstitution.substitute assignment left) (ContextSubstitution.substitute assignment right) :=
  LawSame.lift (fun step => step.substitute assignment) same

/-- Law-equal lists, pointwise, inside a wrapper whose positions admit law moves. -/
theorem lawSame_pointwise (wrap : List Pattern → Pattern)
    (inside : ∀ (before after : List Pattern) {a b : Pattern}, LawStep laws a b →
      LawStep laws (wrap (before ++ a :: after)) (wrap (before ++ b :: after))) :
    ∀ (before : List Pattern) {items items' : List Pattern}, List.Forall₂ (LawSame laws) items items' →
      LawSame laws (wrap (before ++ items)) (wrap (before ++ items'))
  | _, [], [], .nil => .refl _
  | before, item :: rest, item' :: rest', .cons head tail => by
    have first : LawSame laws (wrap (before ++ item :: rest)) (wrap (before ++ item' :: rest)) :=
      LawSame.lift (f := fun x => wrap (before ++ x :: rest)) (fun step => inside before rest step) head
    have later := lawSame_pointwise wrap inside (before ++ [item']) tail
    simp only [List.append_assoc, List.singleton_append] at later
    exact .trans _ _ _ first later

theorem lawSame_apply_congr (label : String) {items items' : List Pattern}
    (pointwise : List.Forall₂ (LawSame laws) items items') :
    LawSame laws (.apply label items) (.apply label items') := by
  simpa using lawSame_pointwise (fun items => .apply label items) (fun _ _ _ _ step => .apply step) [] pointwise

theorem lawSame_collection_congr (kind : CollType) (rest : Option String) {items items' : List Pattern}
    (pointwise : List.Forall₂ (LawSame laws) items items') :
    LawSame laws (.collection kind items rest) (.collection kind items' rest) := by
  simpa using lawSame_pointwise (fun items => .collection kind items rest) (fun _ _ _ _ step => .element step) [] pointwise

theorem lawSame_lambda_congr (binder : Option String) {body body' : Pattern} (same : LawSame laws body body') :
    LawSame laws (.lambda binder body) (.lambda binder body') :=
  LawSame.lift (fun step => .lambda step) same

theorem lawSame_multiLambda_congr (arity : Nat) (binders : List String) {body body' : Pattern}
    (same : LawSame laws body body') : LawSame laws (.multiLambda arity binders body) (.multiLambda arity binders body') :=
  LawSame.lift (fun step => .multiLambda step) same

theorem lawSame_subst_congr {body body' replacement replacement' : Pattern} (sameBody : LawSame laws body body')
    (sameReplacement : LawSame laws replacement replacement') :
    LawSame laws (.subst body replacement) (.subst body' replacement') :=
  .trans _ _ _ (LawSame.lift (f := fun x => .subst x replacement) (fun step => .substBody step) sameBody)
    (LawSame.lift (f := fun x => .subst body' x) (fun step => .substReplacement step) sameReplacement)

/-- Lifting indices maps a law move to a law move. -/
theorem LawStep.liftBVars {left right : Pattern} (step : LawStep laws left right) :
    ∀ cutoff shift, LawStep laws (Substitution.liftBVars cutoff shift left) (Substitution.liftBVars cutoff shift right) := by
  induction step with
  | permute unordered permutation =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map]
    exact .permute unordered (permutation.map _)
  | members same =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map]
    exact .members (members_map same _)
  | flatten found =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, List.map_append, List.map_cons]
    exact .flatten found
  | unit found unit =>
    intro cutoff shift
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, List.map_append, List.map_cons,
      List.map_nil]
    exact .unit found unit
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

/-- **Substituting law-equal values gives law-equal results.** -/
theorem lawSame_substitute_assignment : ∀ (pattern : Pattern) {first second : ContextSubstitution.Assignment},
    (∀ index, LawSame laws (first index) (second index)) →
    LawSame laws (ContextSubstitution.substitute first pattern) (ContextSubstitution.substitute second pattern)
  | .bvar index, _, _, pointwise => by simp only [ContextSubstitution.substitute]; exact pointwise index
  | .fvar _, _, _, _ => by simp only [ContextSubstitution.substitute]; exact .refl _
  | .apply label arguments, first, second, pointwise => by
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    apply lawSame_apply_congr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro item member
    have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
    exact lawSame_substitute_assignment item pointwise
  | .lambda binder body, first, second, pointwise => by
    simp only [ContextSubstitution.substitute]
    apply lawSame_lambda_congr
    apply lawSame_substitute_assignment body
    intro index
    unfold ContextSubstitution.lift
    split
    · exact .refl _
    · exact LawSame.lift (fun step => step.liftBVars 0 1) (pointwise _)
  | .multiLambda arity binders body, first, second, pointwise => by
    simp only [ContextSubstitution.substitute]
    apply lawSame_multiLambda_congr
    apply lawSame_substitute_assignment body
    intro index
    unfold ContextSubstitution.lift
    split
    · exact .refl _
    · exact LawSame.lift (fun step => step.liftBVars 0 arity) (pointwise _)
  | .subst body replacement, first, second, pointwise => by
    simp only [ContextSubstitution.substitute]
    apply lawSame_subst_congr
    · apply lawSame_substitute_assignment body
      intro index
      unfold ContextSubstitution.lift
      split
      · exact .refl _
      · exact LawSame.lift (fun step => step.liftBVars 0 1) (pointwise _)
    · exact lawSame_substitute_assignment replacement pointwise
  | .collection kind elements rest, first, second, pointwise => by
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    apply lawSame_collection_congr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro item member
    have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
    exact lawSame_substitute_assignment item pointwise
termination_by pattern => sizeOf pattern

/-- **Ordinary binder elimination respects the collection laws.** -/
theorem instantiateBVar_lawSame {replacement replacement' body body' : Pattern}
    (sameReplacement : LawSame laws replacement replacement') (sameBody : LawSame laws body body') :
    LawSame laws (Substitution.instantiateBVar replacement body) (Substitution.instantiateBVar replacement' body') := by
  rw [← ContextSubstitution.substitute_single_eq_instantiateBVar, ← ContextSubstitution.substitute_single_eq_instantiateBVar]
  refine .trans _ _ _ (sameBody.substitute _) (lawSame_substitute_assignment body' ?_)
  intro index
  cases index with
  | zero => exact sameReplacement
  | succ => exact .refl _

/-! ## Instantiating law-equal captures -/

/-- Values with the same context and law-equal bodies. -/
def ValueLawSame (laws : List Laws) (left right : ContextualValue) : Prop :=
  left.dependencies = right.dependencies ∧ left.ambient = right.ambient ∧ LawSame laws left.body right.body

/-- Assignments binding the same names, in order, to law-equal values. -/
def AssignLawSame (laws : List Laws) (left right : ScopedRuleMatching.Assignment) : Prop :=
  List.Forall₂ (fun first second => first.1 = second.1 ∧ ValueLawSame laws first.2 second.2) left right

theorem lookup_lawSame {left right : ScopedRuleMatching.Assignment} (same : AssignLawSame laws left right) (name : String) :
    (ScopedRuleMatching.lookup left name = none ∧ ScopedRuleMatching.lookup right name = none) ∨
      ∃ first second, ScopedRuleMatching.lookup left name = some first ∧
        ScopedRuleMatching.lookup right name = some second ∧ ValueLawSame laws first second := by
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

/-- **Instantiating law-equal values.** -/
theorem instantiateValue?_lawSame {value other : ContextualValue} (same : ValueLawSame laws value other)
    (ambient depth : Nat) (arguments : List Pattern) (result : Pattern)
    (found : instantiateValue? value ambient depth arguments = some result) :
    ∃ otherResult, instantiateValue? other ambient depth arguments = some otherResult ∧ LawSame laws result otherResult := by
  obtain ⟨sameDeps, sameAmbient, sameBody⟩ := same
  obtain ⟨ambientOk, lengthOk, bodyScoped, argumentsScoped, substituted, resultScoped⟩ :=
    (instantiateValue?_eq_some_iff _ _ _ _ _).mp found
  have imageSame : LawSame laws result
      (ContextSubstitution.substitute (occurrenceAssignment other.dependencies.length depth arguments) other.body) := by
    rw [← substituted, ← sameDeps]
    exact sameBody.substitute _
  refine ⟨_, (instantiateValue?_eq_some_iff _ _ _ _ _).mpr ⟨sameAmbient ▸ ambientOk, sameDeps ▸ lengthOk, ?_,
    argumentsScoped, rfl, ?_⟩, imageSame⟩
  · rw [← sameDeps, ← sameBody.wellScoped]; exact bodyScoped
  · rw [← imageSame.wellScoped]; exact resultScoped

/-- The root shape of a collection: its kind and rest. -/
def collectionShape : Pattern → Option (CollType × Option String)
  | .collection kind _ rest => some (kind, rest)
  | _ => none

theorem LawStep.collectionShape {left right : Pattern} (step : LawStep laws left right) :
    collectionShape left = collectionShape right := by
  cases step <;> rfl

theorem LawSame.collectionShape {left right : Pattern} (same : LawSame laws left right) :
    CanonicalBags.collectionShape left = CanonicalBags.collectionShape right := by
  induction same with
  | rel _ _ step => exact step.collectionShape
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem lawSame_collection {kind : CollType} {elements : List Pattern} {rest : Option String} {other : Pattern}
    (same : LawSame laws (.collection kind elements rest) other) : ∃ elements', other = .collection kind elements' rest := by
  have shape := same.collectionShape
  cases other <;> simp_all [collectionShape]

/-- Prefixing every collection's elements. -/
def prependElements (front : List Pattern) : Pattern → Pattern
  | .collection kind elements rest => .collection kind (front ++ elements) rest
  | other => other

theorem LawStep.prependElements (front : List Pattern) {left right : Pattern} (step : LawStep laws left right) :
    LawStep laws (CanonicalBags.prependElements front left) (CanonicalBags.prependElements front right) := by
  cases step with
  | permute unordered permutation => exact .permute unordered (permutation.append_left front)
  | members same => exact .members fun a => by simp only [List.mem_append]; exact or_congr Iff.rfl (same a)
  | flatten found => simpa [CanonicalBags.prependElements] using LawStep.flatten (laws := laws) (before := front ++ _) found
  | unit found unit => simpa [CanonicalBags.prependElements] using LawStep.unit (laws := laws) (before := front ++ _) found unit
  | apply inner => exact .apply inner
  | lambda inner => exact .lambda inner
  | multiLambda inner => exact .multiLambda inner
  | substBody inner => exact .substBody inner
  | substReplacement inner => exact .substReplacement inner
  | element inner => simpa [CanonicalBags.prependElements] using LawStep.element (before := front ++ _) inner

/-- **Splicing law-equal residuals after law-equal elements.** -/
theorem lawSame_splice (kind : CollType) {explicit explicit' residual residual' : List Pattern}
    (pointwise : List.Forall₂ (LawSame laws) explicit explicit')
    (residualSame : LawSame laws (.collection kind residual none) (.collection kind residual' none)) :
    LawSame laws (.collection kind (explicit ++ residual) none) (.collection kind (explicit' ++ residual') none) := by
  have prefixed := LawSame.lift (f := prependElements explicit) (fun step => step.prependElements explicit) residualSame
  simp only [prependElements] at prefixed
  refine .trans _ _ _ prefixed (lawSame_collection_congr kind none ?_)
  exact List.rel_append pointwise (List.forall₂_same.mpr fun _ _ => .refl _)

mutual
/-- **Instantiating a right side with law-equal captures** gives law-equal results, for every
binder operation that respects the collection laws. -/
theorem instantiateWith?_lawSame (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (operation : Pattern → Pattern → Pattern)
    (respects : ∀ {a a' b b' : Pattern}, LawSame laws a a' → LawSame laws b b' →
      LawSame laws (operation a b) (operation a' b')) :
    ∀ (pattern : Pattern) (site : RulePatternSite) (path : List Nat) (depth : Nat)
      (left right : ScopedRuleMatching.Assignment) (result : Pattern), AssignLawSame laws left right →
      ScopedRuleMatching.instantiateWith? operation rule spec ambient site path depth left pattern = some result →
      ∃ otherResult, ScopedRuleMatching.instantiateWith? operation rule spec ambient site path depth right pattern =
        some otherResult ∧ LawSame laws result otherResult
  | .fvar name, site, path, depth, left, right, result, same, found => by
    rw [ScopedRuleMatching.instantiateWith?] at found ⊢
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at found ⊢
    obtain ⟨value, valueFound, arguments, argumentsFound, instantiated⟩ := found
    rcases lookup_lawSame same name with ⟨leftNone, _⟩ | ⟨first, second, leftSome, rightSome, valueSame⟩
    · rw [leftNone] at valueFound; cases valueFound
    · rw [leftSome, Option.some.injEq] at valueFound
      subst valueFound
      obtain ⟨otherResult, otherFound, resultSame⟩ :=
        instantiateValue?_lawSame valueSame ambient depth arguments result instantiated
      exact ⟨otherResult, ⟨second, rightSome, arguments, argumentsFound, otherFound⟩, resultSame⟩
  | .bvar index, site, path, depth, left, right, result, same, found => by
    rw [ScopedRuleMatching.instantiateWith?] at found ⊢
    exact ⟨result, found, .refl _⟩
  | .apply constructor arguments, site, path, depth, left, right, result, same, found => by
    rw [ScopedRuleMatching.instantiateWith?] at found ⊢
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
    obtain ⟨results, resultsFound, rfl⟩ := found
    obtain ⟨otherResults, otherFound, pointwise⟩ := instantiateArgsWith?_lawSame rule spec ambient operation respects
      arguments site path depth left right 0 results same resultsFound
    exact ⟨_, ⟨otherResults, otherFound, rfl⟩, lawSame_apply_congr _ pointwise⟩
  | .lambda binder body, site, path, depth, left, right, result, same, found => by
    rw [ScopedRuleMatching.instantiateWith?] at found ⊢
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
    obtain ⟨inner, innerFound, rfl⟩ := found
    obtain ⟨otherInner, otherFound, innerSame⟩ := instantiateWith?_lawSame rule spec ambient operation respects
      body site (path ++ [0]) (depth + 1) left right inner same innerFound
    exact ⟨_, ⟨otherInner, otherFound, rfl⟩, lawSame_lambda_congr _ innerSame⟩
  | .multiLambda arity binders body, site, path, depth, left, right, result, same, found => by
    rw [ScopedRuleMatching.instantiateWith?] at found ⊢
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
    obtain ⟨inner, innerFound, rfl⟩ := found
    obtain ⟨otherInner, otherFound, innerSame⟩ := instantiateWith?_lawSame rule spec ambient operation respects
      body site (path ++ [0]) (depth + arity) left right inner same innerFound
    exact ⟨_, ⟨otherInner, otherFound, rfl⟩, lawSame_multiLambda_congr _ _ innerSame⟩
  | .subst body replacement, site, path, depth, left, right, result, same, found => by
    rw [ScopedRuleMatching.instantiateWith?] at found ⊢
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
    obtain ⟨body', bodyFound, replacement', replacementFound, rfl⟩ := found
    obtain ⟨otherBody, otherBodyFound, bodySame⟩ := instantiateWith?_lawSame rule spec ambient operation respects
      body site (path ++ [0]) (depth + 1) left right body' same bodyFound
    obtain ⟨otherReplacement, otherReplacementFound, replacementSame⟩ := instantiateWith?_lawSame rule spec ambient
      operation respects replacement site (path ++ [1]) depth left right replacement' same replacementFound
    exact ⟨_, ⟨otherBody, otherBodyFound, otherReplacement, otherReplacementFound, rfl⟩,
      respects replacementSame bodySame⟩
  | .collection kind elements rest, site, path, depth, left, right, result, same, found => by
    rw [ScopedRuleMatching.instantiateWith?] at found ⊢
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at found ⊢
    obtain ⟨explicit, explicitFound, finish⟩ := found
    obtain ⟨otherExplicit, otherExplicitFound, pointwise⟩ := instantiateArgsWith?_lawSame rule spec ambient operation
      respects elements site path depth left right 0 explicit same explicitFound
    cases rest with
    | none =>
      simp only [Option.some.injEq] at finish
      subst finish
      exact ⟨_, ⟨otherExplicit, otherExplicitFound, rfl⟩, lawSame_collection_congr _ _ pointwise⟩
    | some name =>
      simp only [Option.bind_eq_some_iff] at finish
      obtain ⟨value, valueFound, arguments, argumentsFound, produced, instantiated, finish⟩ := finish
      rcases lookup_lawSame same name with ⟨leftNone, _⟩ | ⟨first, second, leftSome, rightSome, valueSame⟩
      · rw [leftNone] at valueFound; cases valueFound
      rw [leftSome, Option.some.injEq] at valueFound
      subst valueFound
      obtain ⟨otherProduced, otherInstantiated, producedSame⟩ :=
        instantiateValue?_lawSame valueSame ambient depth arguments produced instantiated
      cases produced with
      | collection actualKind residual residualRest =>
        cases residualRest with
        | some _ => simp at finish
        | none =>
          obtain ⟨otherResidual, rfl⟩ := lawSame_collection producedSame
          simp only at finish
          split at finish
          · rename_i sameKind
            simp only [Option.some.injEq] at finish
            subst finish
            have kindEq : actualKind = kind := by simpa using sameKind
            subst kindEq
            refine ⟨_, ⟨otherExplicit, otherExplicitFound, ?_⟩, lawSame_splice actualKind pointwise producedSame⟩
            simp only [Option.bind_eq_some_iff]
            exact ⟨second, rightSome, arguments, argumentsFound, by simp [otherInstantiated]⟩
          · cases finish
      | _ => simp at finish
termination_by pattern => sizeOf pattern

theorem instantiateArgsWith?_lawSame (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (operation : Pattern → Pattern → Pattern)
    (respects : ∀ {a a' b b' : Pattern}, LawSame laws a a' → LawSame laws b b' →
      LawSame laws (operation a b) (operation a' b')) :
    ∀ (patterns : List Pattern) (site : RulePatternSite) (path : List Nat) (depth : Nat)
      (left right : ScopedRuleMatching.Assignment) (index : Nat) (results : List Pattern), AssignLawSame laws left right →
      ScopedRuleMatching.instantiateArgsWith? operation rule spec ambient site path depth left index patterns =
        some results →
      ∃ otherResults, ScopedRuleMatching.instantiateArgsWith? operation rule spec ambient site path depth right index
        patterns = some otherResults ∧ List.Forall₂ (LawSame laws) results otherResults
  | [], site, path, depth, left, right, index, results, same, found => by
    rw [ScopedRuleMatching.instantiateArgsWith?] at found ⊢
    simp only [Option.some.injEq] at found
    subst found
    exact ⟨[], rfl, .nil⟩
  | pattern :: patterns, site, path, depth, left, right, index, results, same, found => by
    rw [ScopedRuleMatching.instantiateArgsWith?] at found ⊢
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at found ⊢
    obtain ⟨head, headFound, tail, tailFound, rfl⟩ := found
    obtain ⟨otherHead, otherHeadFound, headSame⟩ := instantiateWith?_lawSame rule spec ambient operation respects
      pattern site (path ++ [index]) depth left right head same headFound
    obtain ⟨otherTail, otherTailFound, tailSame⟩ := instantiateArgsWith?_lawSame rule spec ambient operation respects
      patterns site path depth left right (index + 1) tail same tailFound
    exact ⟨_, ⟨otherHead, otherHeadFound, otherTail, otherTailFound, rfl⟩, .cons headSame tailSame⟩
termination_by patterns => sizeOf patterns
end

end Mettapedia.OSLF.MeTTaIL.CanonicalBags
