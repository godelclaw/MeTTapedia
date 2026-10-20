import Mettapedia.OSLF.MeTTaIL.CanonicalSites

/-!
# Matching at law-normal forms

The normal form of the declared collection laws flattens nested collections of a flattening
kind and removes declared units (`CollectionLaws.normalize`). It inspects no index, so it
commutes with every renaming of indices (`normalize_rename`); a capture recovered from a
normalized subject is the normal form of the capture recovered from the original
(`recoverValue?_normalize`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags

open Syntax CollectionLaws RuleBinding ScopedRuleMatching GeneralScopedMatch
open ContextSubstitution (substitute substituteList lift)

theorem splice_rename (law : Laws) (rename : Nat → Nat) (pattern : Pattern) :
    splice law (substitute (indexRenaming rename) pattern) = (splice law pattern).map (substitute (indexRenaming rename)) := by
  cases pattern with
  | collection kind elements rest =>
    cases rest with
    | none =>
      simp only [substitute, ContextSubstitution.substituteList_eq_map, splice]
      split <;> simp [substitute, ContextSubstitution.substituteList_eq_map]
    | some name => simp [substitute, ContextSubstitution.substituteList_eq_map, splice]
  | apply label arguments =>
    cases arguments with
    | nil =>
      simp only [substitute, ContextSubstitution.substituteList_eq_map, List.map_nil, splice]
      split <;> simp [substitute]
    | cons => simp [substitute, ContextSubstitution.substituteList_eq_map, splice]
  | bvar index => simp [substitute, splice]
  | fvar name => simp [substitute, splice]
  | lambda binder body => simp [substitute, splice]
  | multiLambda arity binders body => simp [substitute, splice]
  | subst body replacement => simp [substitute, splice]

/-- **The law-normal form commutes with every renaming of indices.** -/
theorem normalize_rename (laws : List Laws) : ∀ (rename : Nat → Nat) (pattern : Pattern),
    normalize laws (substitute (indexRenaming rename) pattern) = substitute (indexRenaming rename) (normalize laws pattern)
  | _, .bvar index => by simp only [substitute]; rw [normalize, normalize]; rfl
  | _, .fvar name => by simp only [substitute]; rw [normalize]; rfl
  | rename, .apply label arguments => by
    simp only [substitute, ContextSubstitution.substituteList_eq_map]
    rw [normalize, normalize]
    simp only [List.map_map, substitute, ContextSubstitution.substituteList_eq_map]
    congr 1
    apply List.map_congr_left
    intro item member
    have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
    exact normalize_rename laws rename item
  | rename, .lambda binder body => by
    simp only [substitute, lift_renaming]
    rw [normalize, normalize, normalize_rename laws _ body]
    simp only [substitute, lift_renaming]
  | rename, .multiLambda arity binders body => by
    simp only [substitute, lift_renaming]
    rw [normalize, normalize, normalize_rename laws _ body]
    simp only [substitute, lift_renaming]
  | rename, .subst body replacement => by
    simp only [substitute, lift_renaming]
    rw [normalize, normalize, normalize_rename laws _ body, normalize_rename laws _ replacement]
    simp only [substitute, lift_renaming]
  | rename, .collection kind elements rest => by
    simp only [substitute, ContextSubstitution.substituteList_eq_map]
    have each : elements.map (normalize laws ∘ substitute (indexRenaming rename)) =
        elements.map (substitute (indexRenaming rename) ∘ normalize laws) := by
      apply List.map_congr_left
      intro item member
      have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
        have := List.sizeOf_lt_of_mem member; simp only [Pattern.collection.sizeOf_spec]; omega
      exact normalize_rename laws rename item
    rw [normalize, normalize]
    simp only [List.map_map, each]
    split
    · simp only [substitute, ContextSubstitution.substituteList_eq_map, List.map_flatMap, ← List.map_map,
        List.flatMap_map, splice_rename]
    · simp only [substitute, ContextSubstitution.substituteList_eq_map, ← List.map_map]
termination_by _ pattern => sizeOf pattern

theorem isWellScopedListAt_iff (depth : Nat) (items : List Pattern) :
    Pattern.isWellScopedListAt depth items = true ↔ ∀ item ∈ items, item.isWellScopedAt depth = true :=
  Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff depth items

theorem splice_scoped (law : Laws) {depth : Nat} {pattern : Pattern} (inScope : pattern.isWellScopedAt depth = true) :
    ∀ item ∈ splice law pattern, item.isWellScopedAt depth = true := by
  intro item member
  cases pattern with
  | collection kind elements rest =>
    cases rest with
    | none =>
      simp only [splice] at member
      split at member
      · exact (isWellScopedListAt_iff _ _).mp (by simpa [Pattern.isWellScopedAt] using inScope) item member
      · simp only [List.mem_singleton] at member; subst member; exact inScope
    | some name => simp only [splice, List.mem_singleton] at member; subst member; exact inScope
  | apply label arguments =>
    cases arguments with
    | nil =>
      simp only [splice] at member
      split at member
      · simp at member
      · simp only [List.mem_singleton] at member; subst member; exact inScope
    | cons => simp only [splice, List.mem_singleton] at member; subst member; exact inScope
  | _ => simp only [splice, List.mem_singleton] at member; subst member; exact inScope

/-- The law-normal form keeps local scope. -/
theorem normalize_scoped (laws : List Laws) : ∀ {depth : Nat} (pattern : Pattern),
    pattern.isWellScopedAt depth = true → (normalize laws pattern).isWellScopedAt depth = true
  | _, .bvar _, inScope => by rw [normalize]; exact inScope
  | _, .fvar _, inScope => by rw [normalize]; exact inScope
  | depth, .apply label arguments, inScope => by
    rw [normalize]
    simp only [Pattern.isWellScopedAt, isWellScopedListAt_iff, List.mem_map] at inScope ⊢
    rintro _ ⟨item, member, rfl⟩
    have : sizeOf item < sizeOf (Pattern.apply label arguments) := by
      have := List.sizeOf_lt_of_mem member; simp only [Pattern.apply.sizeOf_spec]; omega
    exact normalize_scoped laws item (inScope item member)
  | _, .lambda _ body, inScope => by
    rw [normalize]; simp only [Pattern.isWellScopedAt] at inScope ⊢; exact normalize_scoped laws body inScope
  | _, .multiLambda _ _ body, inScope => by
    rw [normalize]; simp only [Pattern.isWellScopedAt] at inScope ⊢; exact normalize_scoped laws body inScope
  | _, .subst body replacement, inScope => by
    rw [normalize]
    simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at inScope ⊢
    exact ⟨normalize_scoped laws body inScope.1, normalize_scoped laws replacement inScope.2⟩
  | depth, .collection kind elements rest, inScope => by
    have each : ∀ item ∈ elements.map (normalize laws), item.isWellScopedAt depth = true := by
      rintro _ member
      obtain ⟨item, inElements, rfl⟩ := List.mem_map.mp member
      have : sizeOf item < sizeOf (Pattern.collection kind elements rest) := by
        have := List.sizeOf_lt_of_mem inElements; simp only [Pattern.collection.sizeOf_spec]; omega
      exact normalize_scoped laws item ((isWellScopedListAt_iff _ _).mp (by simpa [Pattern.isWellScopedAt] using inScope)
        item inElements)
    rw [normalize]
    split
    · simp only [Pattern.isWellScopedAt, isWellScopedListAt_iff, List.mem_flatMap]
      rintro item ⟨piece, inPieces, inSplice⟩
      exact splice_scoped _ (each piece inPieces) item inSplice
    · simp only [Pattern.isWellScopedAt, isWellScopedListAt_iff]
      exact each
termination_by _ pattern => sizeOf pattern

private theorem mapM_bvars {f : Pattern → Option Nat} (onlyVariables : ∀ argument index, f argument = some index → argument = .bvar index) :
    ∀ {arguments : List Pattern} {found : List Nat}, arguments.mapM f = some found → arguments = found.map Pattern.bvar
  | [], found, mapped => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at mapped; subst mapped; rfl
  | argument :: arguments, found, mapped => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at mapped
    obtain ⟨head, image, tail, mappedTail, rfl⟩ := mapped
    rw [onlyVariables _ _ image, mapM_bvars onlyVariables mappedTail]
    rfl

/-- A variable spine's arguments are its local variables. -/
theorem variableSpine?_arguments {depth : Nat} {arguments : List Pattern} {indices : List Nat}
    (spine : variableSpine? depth arguments = some indices) : arguments = indices.map Pattern.bvar := by
  unfold variableSpine? at spine
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at spine
  obtain ⟨found, mapped, rest⟩ := spine
  have arguments_eq := mapM_bvars (fun argument index image => by
    split at image
    · split at image
      · cases image; rfl
      · cases image
    · cases image) mapped
  split at rest
  · cases rest; exact arguments_eq
  · cases rest

/-- With a variable spine, instantiation renames indices. -/
theorem occurrenceAssignment_eq {depth : Nat} {arguments : List Pattern} {indices : List Nat}
    (spine : variableSpine? depth arguments = some indices) (dependencies : Nat) :
    occurrenceAssignment dependencies depth arguments =
      indexRenaming fun index => if index < dependencies then indices.getD index 0 else depth + (index - dependencies) := by
  rw [variableSpine?_arguments spine]
  funext index
  unfold occurrenceAssignment
  by_cases small : index < dependencies
  · simp only [small, if_true, indexRenaming, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases indices[index]? <;> rfl
  · simp only [small, if_false, indexRenaming]

/-- **A capture recovered from a law-normal subject is the normal form of the capture
recovered from the original.** -/
theorem recoverValue?_normalize (laws : List Laws) {dependencies : List TypeExpr} {ambient depth : Nat}
    {arguments : List Pattern} {target : Pattern} {value : ContextualValue}
    (found : recoverValue? dependencies ambient depth arguments target = some value) :
    recoverValue? dependencies ambient depth arguments (normalize laws target) =
      some { value with body := normalize laws value.body } := by
  unfold recoverValue? at found ⊢
  split at found <;> [cases found; skip]
  rename_i targetScoped
  have normalScoped : (normalize laws target).isWellScopedAt (depth + ambient) = true :=
    normalize_scoped laws target (by simpa using targetScoped)
  simp only [normalScoped, Bool.not_true, Bool.false_eq_true, if_false]
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at found ⊢
  obtain ⟨indices, spine, found⟩ := found
  refine ⟨indices, spine, ?_⟩
  split at found <;> [cases found; skip]
  rename_i lengths
  simp only [lengths, Bool.false_eq_true, if_false]
  split at found <;> [skip; cases found]
  rename_i forward
  cases found
  obtain ⟨sameAmbient, lengthOk, bodyScoped, argumentsScoped, roundTrip, _⟩ :=
    (instantiateValue?_eq_some_iff _ _ _ _ _).mp (by simpa using forward)
  have bodyEq : substitute (recoveryAssignment depth dependencies.length ambient indices) (normalize laws target) =
      normalize laws (substitute (recoveryAssignment depth dependencies.length ambient indices) target) := by
    rw [recoveryAssignment_eq, normalize_rename]
  have imageForward : instantiateValue? ⟨dependencies, ambient,
      normalize laws (substitute (recoveryAssignment depth dependencies.length ambient indices) target)⟩
      ambient depth arguments = some (normalize laws target) := by
    apply (instantiateValue?_eq_some_iff _ _ _ _ _).mpr
    refine ⟨sameAmbient, lengthOk, normalize_scoped laws _ bodyScoped, argumentsScoped, ?_, normalScoped⟩
    simp only at roundTrip ⊢
    rw [occurrenceAssignment_eq spine, ← normalize_rename, ← occurrenceAssignment_eq spine, roundTrip]
  rw [bodyEq, imageForward]
  simp

/-! ## Captures under a map of bodies -/

/-- A captured value with its body mapped. -/
def mapValue (f : Pattern → Pattern) (value : ContextualValue) : ContextualValue := { value with body := f value.body }

/-- Every captured body mapped. -/
def mapAssignment (f : Pattern → Pattern) (assignment : ScopedRuleMatching.Assignment) : ScopedRuleMatching.Assignment :=
  assignment.map fun entry => (entry.1, mapValue f entry.2)

theorem lookup_mapAssignment (f : Pattern → Pattern) (assignment : ScopedRuleMatching.Assignment) (name : String) :
    lookup (mapAssignment f assignment) name = (lookup assignment name).map (mapValue f) := by
  induction assignment with
  | nil => rfl
  | cons entry rest ih =>
    unfold lookup at ih ⊢
    simp only [mapAssignment, List.map_cons] at ih ⊢
    by_cases same : entry.1 = name
    · rw [List.find?_cons_of_pos (by simpa using same), List.find?_cons_of_pos (by simpa using same)]; rfl
    · rw [List.find?_cons_of_neg (by simpa using same), List.find?_cons_of_neg (by simpa using same)]; exact ih

theorem assign_map (f : Pattern → Pattern) {assignment final : ScopedRuleMatching.Assignment} {name : String}
    {value : ContextualValue} (assigned : assign assignment name value = some final) :
    assign (mapAssignment f assignment) name (mapValue f value) = some (mapAssignment f final) := by
  unfold assign at assigned ⊢
  rw [lookup_mapAssignment]
  cases found : lookup assignment name with
  | none => rw [found] at assigned; cases assigned; rfl
  | some prior =>
    rw [found] at assigned
    simp only [Option.map_some]
    by_cases same : prior = value
    · subst same
      simp only [beq_self_eq_true, if_true, Option.some.injEq] at assigned ⊢
      rw [assigned]
    · simp [same] at assigned

theorem capture?_normalize (laws : List Laws) {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat} {assignment final : ScopedRuleMatching.Assignment} {name : String}
    {target : Pattern} (captured : capture? rule spec ambient depth site path assignment name target = some final) :
    capture? rule spec ambient depth site path (mapAssignment (normalize laws) assignment) name (normalize laws target) =
      some (mapAssignment (normalize laws) final) := by
  unfold capture? at captured ⊢
  simp only [bind, Option.bind_eq_some_iff] at captured ⊢
  obtain ⟨dependencies, declared, arguments, found, value, recovered, assigned⟩ := captured
  exact ⟨dependencies, declared, arguments, found, mapValue (normalize laws) value,
    recoverValue?_normalize laws recovered, assign_map _ assigned⟩

/-! ## Patterns safe for the collection laws -/

/-- The normalized elements of a collection of one kind. -/
def normalElements (laws : List Laws) (kind : CollType) (elements : List Pattern) : List Pattern :=
  match lawFor laws kind with
  | some law => (elements.map (normalize laws)).flatMap (splice law)
  | none => elements.map (normalize laws)

theorem normalize_collection' (laws : List Laws) (kind : CollType) (elements : List Pattern) (rest : Option String) :
    normalize laws (.collection kind elements rest) = .collection kind (normalElements laws kind elements) rest := by
  rw [normalize]; unfold normalElements lawFor
  cases laws.find? (fun law => decide (law.kind = kind)) <;> rfl

theorem captureRest?_normalize (laws : List Laws) {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat} {assignment final : ScopedRuleMatching.Assignment} {name : String}
    {kind : CollType} {elements : List Pattern}
    (captured : captureRest? rule spec ambient depth site path assignment name kind elements = some final) :
    captureRest? rule spec ambient depth site path (mapAssignment (normalize laws) assignment) name kind
      (normalElements laws kind elements) = some (mapAssignment (normalize laws) final) := by
  unfold captureRest? at captured ⊢
  have := capture?_normalize laws captured
  rwa [normalize_collection'] at this

/-- A collection element pattern that never matches a nested collection of the flattening kind or
its declared unit: neither a bare metavariable, nor a collection of that kind, nor the unit. -/
def ElementSafe (law : Laws) (pattern : Pattern) : Prop :=
  (∀ name, pattern ≠ .fvar name) ∧ (∀ elements rest, pattern ≠ .collection law.kind elements rest) ∧
    (∀ label, law.unit = some label → pattern ≠ .apply label [])

/-- A schema whose collection patterns of a flattening kind have only safe elements. -/
inductive FlatSafe (laws : List Laws) : Pattern → Prop where
  | fvar (name : String) : FlatSafe laws (.fvar name)
  | bvar (index : Nat) : FlatSafe laws (.bvar index)
  | apply {label : String} {arguments : List Pattern} :
      (∀ argument ∈ arguments, FlatSafe laws argument) → FlatSafe laws (.apply label arguments)
  | lambda {binder : Option String} {body : Pattern} : FlatSafe laws body → FlatSafe laws (.lambda binder body)
  | multiLambda {arity : Nat} {binders : List String} {body : Pattern} :
      FlatSafe laws body → FlatSafe laws (.multiLambda arity binders body)
  | subst {body replacement : Pattern} :
      FlatSafe laws body → FlatSafe laws replacement → FlatSafe laws (.subst body replacement)
  | collection {kind : CollType} {elements : List Pattern} {rest : Option String} :
      (∀ element ∈ elements, FlatSafe laws element) →
      (∀ law, lawFor laws kind = some law → ∀ element ∈ elements, ElementSafe law element) →
      FlatSafe laws (.collection kind elements rest)

theorem arguments_length {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
    {path : List Nat} {depth : Nat} {final : ScopedRuleMatching.Assignment} :
    ∀ (schemas : List Pattern) {targets : List Pattern} {index : Nat} {initial : ScopedRuleMatching.Assignment},
      Arguments rule spec ambient site path depth initial index schemas targets final →
      schemas.length = targets.length
  | [], _, _, _, matched => by cases matched; rfl
  | _ :: schemas, _, _, _, matched => by
    cases matched with
    | cons _ tail => simp [arguments_length schemas tail]

/-- A target matched by a safe element pattern is its own splice. -/
theorem splice_of_safe (laws : List Laws) {law : Laws} {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : ScopedRuleMatching.Assignment}
    {schema target : Pattern} (matched : Matches rule spec ambient site path depth initial schema target final)
    (safe : ElementSafe law schema) : splice law (normalize laws target) = [normalize laws target] := by
  obtain ⟨notVariable, notCollection, notUnit⟩ := safe
  cases matched with
  | capture => exact absurd rfl (notVariable _)
  | bound => rw [normalize]; rfl
  | constructor arguments =>
    rename_i label patterns targets
    rw [normalize]
    cases targets with
    | nil =>
      have : patterns = [] := List.eq_nil_of_length_eq_zero (by simpa using arguments_length _ arguments)
      subst this
      simp only [List.map_nil, splice]
      split
      · rename_i unit; exact absurd rfl (notUnit label unit)
      · rfl
    | cons => rfl
  | binder => rw [normalize]; rfl
  | binders => rw [normalize]; rfl
  | substitution => rw [normalize]; rfl
  | bag =>
    rename_i kind patterns rest targets _ _
    rw [normalize_collection']
    simp only [splice]
    split
    · rename_i same; exact absurd (by rw [same]) (notCollection patterns rest)
    · rfl
  | vector =>
    rw [normalize_collection']
    simp only [splice]
    split
    · rename_i same; exact absurd (by rw [same]) (notCollection _ none)
    · rfl
  | vectorRest =>
    rw [normalize_collection']
    simp only [splice]
    split
    · rename_i same; exact absurd (by rw [same]) (notCollection _ (some _))
    · rfl

theorem select_middle {α : Type} (front back : List α) (item : α) :
    ∃ (position : Nat) (inside : position < (front ++ item :: back).length),
      (front ++ item :: back)[position] = item ∧ (front ++ item :: back).eraseIdx position = front ++ back :=
  ⟨front.length, by simp, by simp, by rw [List.eraseIdx_append_of_length_le (le_refl _)]; simp⟩

/-- Selecting a target that is its own splice selects its normal form among the normalized
elements, with the normalized residual. -/
theorem normalElements_select (laws : List Laws) (kind : CollType) (targets : List Pattern) (selected : Nat)
    (within : selected < targets.length)
    (fixed : ∀ law, lawFor laws kind = some law → splice law (normalize laws targets[selected]) = [normalize laws targets[selected]]) :
    ∃ (position : Nat) (inside : position < (normalElements laws kind targets).length),
      (normalElements laws kind targets)[position] = normalize laws targets[selected] ∧
      (normalElements laws kind targets).eraseIdx position = normalElements laws kind (targets.eraseIdx selected) := by
  have split : targets = targets.take selected ++ targets[selected] :: targets.drop (selected + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have erased : targets.eraseIdx selected = targets.take selected ++ targets.drop (selected + 1) :=
    List.eraseIdx_eq_take_drop_succ _ _
  unfold normalElements
  cases found : lawFor laws kind with
  | some law =>
    have shape : (targets.map (normalize laws)).flatMap (splice law) =
        ((targets.take selected).map (normalize laws)).flatMap (splice law) ++ normalize laws targets[selected] ::
          ((targets.drop (selected + 1)).map (normalize laws)).flatMap (splice law) := by
      conv_lhs => rw [split]
      simp only [List.map_append, List.map_cons, List.flatMap_append, List.flatMap_cons, fixed law found]
      rfl
    dsimp only
    rw [shape, erased]
    obtain ⟨position, inside, atPosition, residual⟩ := select_middle
      (((targets.take selected).map (normalize laws)).flatMap (splice law)) (((targets.drop (selected + 1)).map
        (normalize laws)).flatMap (splice law)) (normalize laws targets[selected])
    exact ⟨position, inside, atPosition, by rw [residual]; simp [List.map_append, List.flatMap_append]⟩
  | none =>
    simp only
    have shape : targets.map (normalize laws) = (targets.take selected).map (normalize laws) ++
        normalize laws targets[selected] :: (targets.drop (selected + 1)).map (normalize laws) := by
      conv_lhs => rw [split]
      rw [List.map_append, List.map_cons]
    rw [shape, erased]
    obtain ⟨position, inside, atPosition, residual⟩ := select_middle ((targets.take selected).map (normalize laws))
      ((targets.drop (selected + 1)).map (normalize laws)) (normalize laws targets[selected])
    exact ⟨position, inside, atPosition, by rw [residual]; simp⟩

theorem normalElements_nil (laws : List Laws) (kind : CollType) : normalElements laws kind [] = [] := by
  unfold normalElements; cases lawFor laws kind <;> rfl

/-- Targets matched by safe element patterns are their own splices. -/
theorem arguments_splice (laws : List Laws) {law : Laws} {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {final : ScopedRuleMatching.Assignment} :
    ∀ {schemas targets : List Pattern} {index : Nat} {initial : ScopedRuleMatching.Assignment},
      Arguments rule spec ambient site path depth initial index schemas targets final →
      (∀ schema ∈ schemas, ElementSafe law schema) →
      ∀ target ∈ targets, splice law (normalize laws target) = [normalize laws target]
  | [], _, _, _, matched, _ => by cases matched; intro _ member; cases member
  | _ :: schemas, _, _, _, matched, safe => by
    cases matched with
    | cons head tail =>
      intro target member
      rcases List.mem_cons.mp member with rfl | inTail
      · exact splice_of_safe laws head (safe _ (.head _))
      · exact arguments_splice laws tail (fun schema inner => safe schema (.tail _ inner)) target inTail

/-- Normalized elements whose prefix consists of their own splices. -/
theorem normalElements_prefix (laws : List Laws) (kind : CollType) (front back : List Pattern)
    (fixed : ∀ law, lawFor laws kind = some law → ∀ target ∈ front, splice law (normalize laws target) = [normalize laws target]) :
    normalElements laws kind (front ++ back) = front.map (normalize laws) ++ normalElements laws kind back := by
  unfold normalElements
  cases found : lawFor laws kind with
  | some law =>
    dsimp only
    rw [List.map_append, List.flatMap_append, flatMap_splice_fixed law _ (by
      intro item member
      obtain ⟨target, inFront, rfl⟩ := List.mem_map.mp member
      exact fixed law found target inFront)]
  | none => dsimp only; rw [List.map_append]

mutual
  /-- **Every match at a subject has a match at its law-normal form**, with normalized captures,
  for every schema safe for the declared laws. -/
  theorem matches_normalize (laws : List Laws) {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : ScopedRuleMatching.Assignment}
      {schema target : Pattern} (safe : FlatSafe laws schema)
      (matched : Matches rule spec ambient site path depth initial schema target final) :
      Matches rule spec ambient site path depth (mapAssignment (normalize laws) initial) schema (normalize laws target)
        (mapAssignment (normalize laws) final) := by
    cases matched with
    | capture captured => exact .capture (capture?_normalize laws captured)
    | bound => rw [normalize]; exact .bound
    | constructor arguments =>
      cases safe with
      | apply each => rw [normalize]; exact .constructor (arguments_normalize laws each arguments)
    | binder body =>
      cases safe with
      | lambda inner => rw [normalize]; exact .binder (matches_normalize laws inner body)
    | binders body =>
      cases safe with
      | multiLambda inner => rw [normalize]; exact .binders (matches_normalize laws inner body)
    | substitution body replacement =>
      cases safe with
      | subst innerBody innerReplacement =>
        rw [normalize]
        exact .substitution (matches_normalize laws innerBody body) (matches_normalize laws innerReplacement replacement)
    | bag notVector bag =>
      cases safe with
      | collection each elements =>
        rw [normalize_collection']
        exact .bag notVector (bag_normalize laws each elements bag)
    | vector arguments =>
      rename_i patterns targets
      cases safe with
      | collection each elements =>
        rw [normalize_collection']
        have fixed : normalElements laws .vec targets = targets.map (normalize laws) := by
          have := normalElements_prefix laws .vec _ [] (fun law found => arguments_splice laws arguments (elements law found))
          rwa [List.append_nil, normalElements_nil, List.append_nil] at this
        rw [fixed]
        exact .vector (arguments_normalize laws each arguments)
    | vectorRest arguments captured =>
      rename_i patterns name targets middle
      cases safe with
      | collection each elements =>
        rw [normalize_collection']
        have decomposed := normalElements_prefix laws .vec (targets.take patterns.length) (targets.drop patterns.length)
          (fun law found => arguments_splice laws arguments (elements law found))
        rw [List.take_append_drop] at decomposed
        have lengths : patterns.length ≤ targets.length := by
          have := arguments_length _ arguments
          rw [List.length_take] at this
          omega
        have front : (normalElements laws .vec targets).take patterns.length =
            (targets.take patterns.length).map (normalize laws) := by
          rw [decomposed, List.take_append_of_le_length (by simp; omega)]
          rw [List.take_of_length_le (by simp)]
        have back : (normalElements laws .vec targets).drop patterns.length =
            normalElements laws .vec (targets.drop patterns.length) := by
          rw [decomposed, List.drop_append_of_le_length (by simp; omega)]
          rw [List.drop_of_length_le (by simp), List.nil_append]
        have frontMatched := arguments_normalize laws each arguments
        rw [← front] at frontMatched
        have restCaptured := captureRest?_normalize laws captured
        rw [← back] at restCaptured
        exact .vectorRest frontMatched restCaptured
  termination_by sizeOf schema

  theorem arguments_normalize (laws : List Laws) {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : ScopedRuleMatching.Assignment}
      {schemas targets : List Pattern} (safe : ∀ schema ∈ schemas, FlatSafe laws schema)
      (matched : Arguments rule spec ambient site path depth initial index schemas targets final) :
      Arguments rule spec ambient site path depth (mapAssignment (normalize laws) initial) index schemas
        (targets.map (normalize laws)) (mapAssignment (normalize laws) final) := by
    cases matched with
    | nil => exact .nil
    | cons head tail =>
      exact .cons (matches_normalize laws (safe _ (.head _)) head)
        (arguments_normalize laws (fun schema member => safe schema (.tail _ member)) tail)
  termination_by sizeOf schemas

  theorem bag_normalize (laws : List Laws) {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : ScopedRuleMatching.Assignment}
      {schemas : List Pattern} {rest : Option String} {kind : CollType} {targets : List Pattern}
      (safe : ∀ schema ∈ schemas, FlatSafe laws schema)
      (elementSafe : ∀ law, lawFor laws kind = some law → ∀ schema ∈ schemas, ElementSafe law schema)
      (matched : Bag rule spec ambient site path depth initial index schemas rest kind targets final) :
      Bag rule spec ambient site path depth (mapAssignment (normalize laws) initial) index schemas rest kind
        (normalElements laws kind targets) (mapAssignment (normalize laws) final) := by
    cases matched with
    | nil => rw [normalElements_nil]; exact .nil
    | rest captured => exact .rest (captureRest?_normalize laws captured)
    | cons selected within head tail =>
      obtain ⟨position, inside, atPosition, residual⟩ := normalElements_select laws kind _ selected within
        (fun law found => splice_of_safe laws head (elementSafe law found _ (.head _)))
      have headNormal := matches_normalize laws (safe _ (.head _)) head
      rw [← atPosition] at headNormal
      have tailNormal := bag_normalize laws (fun schema member => safe schema (.tail _ member))
        (fun law found schema member => elementSafe law found schema (.tail _ member)) tail
      rw [← residual] at tailNormal
      exact .cons position inside headNormal tailNormal
  termination_by sizeOf schemas
end

end Mettapedia.OSLF.MeTTaIL.CanonicalBags
