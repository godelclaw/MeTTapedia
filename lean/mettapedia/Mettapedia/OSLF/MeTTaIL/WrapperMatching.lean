import Mettapedia.OSLF.MeTTaIL.WrapperNormal
import Mettapedia.OSLF.MeTTaIL.QuoteDropMatching

/-!
# Matching at wrapper normal forms

A pattern matches the wrapper normal form of every term it matches when it never matches a wrapper
(`wrapperFree`): each collection pattern of a flattening kind has at least two explicit elements, so the
collection it matches keeps its shape. The captures at the normal form are the normal forms of the
original captures, except that a collection rest keeps its own shape and has its elements in normal
form (`wrapperInner`): a rest of one element is still a collection of one element. A name that is a rest
is never an ordinary metavariable of the same pattern, so a repeated metavariable stays repeated
(`matches_wrapper`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Wrappers

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch CollectionLaws CanonicalBags

variable {laws : List Laws}

/-! ## Maps of captured bodies -/

/-- A map of bodies that commutes with renamings and keeps scope. -/
structure BodyMap (f : Pattern → Pattern) : Prop where
  commutes : ∀ (pattern : Pattern) {assignment : ContextSubstitution.Assignment}, QuoteDrop.Renaming assignment →
    f (ContextSubstitution.substitute assignment pattern) = ContextSubstitution.substitute assignment (f pattern)
  keepsScope : ∀ (pattern : Pattern) (depth : Nat), (f pattern).isWellScopedAt depth = pattern.isWellScopedAt depth

/-- A captured value with its body mapped. -/
def mapValue (f : Pattern → Pattern) (value : ContextualValue) : ContextualValue :=
  { value with body := f value.body }

theorem instantiateValue?_map {f : Pattern → Pattern} (map : BodyMap f) {value : ContextualValue}
    {ambient depth : Nat} {arguments : List Pattern}
    (bvars : ∀ argument ∈ arguments, ∃ index, argument = .bvar index) :
    instantiateValue? (mapValue f value) ambient depth arguments =
      (instantiateValue? value ambient depth arguments).map f := by
  unfold instantiateValue?
  simp only [mapValue, map.keepsScope]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · have commuted : ContextSubstitution.substitute (occurrenceAssignment value.dependencies.length depth arguments)
                (f value.body) =
              f (ContextSubstitution.substitute (occurrenceAssignment value.dependencies.length depth arguments)
                value.body) :=
            (map.commutes _ (QuoteDrop.occurrenceAssignment_renaming bvars)).symm
          simp only [commuted, map.keepsScope]
          split <;> rfl

/-- **A recovered capture's image is recovered from the image of the subject.** -/
theorem recoverValue?_map {f : Pattern → Pattern} (map : BodyMap f) {dependencies : List TypeExpr}
    {ambient depth : Nat} {arguments : List Pattern} {target : Pattern} {value : ContextualValue}
    (found : recoverValue? dependencies ambient depth arguments target = some value) :
    recoverValue? dependencies ambient depth arguments (f target) = some (mapValue f value) := by
  unfold recoverValue? at found ⊢
  rw [map.keepsScope]
  split at found
  · cases found
  · rename_i inScope
    rw [if_neg inScope]
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at found ⊢
    obtain ⟨indices, spine, rest⟩ := found
    refine ⟨indices, spine, ?_⟩
    split at rest
    · cases rest
    · rename_i lengths
      rw [if_neg lengths]
      have body : ContextSubstitution.substitute (recoveryAssignment depth dependencies.length ambient indices)
          (f target) =
          f (ContextSubstitution.substitute (recoveryAssignment depth dependencies.length ambient indices) target) :=
        (map.commutes target (QuoteDrop.recoveryAssignment_renaming _ _ _ _)).symm
      split at rest
      · rename_i forward
        cases rest
        have shape : (⟨dependencies, ambient,
            ContextSubstitution.substitute (recoveryAssignment depth dependencies.length ambient indices)
              (f target)⟩ : ContextualValue) =
            mapValue f ⟨dependencies, ambient,
              ContextSubstitution.substitute (recoveryAssignment depth dependencies.length ambient indices) target⟩ := by
          simp only [mapValue, body]
        rw [shape, instantiateValue?_map map (QuoteDrop.variableSpine?_bvars spine)]
        have forward' := beq_iff_eq.mp forward
        rw [forward']
        simp
      · cases rest

/-! ## The wrapper maps -/

theorem bodyMap_wrapperNormal : BodyMap (wrapperNormal laws) where
  commutes pattern _ renames := wrapperNormal_substitute_renaming pattern renames
  keepsScope := wrapperNormal_wellScoped

variable (laws) in
/-- The wrapper normal form below the root of a collection: a collection keeps its shape and has its
elements in normal form; any other term is in normal form. -/
def wrapperInner : Pattern → Pattern
  | .collection kind elements rest => .collection kind (elements.map (wrapperNormal laws)) rest
  | other => wrapperNormal laws other

theorem wrapperInner_collection (kind : CollType) (elements : List Pattern) (rest : Option String) :
    wrapperInner laws (.collection kind elements rest) = .collection kind (elements.map (wrapperNormal laws)) rest := rfl

theorem bodyMap_wrapperInner : BodyMap (wrapperInner laws) where
  commutes pattern assignment renames := by
    cases pattern with
    | collection kind elements rest =>
      simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, wrapperInner_collection,
        List.map_map]
      congr 1
      exact List.map_congr_left fun element _ => wrapperNormal_substitute_renaming element renames
    | bvar index =>
      obtain ⟨other, found⟩ := renames index
      simp only [ContextSubstitution.substitute, found, wrapperInner, wrapperNormal_bvar]
    | fvar name => simp only [ContextSubstitution.substitute, wrapperInner, wrapperNormal_fvar]
    | apply label arguments =>
      have := wrapperNormal_substitute_renaming (laws := laws) (.apply label arguments) renames
      simpa only [wrapperInner, ContextSubstitution.substitute] using this
    | lambda binder body =>
      have := wrapperNormal_substitute_renaming (laws := laws) (.lambda binder body) renames
      simpa only [wrapperInner, ContextSubstitution.substitute] using this
    | multiLambda arity binders body =>
      have := wrapperNormal_substitute_renaming (laws := laws) (.multiLambda arity binders body) renames
      simpa only [wrapperInner, ContextSubstitution.substitute] using this
    | subst body replacement =>
      have := wrapperNormal_substitute_renaming (laws := laws) (.subst body replacement) renames
      simpa only [wrapperInner, ContextSubstitution.substitute] using this
  keepsScope pattern depth := by
    cases pattern with
    | collection kind elements rest =>
      simp only [wrapperInner_collection, Pattern.isWellScopedAt]
      exact wellScopedList_map depth _ elements fun element _ => wrapperNormal_wellScoped element depth
    | _ => exact wrapperNormal_wellScoped _ depth

theorem wrapperInner_forward (pattern : Pattern) : WrapperForward laws pattern (wrapperInner laws pattern) := by
  cases pattern with
  | collection kind elements rest =>
    exact wrapperForward_collection kind rest (forall₂_map_self fun element _ => to_wrapperNormal element)
  | _ => exact to_wrapperNormal _

/-! ## Assignments -/

variable (laws) in
/-- The map of a captured body: the rest of a collection keeps its shape, every other capture is in
wrapper normal form. -/
def captureMap (rests : List String) (name : String) : Pattern → Pattern :=
  if name ∈ rests then wrapperInner laws else wrapperNormal laws

theorem bodyMap_captureMap (rests : List String) (name : String) : BodyMap (captureMap laws rests name) := by
  unfold captureMap
  split
  · exact bodyMap_wrapperInner
  · exact bodyMap_wrapperNormal

theorem captureMap_forward (rests : List String) (name : String) (pattern : Pattern) :
    WrapperForward laws pattern (captureMap laws rests name pattern) := by
  unfold captureMap
  split
  · exact wrapperInner_forward pattern
  · exact to_wrapperNormal pattern

variable (laws) in
/-- Every captured body mapped by its name's role. -/
def wrapperAssignment (rests : List String) (assignment : ScopedRuleMatching.Assignment) :
    ScopedRuleMatching.Assignment :=
  assignment.map fun entry => (entry.1, mapValue (captureMap laws rests entry.1) entry.2)

theorem lookup_wrapperAssignment (rests : List String) (assignment : ScopedRuleMatching.Assignment) (name : String) :
    lookup (wrapperAssignment laws rests assignment) name =
      (lookup assignment name).map (mapValue (captureMap laws rests name)) := by
  induction assignment with
  | nil => rfl
  | cons entry rest ih =>
    unfold lookup at ih ⊢
    simp only [wrapperAssignment, List.map_cons] at ih ⊢
    by_cases same : entry.1 = name
    · rw [List.find?_cons_of_pos (by simpa using same), List.find?_cons_of_pos (by simpa using same)]
      simp only [Option.map_some, same]
    · rw [List.find?_cons_of_neg (by simpa using same), List.find?_cons_of_neg (by simpa using same)]; exact ih

theorem assign_wrapper (rests : List String) {assignment final : ScopedRuleMatching.Assignment} {name : String}
    {value : ContextualValue} (assigned : assign assignment name value = some final) :
    assign (wrapperAssignment laws rests assignment) name (mapValue (captureMap laws rests name) value) =
      some (wrapperAssignment laws rests final) := by
  unfold assign at assigned ⊢
  rw [lookup_wrapperAssignment]
  cases found : lookup assignment name with
  | none =>
    rw [found] at assigned
    cases assigned
    rfl
  | some prior =>
    rw [found] at assigned
    simp only [Option.map_some]
    by_cases same : prior = value
    · subst same
      simp only [beq_self_eq_true, if_true, Option.some.injEq] at assigned ⊢
      rw [assigned]
    · simp [same] at assigned

theorem capture?_wrapper (rests : List String) {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat} {assignment final : ScopedRuleMatching.Assignment}
    {name : String} {target : Pattern}
    (captured : capture? rule spec ambient depth site path assignment name target = some final) :
    capture? rule spec ambient depth site path (wrapperAssignment laws rests assignment) name
        (captureMap laws rests name target) = some (wrapperAssignment laws rests final) := by
  unfold capture? at captured ⊢
  simp only [bind, Option.bind_eq_some_iff] at captured ⊢
  obtain ⟨dependencies, declared, arguments, found, value, recovered, assigned⟩ := captured
  exact ⟨dependencies, declared, arguments, found, mapValue (captureMap laws rests name) value,
    recoverValue?_map (bodyMap_captureMap rests name) recovered, assign_wrapper rests assigned⟩

/-- An ordinary capture: its body is in wrapper normal form. -/
theorem capture?_ordinary {rests : List String} {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat} {assignment final : ScopedRuleMatching.Assignment}
    {name : String} {target : Pattern} (ordinary : name ∉ rests)
    (captured : capture? rule spec ambient depth site path assignment name target = some final) :
    capture? rule spec ambient depth site path (wrapperAssignment laws rests assignment) name
        (wrapperNormal laws target) = some (wrapperAssignment laws rests final) := by
  have := capture?_wrapper (laws := laws) rests captured
  rwa [captureMap, if_neg ordinary] at this

/-- A rest capture: the rest keeps its shape, with its elements in wrapper normal form. -/
theorem captureRest?_wrapper {rests : List String} {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat} {assignment final : ScopedRuleMatching.Assignment}
    {name : String} {kind : CollType} {elements : List Pattern} (isRest : name ∈ rests)
    (captured : captureRest? rule spec ambient depth site path assignment name kind elements = some final) :
    captureRest? rule spec ambient depth site path (wrapperAssignment laws rests assignment) name kind
        (elements.map (wrapperNormal laws)) = some (wrapperAssignment laws rests final) := by
  unfold captureRest? at captured ⊢
  have := capture?_wrapper (laws := laws) rests captured
  rwa [captureMap, if_pos isRest, wrapperInner_collection] at this

/-! ## Patterns that never match a wrapper -/

variable (laws) in
mutual
  /-- A pattern that never matches a wrapper: every collection pattern of a flattening kind has at least
  two explicit elements; every metavariable is ordinary and every collection rest is a rest. -/
  def wrapperFree (rests : List String) : Pattern → Bool
    | .bvar _ => true
    | .fvar name => !(rests.contains name)
    | .apply _ arguments => wrapperFreeList rests arguments
    | .lambda _ body => wrapperFree rests body
    | .multiLambda _ _ body => wrapperFree rests body
    | .subst body replacement => wrapperFree rests body && wrapperFree rests replacement
    | .collection kind elements rest =>
        ((lawFor laws kind).isNone || decide (2 ≤ elements.length)) &&
          (match rest with | some name => rests.contains name | none => true) && wrapperFreeList rests elements

  /-- Every pattern of a list never matches a wrapper. -/
  def wrapperFreeList (rests : List String) : List Pattern → Bool
    | [] => true
    | pattern :: patterns => wrapperFree rests pattern && wrapperFreeList rests patterns
end

theorem wrapperFreeList_iff {rests : List String} :
    ∀ items : List Pattern, wrapperFreeList laws rests items = true ↔ ∀ item ∈ items, wrapperFree laws rests item = true
  | [] => by simp [wrapperFreeList]
  | item :: rest => by simp [wrapperFreeList, wrapperFreeList_iff rest]

theorem wrapperFree_fvar {rests : List String} {name : String} (free : wrapperFree laws rests (.fvar name) = true) :
    name ∉ rests := by
  simpa [wrapperFree] using free

theorem wrapperFree_apply {rests : List String} {label : String} {arguments : List Pattern}
    (free : wrapperFree laws rests (.apply label arguments) = true) :
    ∀ argument ∈ arguments, wrapperFree laws rests argument = true := by
  rw [wrapperFree] at free
  exact (wrapperFreeList_iff arguments).mp free

theorem wrapperFree_collection {rests : List String} {kind : CollType} {elements : List Pattern}
    {rest : Option String} (free : wrapperFree laws rests (.collection kind elements rest) = true) :
    (lawFor laws kind = none ∨ 2 ≤ elements.length) ∧ (∀ name, rest = some name → name ∈ rests) ∧
      ∀ element ∈ elements, wrapperFree laws rests element = true := by
  simp only [wrapperFree, Bool.and_eq_true, Bool.or_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at free
  obtain ⟨⟨long, named⟩, each⟩ := free
  refine ⟨long, ?_, (wrapperFreeList_iff elements).mp each⟩
  intro name same
  subst same
  simpa using named

theorem bag_length_le {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
    {path : List Nat} {depth : Nat} {final : ScopedRuleMatching.Assignment} {rest : Option String} {kind : CollType} :
    ∀ (schemas : List Pattern) {targets : List Pattern} {index : Nat} {initial : ScopedRuleMatching.Assignment},
      Bag rule spec ambient site path depth initial index schemas rest kind targets final →
      schemas.length ≤ targets.length
  | [], _, _, _, _ => Nat.zero_le _
  | _ :: schemas, _, _, _, matched => by
    cases matched with
    | cons selected within _ tail =>
      have shorter := bag_length_le schemas tail
      rw [List.length_eraseIdx_of_lt within] at shorter
      simp only [List.length_cons]
      omega

theorem two_le_of_take {count : Nat} {targets : List Pattern} (lengths : count = (targets.take count).length)
    (two : 2 ≤ count) : (none : Option String).isSome ∨ 2 ≤ targets.length := by
  rw [List.length_take] at lengths
  exact .inr (by omega)

mutual
  /-- **Every match of a pattern that never matches a wrapper has a match at the wrapper normal form**,
  with mapped captures. -/
  theorem matches_wrapper {rests : List String} {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth : Nat}
      {initial final : ScopedRuleMatching.Assignment} {schema target : Pattern}
      (free : wrapperFree laws rests schema = true)
      (matched : Matches rule spec ambient site path depth initial schema target final) :
      Matches rule spec ambient site path depth (wrapperAssignment laws rests initial) schema (wrapperNormal laws target)
        (wrapperAssignment laws rests final) := by
    cases matched with
    | capture captured => exact .capture (capture?_ordinary (wrapperFree_fvar free) captured)
    | bound => rw [wrapperNormal_bvar]; exact .bound
    | constructor arguments =>
      rw [wrapperNormal_apply]
      exact .constructor (arguments_wrapper (wrapperFree_apply free) arguments)
    | binder body =>
      rw [wrapperNormal_lambda]
      exact .binder (matches_wrapper (by rw [wrapperFree] at free; exact free) body)
    | binders body =>
      rw [wrapperNormal_multiLambda]
      exact .binders (matches_wrapper (by rw [wrapperFree] at free; exact free) body)
    | substitution body replacement =>
      rw [wrapperFree, Bool.and_eq_true] at free
      rw [wrapperNormal_subst]
      exact .substitution (matches_wrapper free.1 body) (matches_wrapper free.2 replacement)
    | bag notVector bag =>
      obtain ⟨long, named, each⟩ := wrapperFree_collection free
      have shape : lawFor laws _ = none ∨ (none : Option String).isSome ∨ 2 ≤ _ :=
        long.imp_right fun two => .inr (le_trans two (bag_length_le _ bag))
      rw [wrapperNormal_collection_long shape]
      exact .bag notVector (bag_wrapper each named bag)
    | vector arguments =>
      obtain ⟨long, _, each⟩ := wrapperFree_collection free
      have shape : lawFor laws _ = none ∨ (none : Option String).isSome ∨ 2 ≤ _ :=
        long.imp_right fun two => .inr (le_of_le_of_eq two (arguments_length _ arguments))
      rw [wrapperNormal_collection_long shape]
      exact .vector (arguments_wrapper each arguments)
    | vectorRest arguments captured =>
      obtain ⟨long, named, each⟩ := wrapperFree_collection free
      have shape := long.imp_right fun two => two_le_of_take (arguments_length _ arguments) two
      rw [wrapperNormal_collection_long shape]
      have front := arguments_wrapper each arguments
      have rest := captureRest?_wrapper (laws := laws) (named _ rfl) captured
      rw [List.map_take] at front
      rw [List.map_drop] at rest
      exact .vectorRest front rest
  termination_by sizeOf schema

  theorem arguments_wrapper {rests : List String} {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth index : Nat}
      {initial final : ScopedRuleMatching.Assignment} {schemas targets : List Pattern}
      (free : ∀ schema ∈ schemas, wrapperFree laws rests schema = true)
      (matched : Arguments rule spec ambient site path depth initial index schemas targets final) :
      Arguments rule spec ambient site path depth (wrapperAssignment laws rests initial) index schemas
        (targets.map (wrapperNormal laws)) (wrapperAssignment laws rests final) := by
    cases matched with
    | nil => exact .nil
    | cons head tail =>
      exact .cons (matches_wrapper (free _ (by simp)) head)
        (arguments_wrapper (fun schema member => free schema (by simp [member])) tail)
  termination_by sizeOf schemas

  theorem bag_wrapper {rests : List String} {rule : RewriteRule} {spec : RuleBindingSpec}
      {ambient : Nat} {site : RulePatternSite} {path : List Nat} {depth index : Nat}
      {initial final : ScopedRuleMatching.Assignment} {schemas : List Pattern} {rest : Option String}
      {kind : CollType} {targets : List Pattern}
      (free : ∀ schema ∈ schemas, wrapperFree laws rests schema = true)
      (named : ∀ name, rest = some name → name ∈ rests)
      (matched : Bag rule spec ambient site path depth initial index schemas rest kind targets final) :
      Bag rule spec ambient site path depth (wrapperAssignment laws rests initial) index schemas rest kind
        (targets.map (wrapperNormal laws)) (wrapperAssignment laws rests final) := by
    cases matched with
    | nil => exact .nil
    | rest captured => exact .rest (captureRest?_wrapper (named _ rfl) captured)
    | cons selected within head tail =>
      have headNormal := matches_wrapper (free _ (by simp)) head
      have tailNormal := bag_wrapper (fun schema member => free schema (by simp [member])) named tail
      rw [← QuoteDrop.map_eraseIdx'] at tailNormal
      refine .cons selected (by simpa using within) ?_ tailNormal
      simpa using headNormal
  termination_by sizeOf schemas
end

end Mettapedia.OSLF.MeTTaIL.Wrappers
