import Mettapedia.OSLF.NativeTypes.Modal.NativeEventTyping
import Mettapedia.OSLF.NativeTypes.Generation.NativeSignature

/-!
# Independently typed rely and matched parameter readouts

The ordered parameter lists come from each generated authored schema. Every
left-hand-side variable is retained by scoped matching and subsequent premise
execution. Its sort and dependency context are recovered from the authored
declaration, rather than inferred from a returned endpoint.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeEventParameters

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.RedexPosition
open Rules NativeEventFibre

def Present (assignment : Assignment) (names : List String) : Prop :=
  ∀ name ∈ names, ∃ value, lookup assignment name = some value

theorem Present.extend {initial final : Assignment} {names : List String}
    (present : Present initial names) (extension : GeneralScopedMatch.Extends initial final) :
    Present final names := by
  intro name member
  obtain ⟨value, found⟩ := present name member
  exact ⟨value, extension name value found⟩

private theorem capture_present {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
    {initial final : Assignment} {name : String} {target : Pattern}
    (captured : capture? rule spec ambient depth site path initial name target = some final) :
    Present final [name] := by
  obtain ⟨_, _, value, _, _, _, found, _, _⟩ := GeneralScopedMatch.capture_interpretation captured
  intro actual member
  have same : actual = name := List.mem_singleton.mp member
  subst actual
  exact ⟨value, found⟩

mutual
theorem matching_present {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth : Nat} {initial final : Assignment}
    {pattern target : Pattern}
    (matched : GeneralScopedMatch.Matches rule spec ambient site path depth initial pattern target final) :
    Present final (fvarNames pattern) := by
  cases matched with
  | capture captured => exact capture_present captured
  | bound => intro name impossible; cases impossible
  | constructor arguments => exact arguments_present arguments
  | binder body => simpa only [fvarNames] using matching_present body
  | binders body => simpa only [fvarNames] using matching_present body
  | substitution body replacement =>
      intro name member
      rcases List.mem_append.mp member with left | right
      · exact (matching_present body).extend replacement.extends name left
      · exact matching_present replacement name right
  | bag _ bag => exact bag_present bag
  | vector arguments =>
      simpa only [fvarNames, Option.toList_none, List.append_nil] using arguments_present arguments
  | vectorRest arguments captured =>
      intro name member
      rcases List.mem_append.mp member with left | right
      · exact (arguments_present arguments).extend (GeneralScopedMatch.capture_extends captured) name left
      · exact capture_present captured name right
termination_by sizeOf pattern

theorem arguments_present {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
    {patterns targets : List Pattern}
    (matched : GeneralScopedMatch.Arguments rule spec ambient site path depth initial index patterns targets final) :
    Present final (fvarNamesList patterns) := by
  cases matched with
  | nil => intro name impossible; cases impossible
  | cons head tail =>
      intro name member
      rcases List.mem_append.mp member with left | right
      · exact (matching_present head).extend tail.extends name left
      · exact arguments_present tail name right
termination_by sizeOf patterns

theorem bag_present {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {depth index : Nat} {initial final : Assignment}
    {patterns targets : List Pattern} {rest : Option String} {kind : CollType}
    (matched : GeneralScopedMatch.Bag rule spec ambient site path depth initial index patterns rest kind targets final) :
    Present final (fvarNamesList patterns ++ rest.toList) := by
  cases matched with
  | nil => intro name impossible; cases impossible
  | rest captured => exact capture_present captured
  | cons _ _ head tail =>
      intro name member
      rcases List.mem_append.mp member with left | right
      · rcases List.mem_append.mp left with inHead | inTail
        · exact (matching_present head).extend tail.extends name inHead
        · exact bag_present tail name (List.mem_append_left _ inTail)
      · exact bag_present tail name (List.mem_append_right _ right)
termination_by sizeOf patterns
end

theorem firing_present {environment : GeneralPremise.Environment} {bound : List TypeExpr}
    {carrier : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List GeneralPremise.Event}
    (firing : GeneralPremise.RootFiring environment bound carrier source index trace captured completed history target) :
    ∃ rule, environment.language.rewrites[index]? = some rule ∧
      Present completed (fvarNames rule.left) := by
  cases firing with
  | fire declared _ _ _ matching _ premises _ _ =>
      exact ⟨_, declared, (matching_present matching.matching).extend premises.extension⟩

private theorem child_names {host child : Pattern} (member : child ∈ children host) :
    ∀ name ∈ fvarNames child, name ∈ fvarNames host := by
  cases host with
  | bvar _ => cases member
  | fvar _ => cases member
  | apply _ arguments =>
      intro name present
      change name ∈ fvarNamesList arguments
      rw [fvarNamesList_eq]
      exact List.mem_flatMap.mpr ⟨child, member, by simpa only [fvarNames_eq] using present⟩
  | lambda _ body =>
      have same : child = body := List.mem_singleton.mp member
      subst child
      exact fun _ present => present
  | multiLambda _ _ body =>
      have same : child = body := List.mem_singleton.mp member
      subst child
      exact fun _ present => present
  | subst body replacement =>
      intro name present
      rcases (show child = body ∨ child = replacement from by simpa [children] using member) with same | same
      · subst child; exact List.mem_append_left _ present
      · subst child; exact List.mem_append_right _ present
  | collection _ elements rest =>
      intro name present
      apply List.mem_append_left
      rw [fvarNamesList_eq]
      exact List.mem_flatMap.mpr ⟨child, member, by simpa only [fvarNames_eq] using present⟩

theorem focus_names_subset (host : Pattern) (position : Position) :
    ∀ name ∈ focusFreeVars host position, name ∈ fvarNames host := by
  induction position generalizing host with
  | nil => exact fun _ present => present
  | cons childIndex rest ih =>
      cases selected : childAt host childIndex with
      | none => simp only [focusFreeVars, subtermAt, selected, Option.bind_none]
                intro name impossible; cases impossible
      | some child =>
          intro name present
          have inFocus : name ∈ focusFreeVars child rest := by
            simpa only [focusFreeVars, subtermAt, selected, Option.bind_some] using present
          exact child_names (List.mem_of_getElem? selected) name (ih child name inFocus)

theorem context_names_subset (host : Pattern) (position : Position) :
    ∀ name ∈ contextFreeVars host position, name ∈ fvarNames host := by
  induction position generalizing host with
  | nil => intro name impossible; cases impossible
  | cons childIndex rest ih =>
      intro name present
      simp only [contextFreeVars, List.mem_append] at present
      rcases present with (owned | sibling) | deeper
      · cases host <;> simp_all [localVars, fvarNames]
      · obtain ⟨entry, member, present⟩ := List.mem_flatMap.mp sibling
        split at present
        · cases present
        · have childMember : entry.1 ∈ children host := by
            have mapped : entry.1 ∈ (children host).zipIdx.map Prod.fst :=
              List.mem_map.mpr ⟨entry, member, rfl⟩
            simpa only [List.zipIdx_map_fst] using mapped
          exact child_names childMember name present
      · cases selected : childAt host childIndex with
        | none => rw [selected] at deeper; cases deeper
        | some child =>
            rw [selected] at deeper
            exact child_names (List.mem_of_getElem? selected) name (ih child name deeper)

variable {plan : Plan} {schema : Schema plan}

theorem Event.left_present (event : Event schema) :
    Present event.assignment (fvarNames schema.declaration.rule.left) := by
  obtain ⟨rule, declared, present⟩ := firing_present (event.root_firing schema)
  rw [event.ordinal] at declared
  have authored := GeneralPlanEnvironment.selected_rule plan
    (List.mk_mem_zipIdx_iff_getElem?.mp schema.declared)
  have same := Option.some.inj (declared.symm.trans authored)
  subst rule
  simpa only [event.completed] using present

theorem Event.rely_present (event : Event schema) : Present event.assignment schema.relyNames := by
  intro name member
  apply Event.left_present event name
  apply context_names_subset
  exact (List.mem_filter.mp (List.mem_eraseDups.mp member)).1

theorem Event.matched_present (event : Event schema) : Present event.assignment schema.matchedNames := by
  intro name member
  apply Event.left_present event name
  apply focus_names_subset _ schema.position
  unfold Schema.matchedNames at member
  unfold focusFreeVars
  cases selected : subtermAt schema.declaration.rule.left schema.position <;>
    simpa only [selected, Option.map_none, Option.map_some, Option.getD_none, Option.getD_some] using member

/-- Slot metadata is obtained from authored scoped and sorted declarations. -/
structure Slot (schema : Schema plan) where
  name : String
  dependencies : List TypeExpr
  expected : TypeExpr
  declared : dependencies? schema.declaration.binding.spec name = some dependencies
  sorted : schema.declaration.rule.typeContext.lookup name = some expected

def slot? (schema : Schema plan) (name : String) : Option (Slot schema) :=
  match declared : dependencies? schema.declaration.binding.spec name,
      sorted : schema.declaration.rule.typeContext.lookup name with
  | some dependencies, some expected => some ⟨name, dependencies, expected, declared, sorted⟩
  | _, _ => none

/-- Each value is in its precise local dependency and ambient context. -/
abbrev Value (slot : Slot schema) :=
  {value : ContextualValue | value.dependencies = slot.dependencies ∧
    value.ambient = schema.bound.length ∧
    HasType plan.snapshot.language plan.snapshot.free (slot.dependencies ++ schema.bound)
      value.body slot.expected ∧ isObjectPattern value.body = true}

theorem slot?_name {name : String} {slot : Slot schema} (decoded : slot? schema name = some slot) :
    slot.name = name := by
  unfold slot? at decoded
  split at decoded
  · cases Option.some.inj decoded
    rfl
  · cases decoded

theorem slot?_complete (event : Event schema) (name : String)
    (present : ∃ value, lookup event.assignment name = some value) :
    ∃ slot, slot? schema name = some slot := by
  obtain ⟨value, found⟩ := present
  obtain ⟨dependencies, expected, declared, sorted, _, _, _⟩ :=
    (NativeEventTyping.Event.assignment_typed event).1 name value
      (ConditionalEquationExecution.lookup_assignment_member _ _ _ found)
  change dependencies? schema.declaration.binding.spec name = some dependencies at declared
  change schema.declaration.rule.typeContext.lookup name = some expected at sorted
  exact ⟨⟨name, dependencies, expected, declared, sorted⟩,
    by
      unfold slot?
      split
      · rename_i actualDependencies actualExpected actualDeclared actualSorted
        have sameDependencies := Option.some.inj (actualDeclared.symm.trans declared)
        have sameExpected := Option.some.inj (actualSorted.symm.trans sorted)
        subst actualDependencies
        subst actualExpected
        rfl
      · simp_all⟩

def readSlot (event : Event schema) (slot : Slot schema) : Option (Value slot) :=
  match found : lookup event.assignment slot.name with
  | none => none
  | some value => some ⟨value, by
      have member := ConditionalEquationExecution.lookup_assignment_member _ _ _ found
      obtain ⟨dependencies, expected, declared, sorted, metadata, ambient, typed⟩ :=
        (NativeEventTyping.Event.assignment_typed event).1 slot.name value member
      have sameDependencies := Option.some.inj (declared.symm.trans slot.declared)
      have sameExpected := Option.some.inj (sorted.symm.trans slot.sorted)
      rw [sameDependencies, sameExpected] at typed
      change HasType (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
        (slot.dependencies ++ schema.bound) value.body slot.expected at typed
      exact ⟨metadata.trans sameDependencies, ambient,
        GeneralLanguageTyping.type_transport (GeneralPlanEnvironment.grammar plan) typed,
        (NativeEventTyping.Event.assignment_typed event).2 slot.name value member⟩⟩

theorem readSlot_exact (event : Event schema) (slot : Slot schema) :
    (readSlot event slot).isSome = (lookup event.assignment slot.name).isSome := by
  unfold readSlot
  split <;> simp_all

theorem readSlot_value (event : Event schema) (slot : Slot schema) (value : Value slot)
    (read : readSlot event slot = some value) :
    lookup event.assignment slot.name = some value.val := by
  unfold readSlot at read
  split at read
  · cases read
  · rename_i actual found
    cases Option.some.inj read
    exact found

def slots? (schema : Schema plan) (names : List String) : Option (List (Slot schema)) :=
  Generation.NativeSignature.decodeList (slot? schema) names

theorem slots?_names {names : List String} {slots : List (Slot schema)}
    (decoded : slots? schema names = some slots) : slots.map Slot.name = names := by
  have each := Generation.NativeSignature.decodeList_sound decoded
  clear decoded
  induction each with
  | nil => rfl
  | cons first _ ih =>
      simp only [List.map_cons, slot?_name first, ih]

theorem slots?_complete (event : Event schema) (names : List String)
    (present : Present event.assignment names) : ∃ slots, slots? schema names = some slots :=
  Generation.NativeSignature.decodeList_exists (fun name member => slot?_complete event name (present name member))

/-- The tuple keeps every slot and its value in the generated list order. -/
structure ParameterTuple (schema : Schema plan) where
  slots : List (Slot schema)
  values : ∀ index : Fin slots.length, Value slots[index]

def parameters (event : Event schema) (names : List String)
    (present : Present event.assignment names) : ParameterTuple schema where
  slots := (slots? schema names).get (by
    obtain ⟨slots, decoded⟩ := slots?_complete event names present
    simp only [decoded, Option.isSome_some])
  values index := by
    let slots := (slots? schema names).get (by
      obtain ⟨slots, decoded⟩ := slots?_complete event names present
      simp only [decoded, Option.isSome_some])
    have original : slots.map Slot.name = names := slots?_names (Option.some_get _).symm
    have member : slots[index].name ∈ names := by
      have mapped : slots[index].name ∈ slots.map Slot.name :=
        List.mem_map.mpr ⟨slots[index], List.getElem_mem index.isLt, rfl⟩
      exact Eq.mp (congrArg (fun observed : List String => slots[index].name ∈ observed) original) mapped
    have available : (readSlot event slots[index]).isSome := by
      obtain ⟨value, found⟩ := present slots[index].name member
      exact (readSlot_exact event slots[index]).trans (congrArg Option.isSome found)
    exact (readSlot event slots[index]).get available

theorem parameters_names (event : Event schema) (names : List String)
    (present : Present event.assignment names) :
    (parameters event names present).slots.map Slot.name = names :=
  slots?_names (Option.some_get _).symm

theorem parameters_values (event : Event schema) (names : List String)
    (present : Present event.assignment names) (index : Fin (parameters event names present).slots.length) :
    lookup event.assignment (parameters event names present).slots[index].name =
      some ((parameters event names present).values index).val :=
  readSlot_value event _ _ (Option.some_get _).symm

def relyParameters (event : Event schema) : ParameterTuple schema :=
  parameters event schema.relyNames (Event.rely_present event)

def matchedParameters (event : Event schema) : ParameterTuple schema :=
  parameters event schema.matchedNames (Event.matched_present event)

theorem rely_parameters_exact (event : Event schema) :
    (relyParameters event).slots.map Slot.name = schema.relyNames ∧
      ∀ index : Fin (relyParameters event).slots.length,
        lookup event.assignment (relyParameters event).slots[index].name =
          some ((relyParameters event).values index).val :=
  ⟨parameters_names _ _ _, parameters_values _ _ _⟩

theorem matched_parameters_exact (event : Event schema) :
    (matchedParameters event).slots.map Slot.name = schema.matchedNames ∧
      ∀ index : Fin (matchedParameters event).slots.length,
        lookup event.assignment (matchedParameters event).slots[index].name =
          some ((matchedParameters event).values index).val :=
  ⟨parameters_names _ _ _, parameters_values _ _ _⟩

end Mettapedia.OSLF.NativeTypes.Modal.NativeEventParameters
