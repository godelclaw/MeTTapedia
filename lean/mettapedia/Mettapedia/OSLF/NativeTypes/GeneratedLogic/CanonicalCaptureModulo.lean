import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureSteps
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSchemaInstantiationObjects

/-!
# Set rules modulo the set laws at every boundary

Under the either reading a language's semantics holds modulo its laws everywhere. A rule may fire at any presentation
of a state, and inside a step every internal boundary reads terms modulo the set laws: a premise steps any
presentation of its child, its target is matched at any presentation of the step's result, and a relation's answers
are matched at any presentations of their values (`RuleReading.modulo`: the equational internal boundary policy with
the equivalence of terms with one canonical form, `canonSetoid`).

A hereditary set language has canonical forms for this reading, with presentations listed under bounds by depth
(`moduloForms`), whatever its rules' premises are: step premises from any schema, relation queries over metavariables
in a relation environment that answers alike requests alike, freshness conditions, and universally quantified
premises.

- **Object terms** (`captures_object`, `applyBindingsScoped_object`): the captures of an object term are object terms,
  and a schema whose collection rests are rests of the rule's left side instantiates to an object term.
- **Every step modulo the set laws is listed** (`modulo_listed`), by induction on the size of its witness. The match
  moves to a listed presentation with canonical captures (`capture_transfer_object`), and each premise moves with it
  (`premise_listed`):
  - a step premise's child keeps its class, so its step is matched first, at a listed presentation of the child (the
    induction), and its target's match moves to a listed presentation of the result;
  - a relation is answered alike at the canonical request and matched at canonical answers;
  - a freshness condition reads the same names;
  - a quantified premise holds at each canonical member as it holds at a member of the same class.
- **Coherence** (`modulo_coherent`, `moduloForms`): the front door's canonical forms for the reading.

A quantified premise whose body steps has one witness per element, and the copies of a member may step differently:
labels that look under a rule's premises can tell the copies apart, rule labels cannot. The forms keep every label when
no quantified premise's body steps (`deep`), and the rule labels otherwise.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchArgsRel MatchBagRel matchPattern_iff_matchRel)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (canon Same arrange arrange_mem canon_idempotent canon_collection canon_apply)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv premiseStepWithEnv builtinRelationTuples matchRelationArgs
  matchRelationArgument)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule matchPatternForRule_eq_syntactic)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (isObjectPatternList_iff)

variable {language : LanguageDef} {sort : String}

/-! ## Object terms -/

theorem object_collection_iff {kind : CollType} {elements : List Pattern} {rest : Option String} :
    IsObject (.collection kind elements rest) ↔ rest = none ∧ ∀ element ∈ elements, IsObject element := by
  simp only [IsObject, isObjectPattern, Bool.and_eq_true, isObjectPatternList_iff, Option.isNone_iff_eq_none]
  rfl

theorem object_apply_iff {label : String} {arguments : List Pattern} :
    IsObject (.apply label arguments) ↔ ∀ argument ∈ arguments, IsObject argument := by
  simp only [IsObject, isObjectPattern, isObjectPatternList_iff]
  rfl

theorem object_canon_iff {term : Pattern} : IsObject (canon term) ↔ IsObject term := by
  simp only [IsObject, BagForms.canon_object]

theorem object_of_same {first second : Pattern} (same : canon first = canon second) (object : IsObject first) :
    IsObject second :=
  object_canon_iff.mp (same ▸ object_canon_iff.mpr object)

mutual
/-- **The captures of an object term are object terms.** -/
theorem captures_object : ∀ {pattern term : Pattern} {bindings : Bindings}, MatchRel pattern term bindings →
    IsObject term → ∀ entry ∈ bindings, IsObject entry.2
  | _, _, _, .fvar, object, entry, member => by
    rw [List.mem_singleton.mp member]
    exact object
  | _, _, _, .bvar, _, _, member => absurd member List.not_mem_nil
  | _, _, _, .apply arguments _, object, entry, member =>
    captures_object_args arguments (object_apply_iff.mp object) entry member
  | _, _, _, .lambda body, object, entry, member =>
    captures_object body (by simpa [IsObject, isObjectPattern] using object) entry member
  | _, _, _, .multiLambda body, object, entry, member =>
    captures_object body (by simpa [IsObject, isObjectPattern] using object) entry member
  | _, _, _, .collection _ bag, object, entry, member =>
    captures_object_bag bag (object_collection_iff.mp object).2 entry member
  | _, _, _, .vector arguments, object, entry, member =>
    captures_object_args arguments (object_collection_iff.mp object).2 entry member
  | _, _, _, .vectorRest arguments merged, object, entry, member => by
    have members := (object_collection_iff.mp object).2
    rcases mem_of_mergeBindings _ _ merged entry member with inPrefix | inRest
    · exact captures_object_args arguments (fun element inside => members element (List.mem_of_mem_take inside)) entry
        inPrefix
    · rw [List.mem_singleton.mp inRest]
      exact object_collection_iff.mpr ⟨rfl, fun element inside => members element (List.mem_of_mem_drop inside)⟩
  | _, _, _, .subst _ _ _, object, _, _ => by simp [IsObject, isObjectPattern] at object

theorem captures_object_args : ∀ {patterns terms : List Pattern} {bindings : Bindings},
    MatchArgsRel patterns terms bindings → (∀ term ∈ terms, IsObject term) → ∀ entry ∈ bindings, IsObject entry.2
  | _, _, _, .nil, _, _, member => absurd member List.not_mem_nil
  | _, _, _, .cons head tail merged, objects, entry, member => by
    rcases mem_of_mergeBindings _ _ merged entry member with inHead | inTail
    · exact captures_object head (objects _ List.mem_cons_self) entry inHead
    · exact captures_object_args tail (fun term inside => objects term (List.mem_cons_of_mem _ inside)) entry inTail

theorem captures_object_bag : ∀ {patterns : List Pattern} {rest : Option String} {kind : CollType}
    {terms : List Pattern} {bindings : Bindings}, MatchBagRel patterns rest kind terms bindings →
    (∀ term ∈ terms, IsObject term) → ∀ entry ∈ bindings, IsObject entry.2
  | _, _, _, _, _, .nilNoRest, _, _, member => absurd member List.not_mem_nil
  | _, _, _, _, _, .nilRest, objects, entry, member => by
    rw [List.mem_singleton.mp member]
    exact object_collection_iff.mpr ⟨rfl, objects⟩
  | _, _, _, _, _, .cons _ bound head tail merged, objects, entry, member => by
    rcases mem_of_mergeBindings _ _ merged entry member with inHead | inTail
    · exact captures_object head (objects _ (List.getElem_mem bound)) entry inHead
    · exact captures_object_bag tail (fun term inside => objects term (List.mem_of_mem_eraseIdx inside)) entry inTail
end

mutual
/-- **A schema whose instances are object terms**, given the rests that hold closed sets: each collection with a rest
is a set whose rest is one of them. -/
def objectSchema (rests : List String) : Pattern → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .apply _ arguments => objectSchemaList rests arguments
  | .lambda _ body => objectSchema rests body
  | .multiLambda _ _ body => objectSchema rests body
  | .subst body replacement => objectSchema rests body && objectSchema rests replacement
  | .collection kind elements rest =>
    (match rest with
      | none => true
      | some name => kind == .hashSet && decide (name ∈ rests)) && objectSchemaList rests elements

def objectSchemaList (rests : List String) : List Pattern → Bool
  | [] => true
  | pattern :: patterns => objectSchema rests pattern && objectSchemaList rests patterns
end

theorem objectSchemaList_iff {rests : List String} : ∀ {patterns : List Pattern},
    objectSchemaList rests patterns = true ↔ ∀ pattern ∈ patterns, objectSchema rests pattern = true
  | [] => by simp [objectSchemaList]
  | _ :: _ => by simp [objectSchemaList, objectSchemaList_iff]

/-- **Captures a derivation keeps**: object values, with the given rests holding closed sets. -/
def Kept (rests : List String) (bindings : Bindings) : Prop :=
  (∀ entry ∈ bindings, IsObject entry.2) ∧
    ∀ name ∈ rests, ∃ elements, bindings.find? (·.1 == name) = some (name, .collection .hashSet elements none)

/-- **A schema of kept captures instantiates to an object term.** -/
theorem applyBindingsScoped_object {lhs : Pattern} {bindings : Bindings} {rests : List String}
    (kept : Kept rests bindings) :
    ∀ (pattern : Pattern) (depth : ℕ), objectSchema rests pattern = true →
      IsObject (applyBindingsScoped lhs bindings depth pattern) := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth _; rfl
  | hfvar name =>
    intro depth _
    simp only [applyBindingsScoped]
    split
    · rename_i entry found
      have object := kept.1 _ (List.mem_of_find?_eq_some found)
      split
      · simp only [IsObject, Mettapedia.GSLT.LanguageDef.isObjectPattern_liftBVars]
        exact object
      · exact object
    · rfl
  | happly label arguments recurse =>
    intro depth schema
    simp only [objectSchema, objectSchemaList_iff] at schema
    simp only [applyBindingsScoped, applyBindingsScopedList_eq_map]
    refine object_apply_iff.mpr fun argument member => ?_
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
    exact recurse original inside depth (schema original inside)
  | hlambda binder body recurse =>
    intro depth schema
    simp only [objectSchema] at schema
    simpa [applyBindingsScoped, IsObject, isObjectPattern] using recurse (depth + 1) schema
  | hmultiLambda arity binders body recurse =>
    intro depth schema
    simp only [objectSchema] at schema
    simpa [applyBindingsScoped, IsObject, isObjectPattern] using recurse (depth + arity) schema
  | hsubst body replacement recurseBody recurseReplacement =>
    intro depth schema
    simp only [objectSchema, Bool.and_eq_true] at schema
    simp only [applyBindingsScoped]
    exact Mettapedia.OSLF.MeTTaIL.GeneralPremise.instantiateBVarAt_objects 0 (recurseBody (depth + 1) schema.1)
      (recurseReplacement depth schema.2)
  | hcollection kind elements rest recurse =>
    intro depth schema
    simp only [objectSchema, Bool.and_eq_true, objectSchemaList_iff] at schema
    obtain ⟨restSchema, elementsSchema⟩ := schema
    simp only [applyBindingsScoped, applyBindingsScopedList_eq_map]
    have elementsObject : ∀ element ∈ elements.map (applyBindingsScoped lhs bindings depth), IsObject element := by
      intro element member
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
      exact recurse original inside depth (elementsSchema original inside)
    cases rest with
    | none =>
      simp only [restSplice, List.append_nil]
      exact object_collection_iff.mpr ⟨rfl, elementsObject⟩
    | some name =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at restSchema
      obtain ⟨rfl, inRests⟩ := restSchema
      obtain ⟨restElements, found⟩ := kept.2 name inRests
      have restObject := kept.1 _ (List.mem_of_find?_eq_some found)
      have restMembers := (object_collection_iff.mp restObject).2
      rw [BagForms.restSplice_collection lhs depth .hashSet .hashSet found]
      simp only [beq_self_eq_true, if_true]
      refine object_collection_iff.mpr ⟨rfl, fun element member => ?_⟩
      rcases List.mem_append.mp member with inElements | inRest
      · exact elementsObject element inElements
      · split at inRest
        · obtain ⟨original, inside, rfl⟩ := List.mem_map.mp inRest
          simp only [IsObject, Mettapedia.GSLT.LanguageDef.isObjectPattern_liftBVars]
          exact restMembers original inside
        · exact restMembers element inRest

/-! ## Captures stay put -/

theorem find?_mergeBindings_of_find? : ∀ (second : Bindings) {first result : Bindings} {name : String}
    {entry : String × Pattern}, mergeBindings first second = some result →
    first.find? (·.1 == name) = some entry → result.find? (·.1 == name) = some entry
  | [], first, result, name, entry, merged, found => by
    simp only [mergeBindings, List.foldlM_nil, Option.pure_def, Option.some.injEq] at merged
    subst merged
    exact found
  | head :: tail, first, result, name, entry, merged, found => by
    rw [mergeBindings_cons] at merged
    cases hit : first.find? (fun item => item.1 == head.1) with
    | none =>
      rw [hit] at merged
      simp only [Option.bind_some] at merged
      refine find?_mergeBindings_of_find? tail merged ?_
      have other : head.1 ≠ name := by
        intro same
        subst same
        rw [found] at hit
        cases hit
      rw [List.find?_cons]
      simp only [beq_iff_eq, other, if_false]
      exact found
    | some existing =>
      rw [hit] at merged
      split at merged
      · simp only [Option.bind_some] at merged
        exact find?_mergeBindings_of_find? tail merged found
      · cases merged

theorem mem_of_mem_mergeBindings_left : ∀ (second : Bindings) {first result : Bindings} {entry : String × Pattern},
    mergeBindings first second = some result → entry ∈ first → entry ∈ result
  | [], first, result, entry, merged, member => by
    simp only [mergeBindings, List.foldlM_nil, Option.pure_def, Option.some.injEq] at merged
    subst merged
    exact member
  | head :: tail, first, result, entry, merged, member => by
    rw [mergeBindings_cons] at merged
    cases hit : first.find? (fun item => item.1 == head.1) with
    | none =>
      rw [hit] at merged
      simp only [Option.bind_some] at merged
      exact mem_of_mem_mergeBindings_left tail merged (List.mem_cons_of_mem _ member)
    | some existing =>
      rw [hit] at merged
      split at merged
      · simp only [Option.bind_some] at merged
        exact mem_of_mem_mergeBindings_left tail merged member
      · cases merged

theorem find?_bindParameter_of_ne {bindings : Bindings} {parameter name : String} {element : Pattern}
    (other : parameter ≠ name) :
    (bindParameter bindings parameter element).find? (·.1 == name) = bindings.find? (·.1 == name) := by
  simp only [bindParameter, List.find?_cons, beq_iff_eq, other, if_false]
  induction bindings with
  | nil => rfl
  | cons head tail ih =>
    by_cases same : head.1 = parameter
    · have : head.1 ≠ name := same ▸ other
      simp [List.filter_cons, same, List.find?_cons, this, ih]
    · by_cases hit : head.1 = name
      · simp [List.filter_cons, same, List.find?_cons, hit]
      · simp [List.filter_cons, same, List.find?_cons, hit, ih]

theorem kept_merge {rests : List String} {bindings matched result : Bindings} (kept : Kept rests bindings)
    (objects : ∀ entry ∈ matched, IsObject entry.2) (merged : mergeBindings bindings matched = some result) :
    Kept rests result := by
  refine ⟨fun entry member => ?_, fun name inRests => ?_⟩
  · rcases mem_of_mergeBindings _ _ merged entry member with inFirst | inSecond
    · exact kept.1 entry inFirst
    · exact objects entry inSecond
  · obtain ⟨elements, found⟩ := kept.2 name inRests
    exact ⟨elements, find?_mergeBindings_of_find? _ merged found⟩

theorem kept_bindParameter {rests : List String} {bindings : Bindings} {parameter : String} {element : Pattern}
    (kept : Kept rests bindings) (object : IsObject element) (fresh : parameter ∉ rests) :
    Kept rests (bindParameter bindings parameter element) := by
  refine ⟨fun entry member => ?_, fun name inRests => ?_⟩
  · simp only [bindParameter, List.mem_cons, List.mem_filter] at member
    rcases member with rfl | ⟨inside, -⟩
    · exact object
    · exact kept.1 entry inside
  · obtain ⟨elements, found⟩ := kept.2 name inRests
    refine ⟨elements, ?_⟩
    rw [find?_bindParameter_of_ne (fun same => fresh (same ▸ inRests))]
    exact found

theorem kept_canon {rests : List String} {bindings : Bindings} (kept : Kept rests bindings) :
    Kept rests (BagForms.canonBindings bindings) := by
  refine ⟨fun entry member => ?_, fun name inRests => ?_⟩
  · simp only [BagForms.canonBindings, List.mem_map] at member
    obtain ⟨original, inside, rfl⟩ := member
    exact object_canon_iff.mpr (kept.1 original inside)
  · obtain ⟨elements, found⟩ := kept.2 name inRests
    refine ⟨arrange .hashSet (elements.map canon), ?_⟩
    rw [BagForms.find?_canonBindings, found]
    simp [canon_collection]

/-! ## The left side binds its rests -/

/-- Closed hereditary patterns have no rests. -/
theorem restNames_hereditary {pattern : Pattern} (holds : Hereditary language sort pattern) : restNames pattern = [] := by
  induction holds with
  | atom _ => rfl
  | @members values _ inside =>
    show restNames (.collection .hashSet values none) = []
    simp only [restNames, Option.toList_none, List.nil_append]
    induction values with
    | nil => rfl
    | cons head tail ih =>
      simp only [restNamesList, inside head List.mem_cons_self, List.nil_append]
      exact ih (fun value member => (by assumption : ∀ value ∈ head :: tail, Hereditary language sort value) value
        (List.mem_cons_of_mem _ member)) fun value member => inside value (List.mem_cons_of_mem _ member)

theorem mem_of_mem_mergeBindings_right : ∀ (second : Bindings) {first result : Bindings} {entry : String × Pattern},
    mergeBindings first second = some result → entry ∈ second → entry ∈ result
  | [], _, _, _, _, member => absurd member List.not_mem_nil
  | head :: tail, first, result, entry, merged, member => by
    rw [mergeBindings_cons] at merged
    cases hit : first.find? (fun item => item.1 == head.1) with
    | none =>
      rw [hit] at merged
      simp only [Option.bind_some] at merged
      rcases List.mem_cons.mp member with rfl | inTail
      · exact mem_of_mem_mergeBindings_left tail merged List.mem_cons_self
      · exact mem_of_mem_mergeBindings_right tail merged inTail
    | some existing =>
      obtain ⟨existingName, existingValue⟩ := existing
      rw [hit] at merged
      simp only at merged
      split at merged
      · rename_i agree
        simp only [Option.bind_some] at merged
        rcases List.mem_cons.mp member with rfl | inTail
        · have sameName : existingName = entry.1 := by simpa using List.find?_some hit
          have sameValue : existingValue = entry.2 := by simpa using agree
          have inFirst : (existingName, existingValue) ∈ first := List.mem_of_find?_eq_some hit
          rw [sameName, sameValue] at inFirst
          exact mem_of_mem_mergeBindings_left tail merged inFirst
        · exact mem_of_mem_mergeBindings_right tail merged inTail
      · cases merged

theorem mem_restNamesList {name : String} : ∀ {patterns : List Pattern}, name ∈ restNamesList patterns →
    ∃ pattern ∈ patterns, name ∈ restNames pattern
  | [], member => by simp [restNamesList] at member
  | head :: tail, member => by
    simp only [restNamesList, List.mem_append] at member
    rcases member with inHead | inTail
    · exact ⟨head, List.mem_cons_self, inHead⟩
    · obtain ⟨pattern, inside, hit⟩ := mem_restNamesList inTail
      exact ⟨pattern, List.mem_cons_of_mem _ inside, hit⟩

theorem bag_rest_bound : ∀ {patterns : List Pattern} {rest : String} {kind : CollType} {terms : List Pattern}
    {bindings : Bindings}, MatchBagRel patterns (some rest) kind terms bindings →
    ∃ elements, (rest, .collection kind elements none) ∈ bindings
  | _, _, _, _, _, .nilRest => ⟨_, List.mem_singleton_self _⟩
  | _, _, _, _, _, .cons _ _ _ tail merged => by
    obtain ⟨elements, inside⟩ := bag_rest_bound tail
    exact ⟨elements, mem_of_mem_mergeBindings_right _ merged inside⟩

theorem bag_element_captures : ∀ {patterns : List Pattern} {rest : Option String} {kind : CollType}
    {terms : List Pattern} {bindings : Bindings}, MatchBagRel patterns rest kind terms bindings →
    ∀ pattern ∈ patterns, ∃ term captured, MatchRel pattern term captured ∧ ∀ entry ∈ captured, entry ∈ bindings
  | _, _, _, _, _, .nilNoRest, _, member => absurd member List.not_mem_nil
  | _, _, _, _, _, .nilRest, _, member => absurd member List.not_mem_nil
  | _, _, _, _, _, .cons _ _ head tail merged, pattern, member => by
    rcases List.mem_cons.mp member with rfl | inTail
    · exact ⟨_, _, head, fun entry inside => mem_of_mem_mergeBindings_left _ merged inside⟩
    · obtain ⟨term, captured, matched, inside⟩ := bag_element_captures tail pattern inTail
      exact ⟨term, captured, matched, fun entry hit => mem_of_mem_mergeBindings_right _ merged (inside entry hit)⟩

/-- **A nested element pattern's match binds each of its rests to a closed set.** -/
theorem rests_bound {bounds : List ℕ} {pattern : Pattern} (element : NestedElement language sort bounds pattern) :
    ∀ {term : Pattern} {bindings : Bindings}, MatchRel pattern term bindings →
      ∀ name ∈ restNames pattern, ∃ elements, (name, .collection .hashSet elements none) ∈ bindings := by
  induction element with
  | var _ _ =>
    intro term bindings _ name member
    simp [restNames] at member
  | closed _ holds _ =>
    intro term bindings _ name member
    rw [restNames_hereditary holds] at member
    cases member
  | @set bound bounds elements inner short each recurse =>
    intro term bindings matched name member
    cases matched with
    | collection _ bag =>
      simp only [restNames, List.mem_append] at member
      rcases member with inInner | inElements
      · cases inner with
        | none => cases inInner
        | some rest =>
          simp only [Option.toList_some, List.mem_singleton] at inInner
          subst inInner
          exact bag_rest_bound bag
      · obtain ⟨pattern, inside, hit⟩ := mem_restNamesList inElements
        obtain ⟨term', captured, matched', sub⟩ := bag_element_captures bag pattern inside
        obtain ⟨found, entry⟩ := recurse pattern inside matched' name hit
        exact ⟨found, sub _ entry⟩

theorem find?_of_mem_nodup {bindings : Bindings} {name : String} {value : Pattern}
    (distinct : (bindings.map Prod.fst).Nodup) (member : (name, value) ∈ bindings) :
    bindings.find? (·.1 == name) = some (name, value) := by
  obtain ⟨found, hit⟩ : ∃ found, bindings.find? (·.1 == name) = some found :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨_, member, by simp⟩)
  have sameName : found.1 = name := by simpa using List.find?_some hit
  rw [hit]
  congr 1
  exact List.inj_on_of_nodup_map distinct (List.mem_of_find?_eq_some hit) member sameName

/-! ## Admission -/

/-- Whether a premise steps, alone or inside a quantified premise. -/
def stepsInside : Premise → Bool
  | .congruence _ _ => true
  | .scopedStep _ => true
  | .forAll _ _ body => stepsInside body
  | _ => false

/-- **A premise admitted modulo the set laws**, given the rests of the rule's left side and whether every label is
kept: a freshness condition on a subject without explicit substitutions; a relation query over metavariables; a step
premise whose source instantiates to an object term and whose target is a nested element pattern with distinct
names; a quantified premise whose parameter is not a rest, whose body is admitted, and whose body does not step when
every label is kept. -/
def ModuloPremise (language : LanguageDef) (sort : String) (bounds : List ℕ) (rests : List String) (deep : Bool) :
    Premise → Prop
  | .freshness condition => substFree condition.term = true
  | .relationQuery _ arguments => arguments.all BagForms.isMetavariable = true
  | .congruence source target =>
    objectSchema rests source = true ∧ NestedElement language sort bounds target ∧ (patternNames target).Nodup
  | .scopedStep premise =>
    objectSchema rests premise.source = true ∧ NestedElement language sort bounds premise.target ∧
      (patternNames premise.target).Nodup
  | .forAll _ parameter body =>
    parameter ∉ rests ∧ ModuloPremise language sort bounds rests deep body ∧ (deep = true → stepsInside body = false)

/-- **A rule admitted modulo the set laws**: its left side is a nested element pattern under the bounds, with distinct
names; its right side instantiates to an object term; its premises are admitted. -/
structure ModuloRule (language : LanguageDef) (sort : String) (bounds : List ℕ) (deep : Bool) (rule : RewriteRule) :
    Prop where
  left : NestedElement language sort bounds rule.left
  distinct : (patternNames rule.left).Nodup
  right : objectSchema (restNames rule.left) rule.right = true
  premises : ∀ premise ∈ rule.premises, ModuloPremise language sort bounds (restNames rule.left) deep premise

/-- **A relation environment that answers alike requests alike**: asked about object terms, every answer holds object
terms, and a request alike to it has an answer alike. -/
def AnswersAlike (relEnv : RelationEnv) (language : LanguageDef) : Prop :=
  ∀ (relation : String) (request request' : List Pattern), (∀ value ∈ request, IsObject value) →
    List.Forall₂ Same request request' →
    ∀ tuple ∈ builtinRelationTuples language relation request ++ relEnv.tuples relation request,
      (∀ value ∈ tuple, IsObject value) ∧
        ∃ tuple' ∈ builtinRelationTuples language relation request' ++ relEnv.tuples relation request',
          List.Forall₂ Same tuple tuple'

/-- **The builtin relations answer alike requests alike.** -/
theorem answersAlike_empty : AnswersAlike RelationEnv.empty language := by
  intro relation request request' objects same tuple member
  simp only [RelationEnv.empty, List.append_nil] at member ⊢
  unfold builtinRelationTuples at member ⊢
  split at member
  · rename_i left right
    cases same with
    | cons sameLeft rest =>
      cases rest with
      | cons sameRight tail =>
        cases tail
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · refine ⟨fun value inside => ?_, _, List.mem_cons_self, .cons sameLeft (.cons sameLeft .nil)⟩
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl <;> exact objects _ List.mem_cons_self
        · refine ⟨fun value inside => ?_, _, List.mem_cons_of_mem _ List.mem_cons_self,
            .cons sameRight (.cons sameRight .nil)⟩
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl <;> exact objects _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · cases member

/-- **A hereditary set language read modulo the set laws**, under bounds by depth, keeping every label when `deep`. -/
structure ModuloSetLanguage (relEnv : RelationEnv) (language : LanguageDef) (carrier : GrammarRule) (bounds : List ℕ)
    (deep : Bool) : Prop where
  hereditary : HereditaryLanguage language carrier
  rules : ∀ rule ∈ language.rewrites, ModuloRule language carrier.category bounds deep rule
  answers : AnswersAlike relEnv language

/-! ## Labels -/

/-- **The labels kept**: every label when `deep`; otherwise those that do not look under a rule's premises. -/
def keptLabel (deep : Bool) : StepLabel → Bool
  | .under _ _ => deep
  | _ => true

/-- Two witnesses every label reads alike. -/
abbrev AgreeAll (first second : Witness) : Prop := ∀ label : StepLabel, label.admits first = label.admits second

theorem any_eq_of_forall₂ (label : StepLabel) : ∀ {first second : List Witness},
    List.Forall₂ AgreeAll first second → first.any label.admits = second.any label.admits
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons head tail => by
    simp only [List.any_cons, head label, any_eq_of_forall₂ label tail]

theorem admits_rule_agree (deep : Bool) {index : ℕ} {first second : Bindings} {premises premises' : List Witness}
    (steps : deep = true → List.Forall₂ AgreeAll (premiseStepsList premises) (premiseStepsList premises')) :
    ∀ label : StepLabel, keptLabel deep label = true →
      label.admits (.rule index first premises) = label.admits (.rule index second premises')
  | .any, _ => rfl
  | .rule _, _ => rfl
  | .under _ inner, kept => by
    simp only [keptLabel] at kept
    simp only [StepLabel.admits, any_eq_of_forall₂ inner (steps kept)]
  | .context _ _ _, _ => rfl

/-! ## Listed presentations -/

/-- **The listed presentations of a term's class**, under bounds by depth. -/
abbrev listed (bounds : List ℕ) : Pattern → List Pattern :=
  listedPresent BagForms.sortBags (capturePresentations bounds)

/-- **The reading of a language's rules modulo the set laws**, its steps listed under bounds by depth. -/
def moduloReading (bounds : List ℕ) : LanguageReading := { rules := .modulo BagForms.sortBags (capturePresentations bounds) }

/-- The set laws: terms with one canonical form. -/
abbrev setLaws : Setoid Pattern := canonSetoid BagForms.sortBags

theorem sortBags_mem_listed (bounds : List ℕ) (term : Pattern) : BagForms.sortBags term ∈ listed bounds term := by
  simp only [listed, listedPresent, List.mem_filter, sortBags_idem, beq_self_eq_true, and_true]
  exact self_mem_capturePresentations _ _

theorem mem_listed {bounds : List ℕ} {term shown : Pattern}
    (inside : shown ∈ capturePresentations bounds (BagForms.sortBags term)) : shown ∈ listed bounds term := by
  simp only [listed, listedPresent, List.mem_filter, beq_iff_eq]
  exact ⟨inside, capturePresentations_class (sortBags_idem term) inside⟩

/-- **A match of a nested element pattern at an object term moves to a listed presentation with canonical
captures.** -/
theorem capture_transfer_object {bounds : List ℕ} {pattern : Pattern} (element : NestedElement language sort bounds pattern)
    {term : Pattern} {bindings : Bindings} (object : IsObject term) (matched : MatchRel pattern term bindings)
    (distinct : (patternNames pattern).Nodup) :
    ∃ partner ∈ capturePresentations bounds (BagForms.sortBags term),
      MatchRel pattern partner (BagForms.canonBindings bindings) := by
  obtain ⟨partner, listedPartner, bindings', matched', same, kept⟩ :=
    capture_transfer_with (fun _ _ => True) (fun _ _ _ => trivial) (fun _ value => value) (fun _ _ canonical => canonical)
      (fun _ _ => self_mem_capturePresentations _ _) element object trivial matched distinct (fun _ _ _ => rfl)
  have canonical : CanonicalValues bindings' := fun entry member => (kept entry member).symm
  rw [← eq_canonBindings_of_same same canonical]
  exact ⟨partner, listedPartner, matched'⟩

/-! ## Premises that do not step -/

mutual
/-- **A premise that does not step contributes no step**, under any policy. -/
theorem premiseSteps_of_stepsInside {relEnv : RelationEnv} {policy : InternalBoundaryPolicy} :
    ∀ (premise : Premise) {sites : Pattern} {bindings result : Bindings} {witness : Witness},
      stepsInside premise = false → PremiseValid relEnv language sites bindings premise witness result policy →
        premiseSteps witness = []
  | .freshness _, _, _, _, _, _, valid => by cases valid <;> first | rfl | (simp [stepEndpoints] at *)
  | .relationQuery _ _, _, _, _, _, _, valid => by cases valid <;> first | rfl | (simp [stepEndpoints] at *)
  | .congruence _ _, _, _, _, _, quiet, _ => by simp [stepsInside] at quiet
  | .scopedStep _, _, _, _, _, quiet, _ => by simp [stepsInside] at quiet
  | .forAll _ _ body, _, _, _, _, quiet, valid => by
    simp only [stepsInside] at quiet
    cases valid with
    | forAll _ bodies => exact forAllSteps_of_stepsInside body quiet bodies
    | equationalForAll _ bodies => exact forAllSteps_of_stepsInside body quiet bodies
    | presentedForAll _ bodies => exact forAllSteps_of_stepsInside body quiet bodies
    | step endpoints _ _ _ => simp [stepEndpoints] at endpoints
    | equationalStep endpoints _ _ _ _ _ => simp [stepEndpoints] at endpoints
    | presentedStep endpoints _ _ _ _ _ => simp [stepEndpoints] at endpoints
    | base base _ => simp [isBase] at base

theorem forAllSteps_of_stepsInside {relEnv : RelationEnv} {policy : InternalBoundaryPolicy} (body : Premise)
    (quiet : stepsInside body = false) :
    ∀ {sites : Pattern} {bindings : Bindings} {parameter : String} {elements : List Pattern} {bodies : List Witness},
      ForAllValid relEnv language sites bindings parameter body elements bodies policy →
        premiseSteps (.forAll bodies) = []
  | _, _, _, [], [], _ => rfl
  | _, _, _, [], _ :: _, valid => by cases valid
  | _, _, _, _ :: _, [], valid => by cases valid
  | _, _, _, _ :: _, witness :: witnesses, valid => by
    have split : ∀ {first : Witness} {rest : List Witness},
        premiseSteps (.forAll (first :: rest)) = premiseSteps first ++ premiseSteps (.forAll rest) := by
      intro first rest
      simp only [premiseSteps, premiseStepsList]
    cases valid with
    | cons head tail =>
      rw [split, premiseSteps_of_stepsInside body quiet head, forAllSteps_of_stepsInside body quiet tail]
      rfl
    | equationalCons head tail =>
      rw [split, premiseSteps_of_stepsInside body quiet head, forAllSteps_of_stepsInside body quiet tail]
      rfl
    | presentedCons head tail =>
      rw [split, premiseSteps_of_stepsInside body quiet head, forAllSteps_of_stepsInside body quiet tail]
      rfl
end

/-! ## Quantified premises -/

theorem forAll_members {relEnv : RelationEnv} {theory : Setoid Pattern} {sites : Pattern} {bindings : Bindings}
    {parameter : String} {body : Premise} :
    ∀ {elements : List Pattern} {bodies : List Witness},
      ForAllValid relEnv language sites bindings parameter body elements bodies (.equational theory) →
      ∀ element ∈ elements, ∃ witness ∈ bodies, ∃ result,
        PremiseValid relEnv language sites (bindParameter bindings parameter element) body witness result
          (.equational theory)
  | [], _, _, _, member => absurd member List.not_mem_nil
  | _ :: _, [], valid, _, _ => by cases valid
  | element :: elements, witness :: witnesses, valid, other, member => by
    cases valid with
    | equationalCons head tail =>
      rcases List.mem_cons.mp member with rfl | inTail
      · exact ⟨witness, List.mem_cons_self, _, head⟩
      · obtain ⟨found, inside, result, valid⟩ := forAll_members tail other inTail
        exact ⟨found, List.mem_cons_of_mem _ inside, result, valid⟩

theorem forAllValid_of_each {relEnv : RelationEnv} {present : Pattern → List Pattern} {sites : Pattern}
    {bindings : Bindings} {parameter : String} {body : Premise} :
    ∀ (elements : List Pattern), (∀ element ∈ elements, ∃ witness result,
      PremiseValid relEnv language sites (bindParameter bindings parameter element) body witness result
        (.presented present)) →
    ∃ bodies, ForAllValid relEnv language sites bindings parameter body elements bodies (.presented present)
  | [], _ => ⟨[], .presentedNil⟩
  | element :: elements, each => by
    obtain ⟨witness, result, valid⟩ := each element List.mem_cons_self
    obtain ⟨bodies, rest⟩ := forAllValid_of_each elements fun other member => each other (List.mem_cons_of_mem _ member)
    exact ⟨witness :: bodies, .presentedCons valid rest⟩

/-! ## Relation queries -/

theorem matchRelationArgs_values : ∀ (arguments : List Pattern) {seed : Bindings} {tuple : List Pattern}
    {extension : Bindings}, arguments.all BagForms.isMetavariable = true →
    extension ∈ matchRelationArgs seed arguments tuple → ∀ entry ∈ extension, entry.2 ∈ tuple
  | [], seed, tuple, extension, _, matched, entry, member => by
    cases tuple with
    | nil =>
      simp only [matchRelationArgs, List.mem_singleton] at matched
      subst matched
      exact absurd member List.not_mem_nil
    | cons _ _ => simp [matchRelationArgs] at matched
  | argument :: arguments, seed, tuple, extension, metavariables, matched, entry, member => by
    simp only [List.all_cons, Bool.and_eq_true] at metavariables
    cases tuple with
    | nil => simp [matchRelationArgs] at matched
    | cons value values =>
      cases argument with
      | fvar name =>
        simp only [matchRelationArgs, List.mem_flatMap] at matched
        obtain ⟨head, headMember, rest⟩ := matched
        split at rest
        · cases rest
        · rename_i extended _
          obtain ⟨tail, tailMember, merged⟩ := List.mem_filterMap.mp rest
          rcases mem_of_mergeBindings _ _ merged entry member with inHead | inTail
          · simp only [matchRelationArgument] at headMember
            split at headMember
            · split at headMember
              · rw [List.mem_singleton.mp headMember] at inHead
                exact absurd inHead List.not_mem_nil
              · exact absurd headMember List.not_mem_nil
            · rw [List.mem_singleton.mp headMember, List.mem_singleton] at inHead
              rw [inHead]
              exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (matchRelationArgs_values arguments metavariables.2 tailMember entry inTail)
      | _ => simp [BagForms.isMetavariable] at metavariables
termination_by arguments => arguments.length

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
