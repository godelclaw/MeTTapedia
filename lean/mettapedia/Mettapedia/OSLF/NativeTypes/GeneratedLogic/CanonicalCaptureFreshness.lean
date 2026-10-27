import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureSetRules
import Mettapedia.OSLF.MeTTaIL.BindingAgreement

/-!
# Freshness premises at canonical captures

A freshness premise `x # M` holds when the name `x` resolves, through the captures, to a name not free in `M` with the
captures substituted. Canonical forms write the members of collections in one order and once in a set, and keep the
names that occur (`canon_freeVars`), so canonical captures keep the free names of every subject without explicit
substitutions (`freeVars_applyBindings_canon`) and resolve every name alike. A freshness premise therefore holds at
canonical captures (`premiseCanon_freshness`), beside the queries and universally quantified premises of
`CanonicalCaptureSetRules`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution (freeVars isFresh checkFreshness)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (canon arrange arrange_mem to_canon BagStep canon_apply canon_collection)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep

/-! ## Canonical forms keep the names that occur -/

theorem bagStep_freeVars_mem {left right : Pattern} (step : BagStep left right) (name : String) :
    name ∈ freeVars left ↔ name ∈ freeVars right := by
  induction step with
  | permute _ permutation =>
    simp only [freeVars, List.mem_flatMap]
    exact ⟨fun ⟨item, member, inside⟩ => ⟨item, permutation.subset member, inside⟩,
      fun ⟨item, member, inside⟩ => ⟨item, permutation.symm.subset member, inside⟩⟩
  | members same =>
    simp only [freeVars, List.mem_flatMap]
    exact ⟨fun ⟨item, member, inside⟩ => ⟨item, (same item).mp member, inside⟩,
      fun ⟨item, member, inside⟩ => ⟨item, (same item).mpr member, inside⟩⟩
  | apply _ ih => simp [freeVars, List.mem_flatMap, ih]
  | lambda _ ih => simp [freeVars, ih]
  | multiLambda _ ih => simp [freeVars, ih]
  | substBody _ ih => simp [freeVars, ih]
  | substReplacement _ ih => simp [freeVars, ih]
  | element _ ih => simp [freeVars, List.mem_flatMap, ih]

/-- **Canonical forms keep the names that occur.** -/
theorem canon_freeVars (pattern : Pattern) (name : String) : name ∈ freeVars (canon pattern) ↔ name ∈ freeVars pattern := by
  suffices keep : ∀ {a b : Pattern}, Relation.EqvGen BagStep a b → (name ∈ freeVars a ↔ name ∈ freeVars b) from
    (keep (to_canon pattern)).symm
  intro a b related
  induction related with
  | rel _ _ step => exact bagStep_freeVars_mem step name
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-! ## Canonical captures keep the free names of a subject -/

mutual
/-- **A pattern without explicit substitutions.** -/
def substFree : Pattern → Bool
  | .bvar _ | .fvar _ => true
  | .apply _ arguments => substFreeList arguments
  | .lambda _ body | .multiLambda _ _ body => substFree body
  | .subst _ _ => false
  | .collection _ elements _ => substFreeList elements

def substFreeList : List Pattern → Bool
  | [] => true
  | pattern :: patterns => substFree pattern && substFreeList patterns
end

theorem substFreeList_iff : ∀ {patterns : List Pattern}, substFreeList patterns = true ↔ ∀ pattern ∈ patterns,
    substFree pattern = true
  | [] => by simp [substFreeList]
  | _ :: _ => by simp [substFreeList, substFreeList_iff]

/-- **A spliced rest keeps its free names at canonical captures**: the canonical form of a bound collection lists the
canonical forms of its members. -/
theorem restResolution_canon (bindings : Bindings) (kind : CollType) (rest : Option String) (name : String) :
    name ∈ (restResolution (BagForms.canonBindings bindings) kind rest).1.flatMap freeVars ↔
      name ∈ (restResolution bindings kind rest).1.flatMap freeVars := by
  cases rest with
  | none => rfl
  | some spliced =>
    simp only [restResolution, BagForms.find?_canonBindings]
    cases bindings.find? (fun entry : String × Pattern => entry.1 == spliced) with
    | none => rfl
    | some entry =>
      obtain ⟨key, value⟩ := entry
      simp only [Option.map_some]
      cases value with
      | collection boundKind boundElements innerRest =>
        rw [canon_collection]
        cases innerRest with
        | some _ => rfl
        | none =>
          by_cases same : (boundKind == kind) = true
          · simp only [same, if_true, List.mem_flatMap]
            constructor
            · rintro ⟨item, member, inside⟩
              obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp ((arrange_mem _).mp member)
              exact ⟨original, originalMember, (canon_freeVars original name).mp inside⟩
            · rintro ⟨item, member, inside⟩
              exact ⟨canon item, (arrange_mem _).mpr (List.mem_map_of_mem member),
                (canon_freeVars item name).mpr inside⟩
          · simp [same]
      | apply label arguments => rw [canon_apply]
      | _ => simp [canon]

/-- **Canonical captures keep the free names of a subject without explicit substitutions.** -/
theorem freeVars_applyBindings_canon (bindings : Bindings) (name : String) (subject : Pattern)
    (free : substFree subject = true) :
    name ∈ freeVars (applyBindings (BagForms.canonBindings bindings) subject) ↔
      name ∈ freeVars (applyBindings bindings subject) := by
  induction subject using Pattern.inductionOn with
  | hbvar index => simp [applyBindings]
  | hfvar captured =>
    rw [BagForms.applyBindings_var, BagForms.applyBindings_var, BagForms.lookup_canonBindings]
    cases Bindings.lookup bindings captured with
    | none => rfl
    | some value => exact canon_freeVars value name
  | happly label arguments recurse =>
    simp only [substFree, substFreeList_iff] at free
    simp only [applyBindings, freeVars, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨_, ⟨argument, member, rfl⟩, inside⟩
      exact ⟨_, ⟨argument, member, rfl⟩, (recurse argument member (free argument member)).mp inside⟩
    · rintro ⟨_, ⟨argument, member, rfl⟩, inside⟩
      exact ⟨_, ⟨argument, member, rfl⟩, (recurse argument member (free argument member)).mpr inside⟩
  | hlambda binder body recurse =>
    simp only [substFree] at free
    simpa [applyBindings, freeVars] using recurse free
  | hmultiLambda arity binders body recurse =>
    simp only [substFree] at free
    simpa [applyBindings, freeVars] using recurse free
  | hsubst body replacement _ _ => simp [substFree] at free
  | hcollection kind elements rest recurse =>
    simp only [substFree, substFreeList_iff] at free
    rw [applyBindings_collection, applyBindings_collection]
    simp only [freeVars, List.flatMap_append, List.mem_append]
    refine or_congr ?_ (restResolution_canon bindings kind rest name)
    simp only [List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨_, ⟨element, member, rfl⟩, inside⟩
      exact ⟨_, ⟨element, member, rfl⟩, (recurse element member (free element member)).mp inside⟩
    · rintro ⟨_, ⟨element, member, rfl⟩, inside⟩
      exact ⟨_, ⟨element, member, rfl⟩, (recurse element member (free element member)).mpr inside⟩

/-! ## Freshness at canonical captures -/

/-- How a freshness premise resolves its name through the captures. -/
def resolved (bindings : Bindings) (name : String) : Option String :=
  match bindings.lookup name with
  | some (.fvar other) => some other
  | some _ => none
  | none => some name

theorem resolved_canonBindings (bindings : Bindings) (name : String) :
    resolved (BagForms.canonBindings bindings) name = resolved bindings name := by
  unfold resolved
  rw [BagForms.lookup_canonBindings]
  cases Bindings.lookup bindings name with
  | none => rfl
  | some value =>
    cases value with
    | fvar other => simp [canon]
    | bvar => simp [canon]
    | apply => rw [Option.map_some, canon_apply]
    | lambda => simp [canon]
    | multiLambda => simp [canon]
    | subst => simp [canon]
    | collection => rw [Option.map_some, canon_collection]

/-- A freshness premise holds when its name resolves to a name fresh in the subject. -/
theorem mem_freshness {relEnv : RelationEnv} {language : LanguageDef} {bindings : Bindings}
    {condition : FreshnessCondition} {name : String} (resolves : resolved bindings condition.varName = some name)
    (fresh : isFresh name (applyBindings bindings condition.term) = true) :
    bindings ∈ Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv relEnv language bindings (.freshness condition) := by
  simp only [Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv]
  change bindings ∈ (match resolved bindings condition.varName with
    | some x => if checkFreshness { varName := x, term := applyBindings bindings condition.term } then [bindings] else []
    | none => [])
  rw [resolves]
  simp [checkFreshness, fresh]

/-- **A freshness premise that holds at some captures holds at their canonical forms**, for a subject without
explicit substitutions; it passes the captures on unchanged. -/
theorem freshness_canon {relEnv : RelationEnv} {language : LanguageDef} {condition : FreshnessCondition}
    (free : substFree condition.term = true) {bindings result : Bindings}
    (member : result ∈ Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv relEnv language bindings (.freshness condition)) :
    result = bindings ∧ BagForms.canonBindings bindings ∈
      Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv relEnv language (BagForms.canonBindings bindings)
        (.freshness condition) := by
  have same : result = bindings := Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv_freshness_mem member
  refine ⟨same, ?_⟩
  rw [same] at member
  obtain ⟨name, resolves, fresh⟩ := Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv_freshness_check member
  refine mem_freshness (name := name) ?_ ?_
  · rw [resolved_canonBindings]
    exact resolves
  · have absent : name ∉ freeVars (applyBindings bindings condition.term) := by simpa [isFresh] using fresh
    have kept : name ∉ freeVars (applyBindings (BagForms.canonBindings bindings) condition.term) := fun inside =>
      absent ((freeVars_applyBindings_canon bindings name condition.term free).mp inside)
    simpa [isFresh] using kept

/-- **A freshness premise holds at canonical captures**, for a subject without explicit substitutions. -/
theorem premiseCanon_freshness {relEnv : RelationEnv} {language : LanguageDef} {condition : FreshnessCondition}
    (free : substFree condition.term = true) : PremiseCanon relEnv language (.freshness condition) := by
  intro sites initial result witness valid
  cases valid with
  | base _ member =>
    obtain ⟨same, canonical⟩ := freshness_canon free member
    subst same
    exact ⟨rfl, .base _, .base rfl canonical, rfl⟩
  | step endpoints => simp [stepEndpoints] at endpoints

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
