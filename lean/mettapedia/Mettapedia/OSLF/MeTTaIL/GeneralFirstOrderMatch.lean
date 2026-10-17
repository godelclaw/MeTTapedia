import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
import Mettapedia.OSLF.MeTTaIL.LinearMatch

/-!
# First-order matching of substitution instances

Merging partial readbacks of one substitution cannot produce a conflicting
assignment. This fact supplies ordinary relational matches for constructor
patterns instantiated by that substitution, including repeated metavariables.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match MatchSpec

def Compatible (environment bindings : Bindings) : Prop :=
  ∀ entry ∈ bindings, environment.lookup entry.1 = some entry.2

def SameNames (bindings : Bindings) (names : List String) : Prop :=
  ∀ name, name ∈ bindings.map Prod.fst ↔ name ∈ names

def Defined (environment : Bindings) (names : List String) : Prop :=
  ∀ name ∈ names, ∃ value, environment.lookup name = some value

/-- Observe bindings in a declared name order, retaining missing entries.
This reads the original store; it neither sorts nor deduplicates that store. -/
def bindingReadout (names : List String) (bindings : Bindings) : List (String × Option Pattern) :=
  names.map fun name => (name, bindings.lookup name)

theorem bindingReadout_eq_of_lookups (names : List String) (first second : Bindings)
    (same : ∀ name, first.lookup name = second.lookup name) :
    bindingReadout names first = bindingReadout names second := by
  apply List.map_congr_left
  intro name _
  rw [same name]

theorem lookup_none_iff_not_mem_names (bindings : Bindings) (name : String) :
    bindings.lookup name = none ↔ name ∉ bindings.map Prod.fst := by
  induction bindings with
  | nil => simp [Bindings.lookup]
  | cons entry bindings ih =>
    rcases entry with ⟨key, value⟩
    by_cases same : key = name
    · subst key
      simp [Bindings.lookup]
    · have test : (key == name) = false := by simp [same]
      simpa only [Bindings.lookup, List.find?_cons, test, Bool.false_eq_true, if_false,
        List.map_cons, List.mem_cons, not_or, ne_eq, Ne.symm same, false_or,
        true_and] using ih

theorem lookup_some_iff_mem_names (bindings : Bindings) (name : String) :
    (∃ value, bindings.lookup name = some value) ↔ name ∈ bindings.map Prod.fst := by
  constructor
  · rintro ⟨value, found⟩
    by_contra absent
    have empty := (lookup_none_iff_not_mem_names bindings name).mpr absent
    rw [found] at empty
    cases empty
  · intro present
    cases found : bindings.lookup name with
    | none => exact False.elim ((lookup_none_iff_not_mem_names bindings name).mp found present)
    | some value => exact ⟨value, rfl⟩

theorem apply_variable (environment : Bindings) (name : String) :
    applyBindings environment (.fvar name) = (environment.lookup name).getD (.fvar name) := by
  cases found : environment.find? (fun entry => entry.1 == name) <;>
    simp [applyBindings, Bindings.lookup, found]

theorem merge_compatible (environment : Bindings) (first second : Bindings)
    (firstCompatible : Compatible environment first) (secondCompatible : Compatible environment second)
    (firstUnique : (first.map Prod.fst).Nodup) :
    ∃ result, mergeBindings first second = some result ∧ Compatible environment result ∧
      (result.map Prod.fst).Nodup ∧
      ∀ name, name ∈ result.map Prod.fst ↔ name ∈ first.map Prod.fst ∨ name ∈ second.map Prod.fst := by
  induction second generalizing first with
  | nil => exact ⟨first, rfl, firstCompatible, firstUnique, by simp⟩
  | cons entry rest ih =>
    rcases entry with ⟨name, value⟩
    have valueRead := secondCompatible (name, value) (by simp)
    have restCompatible : Compatible environment rest := fun pair member =>
      secondCompatible pair (List.mem_cons_of_mem _ member)
    cases found : first.find? (fun pair => pair.1 == name) with
    | none =>
      have fresh : name ∉ first.map Prod.fst := by
        intro member
        obtain ⟨pair, pairMember, key⟩ := List.mem_map.mp member
        have fails := List.find?_eq_none.mp found pair pairMember
        exact fails (by simp [key])
      have extendedCompatible : Compatible environment ((name, value) :: first) := by
        intro pair member
        rcases List.mem_cons.mp member with rfl | member
        · exact valueRead
        · exact firstCompatible pair member
      obtain ⟨result, merged, compatible, unique, names⟩ := ih ((name, value) :: first)
        extendedCompatible restCompatible (List.nodup_cons.mpr ⟨fresh, firstUnique⟩)
      refine ⟨result, ?_, compatible, unique, ?_⟩
      · simpa [mergeBindings, List.foldlM_cons, found] using merged
      · intro queried
        simpa only [List.map_cons, List.mem_cons, or_assoc, or_left_comm] using names queried
    | some pair =>
      have member := List.mem_of_find?_eq_some found
      have key : pair.1 = name := beq_iff_eq.mp
        (List.find?_some (p := fun entry : String × Pattern => entry.1 == name) found)
      have same : pair.2 = value := Option.some.inj ((key ▸ firstCompatible pair member).symm.trans valueRead)
      have nameMember : name ∈ first.map Prod.fst := by
        rw [← key]
        exact List.mem_map_of_mem member
      obtain ⟨result, merged, compatible, unique, names⟩ := ih first firstCompatible restCompatible firstUnique
      refine ⟨result, ?_, compatible, unique, ?_⟩
      · simpa [mergeBindings, List.foldlM_cons, found, same] using merged
      · intro queried
        simp only [List.map_cons, List.mem_cons]
        rw [names]
        constructor
        · rintro (before | after)
          · exact .inl before
          · exact .inr (.inr after)
        · rintro (before | rfl | after)
          · exact .inl before
          · exact .inl nameMember
          · exact .inr after

mutual
  theorem match_instance (environment : Bindings) {schema : Pattern}
      (shape : FirstOrder schema) (defined : Defined environment schema.freeFvarNames) :
      ∃ bindings, MatchRel schema (applyBindings environment schema) bindings ∧
        Compatible environment bindings ∧ (bindings.map Prod.fst).Nodup ∧
        SameNames bindings schema.freeFvarNames := by
    cases shape with
    | metavariable name =>
      obtain ⟨value, found⟩ := defined name (by simp [Pattern.freeFvarNames])
      refine ⟨[(name, value)], ?_, ?_, by simp, ?_⟩
      · simpa only [apply_variable, found, Option.getD_some] using
          (MatchRel.fvar : MatchRel (.fvar name) value [(name, value)])
      · intro entry member
        cases List.mem_singleton.mp member
        exact found
      · intro queried
        simp only [List.map_cons, List.map_nil, Pattern.freeFvarNames, List.mem_singleton]
    | constructor label arguments shapes =>
      obtain ⟨bindings, matched, compatible, unique, names⟩ :=
        match_arguments_instance environment shapes (by
          simpa only [Pattern.freeFvarNames] using defined)
      refine ⟨bindings, ?_, compatible, unique, ?_⟩
      · simpa only [applyBindings] using (MatchRel.apply matched (by simp) :
          MatchRel (.apply label arguments) (.apply label (arguments.map (applyBindings environment))) bindings)
      · simpa only [Pattern.freeFvarNames] using names
  termination_by sizeOf schema

  theorem match_arguments_instance (environment : Bindings) {schemas : List Pattern}
      (shapes : ∀ schema ∈ schemas, FirstOrder schema)
      (defined : Defined environment (schemas.flatMap Pattern.freeFvarNames)) :
      ∃ bindings, MatchArgsRel schemas (schemas.map (applyBindings environment)) bindings ∧
        Compatible environment bindings ∧ (bindings.map Prod.fst).Nodup ∧
        SameNames bindings (schemas.flatMap Pattern.freeFvarNames) := by
    cases schemas with
    | nil => exact ⟨[], .nil, by simp [Compatible], by simp, by simp [SameNames]⟩
    | cons schema schemas =>
      obtain ⟨first, firstMatch, firstCompatible, firstUnique, firstNames⟩ :=
        match_instance environment (shapes schema (by simp))
          (fun name member => defined name (by simp [member]))
      obtain ⟨second, secondMatch, secondCompatible, _, secondNames⟩ :=
        match_arguments_instance environment (schemas := schemas)
          (fun child member => shapes child (List.mem_cons_of_mem _ member))
          (fun name member => defined name (by simp [member]))
      obtain ⟨combined, merged, compatible, unique, names⟩ :=
        merge_compatible environment first second firstCompatible secondCompatible firstUnique
      refine ⟨combined, .cons firstMatch secondMatch merged, compatible, unique, ?_⟩
      intro name
      rw [names, firstNames, secondNames]
      simp only [List.flatMap_cons, List.mem_append]
  termination_by sizeOf schemas
end

theorem compatible_lookup {environment bindings : Bindings}
    (compatible : Compatible environment bindings) {name : String}
    (member : name ∈ bindings.map Prod.fst) : bindings.lookup name = environment.lookup name := by
  cases found : bindings.find? (fun entry => entry.1 == name) with
  | none =>
    obtain ⟨entry, inList, key⟩ := List.mem_map.mp member
    exact (List.find?_eq_none.mp found entry inList (by simp [key])).elim
  | some entry =>
    have inList := List.mem_of_find?_eq_some found
    have key : entry.1 = name := beq_iff_eq.mp
      (List.find?_some (p := fun entry : String × Pattern => entry.1 == name) found)
    simp only [Bindings.lookup, found, Option.map_some]
    exact (key ▸ compatible entry inList).symm

/-- Compatibility with the exact same domain determines all lookups,
including missing names outside the domain. -/
theorem compatible_lookup_all {environment bindings : Bindings}
    (compatible : Compatible environment bindings)
    (names : SameNames bindings (environment.map Prod.fst)) :
    ∀ name, bindings.lookup name = environment.lookup name := by
  intro name
  by_cases present : name ∈ bindings.map Prod.fst
  · exact compatible_lookup compatible present
  · have absent : name ∉ environment.map Prod.fst := fun member => present ((names name).mpr member)
    rw [(lookup_none_iff_not_mem_names bindings name).mpr present,
      (lookup_none_iff_not_mem_names environment name).mpr absent]

theorem compatible_bindingReadout {environment bindings : Bindings}
    (compatible : Compatible environment bindings)
    (names : SameNames bindings (environment.map Prod.fst)) (order : List String) :
    bindingReadout order bindings = bindingReadout order environment :=
  bindingReadout_eq_of_lookups order bindings environment (compatible_lookup_all compatible names)

theorem apply_eq_of_same_lookups {first second : Bindings} {schema : Pattern}
    (shape : FirstOrder schema)
    (same : ∀ name ∈ schema.freeFvarNames, first.lookup name = second.lookup name) :
    applyBindings first schema = applyBindings second schema := by
  induction schema using Pattern.inductionOn with
  | hfvar name => rw [apply_variable, apply_variable, same name (by simp [Pattern.freeFvarNames])]
  | happly label arguments ih =>
    cases shape with
    | constructor _ _ shapes =>
      simp only [applyBindings]
      apply congrArg (Pattern.apply label)
      exact List.map_congr_left (fun argument member => ih argument member (shapes argument member)
        (fun name occurs => same name (by
          simpa only [Pattern.freeFvarNames] using
            (List.mem_flatMap.mpr ⟨argument, member, occurs⟩ : name ∈ arguments.flatMap Pattern.freeFvarNames))))
  | hbvar | hlambda | hmultiLambda | hsubst | hcollection => cases shape

theorem compatible_readout {environment bindings : Bindings} {schema : Pattern}
    (shape : FirstOrder schema) (compatible : Compatible environment bindings)
    (bound : ∀ name ∈ schema.freeFvarNames, name ∈ bindings.map Prod.fst) :
    applyBindings bindings schema = applyBindings environment schema :=
  apply_eq_of_same_lookups shape (fun name member => compatible_lookup compatible (bound name member))

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
