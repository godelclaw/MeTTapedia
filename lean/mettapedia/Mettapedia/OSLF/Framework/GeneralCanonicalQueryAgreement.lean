import Mettapedia.OSLF.Framework.GeneralCanonicalPremiseAgreement
import Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseWeakening
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSchemaProjection

/-!
# Relation queries in the general and canonical semantics

A relation query `R a₁ … aₙ` holds in the general semantics when a provider row of
`R` fits the arguments: an input argument is instantiated and must equal the row
value, and an output argument is matched against it. The canonical engine matches
every argument against a tuple of its relation environment, threading the bindings
from one argument to the next.

For first-order arguments the two agree, when the relation environment answers each
declared relation with the same tuple membership as the provider (`ReadsProvider`).
This agreement does not require the same enumeration order or multiplicity. This module
proves the pieces: the canonical matcher is sound and typed, it finds the instance
of a known substitution, and the general moded arguments read back as the row and
can be constructed from a canonical match. It also collects the first-order lemmas
shared by the premise agreement proofs.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.GeneralCanonicalAgreement

open Mettapedia.OSLF.MeTTaIL
open MeTTaIL.Syntax MeTTaIL.Match MeTTaIL.MatchSpec
open MeTTaIL.ScopedRuleMatching MeTTaIL.RuleBinding MeTTaIL.GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted
open Engine (matchRelationArgument matchRelationArgs)

/-! ## Reading first-order instantiations against a later assignment -/

mutual
 /-- A first-order instantiation succeeds only where every name is bound. -/
 theorem instantiation_bound {operation : Pattern → Pattern → Pattern} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite} {path : List Nat}
    {depth : Nat} {assignment : Assignment} {schema target : Pattern} (shape : FirstOrder schema)
    (read : instantiateWith? operation rule spec ambient site path depth assignment schema = some target) :
    GeneralPremise.BoundNames assignment schema.freeFvarNames := by
  cases shape with
  | metavariable name =>
    simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
    obtain ⟨value, found, _⟩ := read
    intro queried member
    have same : queried = name := by simpa [Pattern.freeFvarNames] using member
    subst same
    exact ⟨value, found⟩
  | constructor label arguments shapes =>
    simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
    obtain ⟨results, read, _⟩ := read
    simpa only [Pattern.freeFvarNames] using instantiation_arguments_bound shapes read
 termination_by sizeOf schema

 theorem instantiation_arguments_bound {operation : Pattern → Pattern → Pattern}
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite}
    {path : List Nat} {depth index : Nat} {assignment : Assignment} {schemas targets : List Pattern}
    (shapes : ∀ schema ∈ schemas, FirstOrder schema)
    (read : instantiateArgsWith? operation rule spec ambient site path depth assignment index schemas =
      some targets) :
    GeneralPremise.BoundNames assignment (schemas.flatMap Pattern.freeFvarNames) := by
  cases schemas with
  | nil => intro _ member; cases member
  | cons schema schemas =>
    simp only [instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
    obtain ⟨target, first, targets, rest, _⟩ := read
    have head := instantiation_bound (shapes schema (by simp)) first
    have tail := instantiation_arguments_bound
      (fun child member => shapes child (List.mem_cons_of_mem _ member)) rest
    intro name member
    simp only [List.flatMap_cons, List.mem_append] at member
    rcases member with earlier | later
    · exact head name earlier
    · exact tail name later
 termination_by sizeOf schemas
end

theorem roots_of_extends {ambient : Nat} {initial chosen : Assignment}
    (later : GeneralScopedMatch.Extends initial chosen)
    (roots : GeneralPremise.RootValues ambient chosen) : GeneralPremise.RootValues ambient initial :=
  fun name value found => roots name value (later name value found)

theorem ordinary_lookup_of_extends {initial chosen : Assignment}
    (later : GeneralScopedMatch.Extends initial chosen) {name : String} {value : ContextualValue}
    (found : lookup initial name = some value) :
    (ordinary chosen).lookup name = (ordinary initial).lookup name := by
  rw [ordinary_lookup, ordinary_lookup, later name value found, found]

/-- An instantiation made from an earlier assignment is the ordinary
instantiation by any later assignment that extends it. -/
theorem readout_chosen {operation : Pattern → Pattern → Pattern} {rule : RewriteRule}
    {ambient : Nat} {site : RulePatternSite} {path : List Nat} {assignment chosen : Assignment}
    {schema target : Pattern} (shape : FirstOrder schema)
    (later : GeneralScopedMatch.Extends assignment chosen)
    (roots : GeneralPremise.RootValues ambient chosen)
    (read : instantiateWith? operation rule (GeneralRuleBindingInference.inferredSpec rule)
      ambient site path 0 assignment schema = some target) :
    applyBindings (ordinary chosen) schema = target := by
  rw [← instantiation_readout shape (roots_of_extends later roots) read]
  apply apply_eq_of_same_lookups shape
  intro name member
  obtain ⟨value, found⟩ := instantiation_bound shape read name member
  exact ordinary_lookup_of_extends later found

/-! ## Binding lists -/

theorem merge_lookup_left {first second combined : Bindings}
    (merged : mergeBindings first second = some combined) {name : String} {value : Pattern}
    (found : first.lookup name = some value) : combined.lookup name = some value :=
  MatchBindingExtension.lookup_preserved
    (fun _ _ selected => mergeBindings_subsumed_left merged selected) found

theorem merge_lookup_right {first second combined : Bindings}
    (merged : mergeBindings first second = some combined) {name : String} {value : Pattern}
    (found : second.lookup name = some value) : combined.lookup name = some value :=
  MatchBindingExtension.lookup_preserved
    (fun _ _ selected => mergeBindings_subsumed_right merged selected) found

/-- A binding list that keeps the lookups of both sides of a merge keeps the
lookups of the merge. -/
theorem extends_merge {first second combined result : Bindings}
    (merged : mergeBindings first second = some combined)
    (left : BindingsExtends first result) (right : BindingsExtends second result) :
    BindingsExtends combined result := by
  intro name value found
  cases firstFound : first.find? (·.1 == name) with
  | some entry =>
    obtain ⟨entryName, entryValue⟩ := entry
    have key : entryName = name := beq_iff_eq.mp
      (List.find?_some (p := fun entry : String × Pattern => entry.1 == name) firstFound)
    subst key
    rw [mergeBindings_subsumed_left merged firstFound] at found
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at found
    subst found
    exact left _ _ firstFound
  | none =>
    have member : (name, value) ∈ combined := by
      have selected := List.mem_of_find?_eq_some found
      exact selected
    rcases List.mem_append.mp (merge_members merged member) with inFirst | inSecond
    · exact absurd (List.find?_eq_none.mp firstFound _ inFirst) (by simp)
    · cases secondFound : second.find? (·.1 == name) with
      | none => exact absurd (List.find?_eq_none.mp secondFound _ inSecond) (by simp)
      | some entry =>
        obtain ⟨entryName, entryValue⟩ := entry
        have key : entryName = name := beq_iff_eq.mp
          (List.find?_some (p := fun entry : String × Pattern => entry.1 == name) secondFound)
        subst key
        rw [mergeBindings_subsumed_right merged secondFound] at found
        simp only [Option.some.injEq, Prod.mk.injEq, true_and] at found
        subst found
        exact right _ _ secondFound

theorem compatible_lift {ambient : Nat} {small large : Bindings} {assignment : Assignment}
    (compatible : ScopedCompatible ambient small assignment)
    (preserved : ∀ name value, small.lookup name = some value → large.lookup name = some value) :
    ScopedCompatible ambient large assignment := fun entry member =>
  let ⟨empty, caller, read⟩ := compatible entry member
  ⟨empty, caller, preserved _ _ read⟩

theorem compatible_defined {ambient : Nat} {environment : Bindings} {assignment : Assignment}
    (compatible : ScopedCompatible ambient environment assignment) {names : List String}
    (bound : GeneralPremise.BoundNames assignment names) : Defined environment names := by
  intro name member
  obtain ⟨value, found⟩ := bound name member
  obtain ⟨_, _, read⟩ := compatible (name, value)
    (ConditionalEquationExecution.lookup_assignment_member assignment name value found)
  exact ⟨value.body, read⟩

/-- On the names an assignment binds, its ordinary projection is the environment
it is compatible with. -/
theorem compatible_apply_eq {ambient : Nat} {environment : Bindings} {assignment : Assignment}
    (compatible : ScopedCompatible ambient environment assignment) {schema : Pattern}
    (shape : FirstOrder schema) (bound : GeneralPremise.BoundNames assignment schema.freeFvarNames) :
    applyBindings (ordinary assignment) schema = applyBindings environment schema := by
  apply apply_eq_of_same_lookups shape
  intro name member
  obtain ⟨value, found⟩ := bound name member
  obtain ⟨_, _, read⟩ := compatible (name, value)
    (ConditionalEquationExecution.lookup_assignment_member assignment name value found)
  rw [ordinary_lookup, found, read]
  rfl

/-- Agreement of two binding lists on a schema's names when the larger one keeps
the smaller one's lookups. -/
theorem apply_eq_of_preserved {small large : Bindings} {schema : Pattern} (shape : FirstOrder schema)
    (defined : Defined small schema.freeFvarNames)
    (preserved : ∀ name value, small.lookup name = some value → large.lookup name = some value) :
    applyBindings large schema = applyBindings small schema := by
  apply apply_eq_of_same_lookups shape
  intro name member
  obtain ⟨value, found⟩ := defined name member
  rw [found, preserved name value found]

mutual
 /-- A first-order match binds only the schema's names. -/
 theorem matchRel_names {schema target : Pattern} {bindings : Bindings} (shape : FirstOrder schema)
    (matched : MatchRel schema target bindings) : ∀ entry ∈ bindings, entry.1 ∈ schema.freeFvarNames := by
  cases shape with
  | metavariable name =>
    rw [LinearMatch.matchRel_fvar_shape matched]
    intro entry member
    rw [List.mem_singleton] at member
    subst member
    simp [Pattern.freeFvarNames]
  | constructor label arguments shapes =>
    cases matched with
    | apply argumentsMatched _ =>
      simpa only [Pattern.freeFvarNames] using matchArgsRel_names shapes argumentsMatched
 termination_by sizeOf schema

 theorem matchArgsRel_names {schemas targets : List Pattern} {bindings : Bindings}
    (shapes : ∀ schema ∈ schemas, FirstOrder schema) (matched : MatchArgsRel schemas targets bindings) :
    ∀ entry ∈ bindings, entry.1 ∈ schemas.flatMap Pattern.freeFvarNames := by
  cases schemas with
  | nil => cases matched; intro _ member; cases member
  | cons schema schemas =>
    cases matched with
    | cons first rest merged =>
      intro entry member
      simp only [List.flatMap_cons, List.mem_append]
      rcases List.mem_append.mp (merge_members merged member) with earlier | later
      · exact Or.inl (matchRel_names (shapes schema (by simp)) first entry earlier)
      · exact Or.inr (matchArgsRel_names (fun child member => shapes child (List.mem_cons_of_mem _ member))
          rest entry later)
 termination_by sizeOf schemas
end

/-- A typed first-order schema gives every name it captures a declared sort, so
its dependency list is empty. -/
theorem dependencies_of_typed {rule : RewriteRule} (unique : (rule.typeContext.map Prod.fst).Nodup)
    {environment : Bindings} {names : List String} (defined : Defined environment names)
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    (typed : CapturesTyped language free bound rule.typeContext environment) :
    ∀ name ∈ names, dependencies? (GeneralRuleBindingInference.inferredSpec rule) name = some [] := by
  intro name member
  obtain ⟨body, read⟩ := defined name member
  obtain ⟨_, declared, _⟩ := typed (name, body) (raw_lookup_member read)
  exact inferred_dependencies_of_lookup rule unique declared

/-! ## The canonical relation matcher on first-order arguments -/

theorem matchRelationArgs_nil_inv {seed extension : Bindings} {values : List Pattern}
    (member : extension ∈ matchRelationArgs seed [] values) : values = [] ∧ extension = [] := by
  cases values with
  | nil => simp only [matchRelationArgs, List.mem_singleton] at member; exact ⟨rfl, member⟩
  | cons _ _ => simp [matchRelationArgs] at member

theorem matchRelationArgs_cons_nil {seed : Bindings} {argument : Pattern} {arguments : List Pattern} :
    matchRelationArgs seed (argument :: arguments) [] = [] := by
  simp [matchRelationArgs]

theorem matchRelationArgs_cons_inv {seed extension : Bindings} {argument value : Pattern}
    {arguments values : List Pattern}
    (member : extension ∈ matchRelationArgs seed (argument :: arguments) (value :: values)) :
    ∃ head extended tail, head ∈ matchRelationArgument seed argument value ∧
      mergeBindings seed head = some extended ∧ tail ∈ matchRelationArgs extended arguments values ∧
      mergeBindings head tail = some extension := by
  simp only [matchRelationArgs, List.mem_flatMap] at member
  obtain ⟨head, headMember, rest⟩ := member
  cases merged : mergeBindings seed head with
  | none => simp [merged] at rest
  | some extended =>
    simp only [merged, List.mem_filterMap] at rest
    obtain ⟨tail, tailMember, combined⟩ := rest
    exact ⟨head, extended, tail, headMember, merged, tailMember, combined⟩

/-- One first-order argument either matches the value, or is a variable already
bound to it. -/
theorem matchRelationArgument_cases {seed head : Bindings} {argument value : Pattern}
    (shape : FirstOrder argument) (member : head ∈ matchRelationArgument seed argument value) :
    MatchRel argument value head ∨
      ∃ name, argument = .fvar name ∧ seed.lookup name = some value ∧ head = [] := by
  cases shape with
  | metavariable name =>
    unfold matchRelationArgument at member
    cases found : seed.lookup name with
    | none =>
      simp only [found, List.mem_singleton] at member
      subst member
      exact Or.inl .fvar
    | some existing =>
      simp only [found] at member
      split at member
      · rename_i same
        subst same
        exact Or.inr ⟨name, rfl, found, List.mem_singleton.mp member⟩
      · simp at member
  | constructor label arguments _ =>
    exact Or.inl (matchPattern_sound (by simpa only [matchRelationArgument] using member))

/-- **Soundness.** A binding list that keeps the seed's and the extension's
lookups instantiates every argument to its tuple value and defines its names. -/
theorem relationArgs_sound : ∀ {arguments values : List Pattern} {seed extension result : Bindings},
    (∀ argument ∈ arguments, FirstOrder argument) →
    extension ∈ matchRelationArgs seed arguments values →
    BindingsExtends seed result → BindingsExtends extension result →
    arguments.map (applyBindings result) = values ∧
      Defined result (arguments.flatMap Pattern.freeFvarNames)
  | [], values, seed, extension, result, _, member, _, _ => by
    obtain ⟨rfl, rfl⟩ := matchRelationArgs_nil_inv member
    exact ⟨rfl, (fun _ member => nomatch member)⟩
  | _ :: _, [], _, _, _, _, member, _, _ => by
    rw [matchRelationArgs_cons_nil] at member
    cases member
  | argument :: arguments, value :: values, seed, extension, result, shapes, member, seedExtends,
      extensionExtends => by
    obtain ⟨head, extended, tail, headMember, extendedMerged, tailMember, combined⟩ :=
      matchRelationArgs_cons_inv member
    have headExtends : BindingsExtends head result := fun name value found =>
      extensionExtends name value (mergeBindings_subsumed_left combined found)
    have tailExtends : BindingsExtends tail result := fun name value found =>
      extensionExtends name value (mergeBindings_subsumed_right combined found)
    obtain ⟨rest, restDefined⟩ := relationArgs_sound
      (fun child member => shapes child (List.mem_cons_of_mem _ member)) tailMember
      (extends_merge extendedMerged seedExtends headExtends) tailExtends
    have shape := shapes argument (by simp)
    have headSound : applyBindings result argument = value ∧
        Defined result argument.freeFvarNames := by
      rcases matchRelationArgument_cases shape headMember with matched | ⟨name, rfl, found, _⟩
      · refine ⟨matchRel_correct_of_extends matched shape.isMatchCorrect headExtends, ?_⟩
        intro name member
        obtain ⟨bound, read⟩ := raw_matching_defined shape matched name member
        exact ⟨bound, MatchBindingExtension.lookup_preserved headExtends read⟩
      · have read := MatchBindingExtension.lookup_preserved seedExtends found
        refine ⟨by rw [apply_variable, read]; rfl, ?_⟩
        intro queried member
        have same : queried = name := by simpa [Pattern.freeFvarNames] using member
        subst same
        exact ⟨value, read⟩
    refine ⟨by rw [List.map_cons, headSound.1, rest], ?_⟩
    intro name member
    rcases List.mem_append.mp (by simpa only [List.flatMap_cons] using member) with here | later
    · exact headSound.2 name here
    · exact restDefined name later

/-- The extension binds only argument names. -/
theorem relationArgs_names : ∀ {arguments values : List Pattern} {seed extension : Bindings},
    (∀ argument ∈ arguments, FirstOrder argument) →
    extension ∈ matchRelationArgs seed arguments values →
    ∀ entry ∈ extension, entry.1 ∈ arguments.flatMap Pattern.freeFvarNames
  | [], values, seed, extension, _, member => by
    obtain ⟨_, rfl⟩ := matchRelationArgs_nil_inv member
    intro _ inside
    cases inside
  | _ :: _, [], _, _, _, member => by
    rw [matchRelationArgs_cons_nil] at member
    cases member
  | argument :: arguments, value :: values, seed, extension, shapes, member => by
    obtain ⟨head, extended, tail, headMember, _, tailMember, combined⟩ :=
      matchRelationArgs_cons_inv member
    have rest := relationArgs_names
      (fun child member => shapes child (List.mem_cons_of_mem _ member)) tailMember
    have shape := shapes argument (by simp)
    intro entry inside
    simp only [List.flatMap_cons, List.mem_append]
    rcases List.mem_append.mp (merge_members combined inside) with fromHead | fromTail
    · left
      rcases matchRelationArgument_cases shape headMember with matched | ⟨_, _, _, rfl⟩
      · exact matchRel_names shape matched entry fromHead
      · cases fromHead
    · exact Or.inr (rest entry fromTail)

/-- **Typing.** Arguments typed by the declared sorts, matched against values of
those sorts, capture typed values. -/
theorem relationArgs_typed {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {context : List (String × TypeExpr)} (valid : language.validate = []) :
    ∀ {arguments values : List Pattern} {types : List TypeExpr} {seed extension : Bindings},
    (∀ argument ∈ arguments, FirstOrder argument) →
    extension ∈ matchRelationArgs seed arguments values →
    List.Forall₂ (HasType language (FreeTypeContext.ofList context) []) arguments types →
    GeneralPremise.ValuesTyped language free bound values types →
    CapturesTyped language free bound context extension
  | [], values, _, seed, extension, _, member, _, _ => by
    obtain ⟨_, rfl⟩ := matchRelationArgs_nil_inv member
    intro _ inside
    cases inside
  | _ :: _, [], _, _, _, _, member, _, _ => by
    rw [matchRelationArgs_cons_nil] at member
    cases member
  | argument :: arguments, value :: values, _, seed, extension, shapes, member, schemasTyped,
      valuesTyped => by
    obtain ⟨head, extended, tail, headMember, _, tailMember, combined⟩ :=
      matchRelationArgs_cons_inv member
    have shape := shapes argument (by simp)
    cases schemasTyped with
    | cons schemaTyped schemasTyped =>
    cases valuesTyped with
    | cons valueTyped valuesTyped =>
    have rest := relationArgs_typed valid
      (fun child member => shapes child (List.mem_cons_of_mem _ member)) tailMember schemasTyped valuesTyped
    have headTyped : CapturesTyped language free bound context head := by
      rcases matchRelationArgument_cases shape headMember with matched | ⟨_, _, _, rfl⟩
      · exact matching_captures_typed valid shape matched schemaTyped valueTyped.1 valueTyped.2.1
          valueTyped.2.2.1
      · intro _ inside
        cases inside
    exact capturesTyped_merge headTyped rest combined

/-- **Instances.** Against the instance of a substitution that defines every
argument name, the canonical matcher finds an extension compatible with that
substitution; with the seed it covers every argument name. -/
theorem relationArgs_instance (environment : Bindings) :
    ∀ {arguments : List Pattern} {seed : Bindings},
    (∀ argument ∈ arguments, FirstOrder argument) →
    Defined environment (arguments.flatMap Pattern.freeFvarNames) →
    Compatible environment seed → (seed.map Prod.fst).Nodup →
    ∃ extension ∈ matchRelationArgs seed arguments (arguments.map (applyBindings environment)),
      Compatible environment extension ∧ (extension.map Prod.fst).Nodup ∧
      (∀ entry ∈ extension, entry.1 ∈ arguments.flatMap Pattern.freeFvarNames) ∧
      ∀ name ∈ arguments.flatMap Pattern.freeFvarNames,
        name ∈ seed.map Prod.fst ∨ name ∈ extension.map Prod.fst
  | [], seed, _, _, _, _ =>
    ⟨[], RelationQueryAdmission.matchRelationArgs_nil seed, (fun _ member => nomatch member), by simp,
      (fun _ member => nomatch member), (fun _ member => nomatch member)⟩
  | argument :: arguments, seed, shapes, defined, compatible, unique => by
    have shape := shapes argument (by simp)
    have headDefined : Defined environment argument.freeFvarNames := fun name member =>
      defined name (List.mem_flatMap.mpr ⟨argument, List.mem_cons_self .., member⟩)
    obtain ⟨head, headMember, headCompatible, headUnique, headNames, headCovers⟩ :
        ∃ head ∈ matchRelationArgument seed argument (applyBindings environment argument),
          Compatible environment head ∧ (head.map Prod.fst).Nodup ∧
          (∀ entry ∈ head, entry.1 ∈ argument.freeFvarNames) ∧
          ∀ name ∈ argument.freeFvarNames, name ∈ seed.map Prod.fst ∨ name ∈ head.map Prod.fst := by
      cases shape with
      | metavariable name =>
        obtain ⟨value, found⟩ := headDefined name (by simp [Pattern.freeFvarNames])
        have applied : applyBindings environment (.fvar name) = value := by
          rw [apply_variable, found]
          rfl
        rw [applied]
        cases seedFound : seed.lookup name with
        | some existing =>
          have inSeed : name ∈ seed.map Prod.fst :=
            List.mem_map.mpr ⟨(name, existing), raw_lookup_member seedFound, rfl⟩
          have same : existing = value := by
            have read := compatible_lookup compatible inSeed
            rw [seedFound, found] at read
            exact Option.some.inj read
          subst same
          refine ⟨[], RelationQueryAdmission.matchRelationArgument_bound_self seedFound,
            (fun _ member => nomatch member), by simp, (fun _ member => nomatch member), ?_⟩
          intro queried member
          have sameName : queried = name := by simpa [Pattern.freeFvarNames] using member
          subst sameName
          exact Or.inl inSeed
        | none =>
          refine ⟨[(name, value)], RelationQueryAdmission.matchRelationArgument_unbound seedFound,
            ?_, by simp, ?_, ?_⟩
          · intro entry member
            cases List.mem_singleton.mp member
            exact found
          · intro entry member
            cases List.mem_singleton.mp member
            simp [Pattern.freeFvarNames]
          · intro queried member
            have sameName : queried = name := by simpa [Pattern.freeFvarNames] using member
            subst sameName
            exact Or.inr (by simp)
      | constructor label children childShapes =>
        obtain ⟨bindings, matched, bindingsCompatible, bindingsUnique, sameNames⟩ :=
          match_instance environment (.constructor label children childShapes) headDefined
        refine ⟨bindings, by simpa only [matchRelationArgument] using matchRel_complete matched,
          bindingsCompatible, bindingsUnique, ?_, ?_⟩
        · intro entry member
          exact (sameNames entry.1).mp (List.mem_map_of_mem member)
        · intro name member
          exact Or.inr ((sameNames name).mpr member)
    obtain ⟨extended, extendedMerged, extendedCompatible, extendedUnique, extendedNames⟩ :=
      merge_compatible environment seed head compatible headCompatible unique
    obtain ⟨tail, tailMember, tailCompatible, _, tailNames, tailCovers⟩ :=
      relationArgs_instance environment (fun child member => shapes child (List.mem_cons_of_mem _ member))
        (fun name member => defined name (by
          rw [List.flatMap_cons]
          exact List.mem_append_right _ member))
        extendedCompatible extendedUnique
    obtain ⟨combined, combinedMerged, combinedCompatible, combinedUnique, combinedNames⟩ :=
      merge_compatible environment head tail headCompatible tailCompatible headUnique
    refine ⟨combined, RelationQueryAdmission.matchRelationArgs_cons headMember extendedMerged tailMember
      combinedMerged, combinedCompatible, combinedUnique, ?_, ?_⟩
    · intro entry member
      rw [List.flatMap_cons, List.mem_append]
      rcases (combinedNames entry.1).mp (List.mem_map_of_mem member) with fromHead | fromTail
      · obtain ⟨headEntry, headEntryMember, key⟩ := List.mem_map.mp fromHead
        exact Or.inl (key ▸ headNames headEntry headEntryMember)
      · obtain ⟨tailEntry, tailEntryMember, key⟩ := List.mem_map.mp fromTail
        exact Or.inr (key ▸ tailNames tailEntry tailEntryMember)
    · intro name member
      rw [List.flatMap_cons, List.mem_append] at member
      rcases member with here | later
      · rcases headCovers name here with inSeed | inHead
        · exact Or.inl inSeed
        · exact Or.inr ((combinedNames name).mpr (Or.inl inHead))
      · rcases tailCovers name later with inExtended | inTail
        · rcases (extendedNames name).mp inExtended with inSeed | inHead
          · exact Or.inl inSeed
          · exact Or.inr ((combinedNames name).mpr (Or.inl inHead))
        · exact Or.inr ((combinedNames name).mpr (Or.inr inTail))

/-- The builtin relation `eq` is the only relation the canonical engine answers
without its relation environment. -/
theorem builtinRelationTuples_eq_nil {language : LanguageDef} {relation : String}
    (distinct : relation ≠ "eq") (arguments : List Pattern) :
    Engine.builtinRelationTuples language relation arguments = [] := by
  unfold Engine.builtinRelationTuples
  split
  · exact absurd rfl distinct
  · rfl

/-! ## Providers -/

/-- The relation environment and provider agree on tuple membership for every
declared relation. Ordering and multiplicity require a stronger interface. -/
def ReadsProvider (relEnv : Engine.RelationEnv) (provider : GeneralPremise.ProviderSnapshot) : Prop :=
  ∀ signature ∈ provider.signatures, ∀ arguments tuple,
    tuple ∈ relEnv.tuples signature.relation arguments ↔
      ∃ row ∈ provider.rows, row.relation = signature.relation ∧ row.values = tuple

/-- A provider without declared relations is read by every relation environment. -/
theorem ReadsProvider.empty (relEnv : Engine.RelationEnv) : ReadsProvider relEnv { signatures := [], rows := [] } :=
  (fun _ member => nomatch member)

/-- The relation environment of a provider: each relation answers with its rows. -/
def providerRelEnv (provider : GeneralPremise.ProviderSnapshot) : Engine.RelationEnv where
  tuples relation _ := provider.rows.filterMap fun row =>
    if row.relation = relation then some row.values else none

theorem providerRelEnv_reads (provider : GeneralPremise.ProviderSnapshot) :
    ReadsProvider (providerRelEnv provider) provider := by
  intro signature _ arguments tuple
  simp only [providerRelEnv, List.mem_filterMap]
  constructor
  · rintro ⟨row, member, selected⟩
    by_cases same : row.relation = signature.relation
    · rw [if_pos same] at selected
      exact ⟨row, member, same, Option.some.inj selected⟩
    · rw [if_neg same] at selected
      cases selected
  · rintro ⟨row, member, same, rfl⟩
    exact ⟨row, member, by rw [if_pos same]⟩

/-! ## Moded arguments in the general semantics -/

theorem queryInputNames_input (argument : Pattern) (arguments : List Pattern) (modes : List RelationArgMode) :
    GeneralPremise.queryInputNames (argument :: arguments) (.input :: modes) =
      argument.freeFvarNames ++ GeneralPremise.queryInputNames arguments modes := rfl

theorem queryInputNames_output (argument : Pattern) (arguments : List Pattern) (modes : List RelationArgMode) :
    GeneralPremise.queryInputNames (argument :: arguments) (.output :: modes) =
      GeneralPremise.queryInputNames arguments modes := rfl

theorem queryOutputNames_input (argument : Pattern) (arguments : List Pattern) (modes : List RelationArgMode) :
    GeneralPremise.queryOutputNames (argument :: arguments) (.input :: modes) =
      GeneralPremise.queryOutputNames arguments modes := rfl

theorem queryOutputNames_output (argument : Pattern) (arguments : List Pattern) (modes : List RelationArgMode) :
    GeneralPremise.queryOutputNames (argument :: arguments) (.output :: modes) =
      argument.freeFvarNames ++ GeneralPremise.queryOutputNames arguments modes := rfl

/-- Every argument name is an input or an output name. -/
theorem query_names_cover : ∀ {arguments : List Pattern} {modes : List RelationArgMode},
    arguments.length = modes.length → ∀ name ∈ arguments.flatMap Pattern.freeFvarNames,
      name ∈ GeneralPremise.queryInputNames arguments modes ∨
        name ∈ GeneralPremise.queryOutputNames arguments modes
  | [], _, _, _, member => by cases member
  | _ :: _, [], lengths, _, _ => by simp at lengths
  | argument :: arguments, mode :: modes, lengths, name, member => by
    rw [List.flatMap_cons, List.mem_append] at member
    have rest := query_names_cover (arguments := arguments) (modes := modes) (by simpa using lengths) name
    cases mode with
    | input =>
      rw [queryInputNames_input, queryOutputNames_input, List.mem_append]
      rcases member with here | later
      · exact Or.inl (Or.inl here)
      · rcases rest later with input | output
        · exact Or.inl (Or.inr input)
        · exact Or.inr output
    | output =>
      rw [queryInputNames_output, queryOutputNames_output, List.mem_append]
      rcases member with here | later
      · exact Or.inr (Or.inl here)
      · rcases rest later with input | output
        · exact Or.inl input
        · exact Or.inr (Or.inr output)

/-- Output names are argument names. -/
theorem queryOutputNames_subset : ∀ {arguments : List Pattern} {modes : List RelationArgMode}
    {name : String}, name ∈ GeneralPremise.queryOutputNames arguments modes →
      name ∈ arguments.flatMap Pattern.freeFvarNames
  | [], _, _, member => by cases member
  | _ :: _, [], _, member => by cases member
  | argument :: arguments, mode :: modes, name, member => by
    rw [List.flatMap_cons, List.mem_append]
    cases mode with
    | input =>
      rw [queryOutputNames_input] at member
      exact Or.inr (queryOutputNames_subset member)
    | output =>
      rw [queryOutputNames_output, List.mem_append] at member
      rcases member with here | later
      · exact Or.inl here
      · exact Or.inr (queryOutputNames_subset later)

/-- Under a later root-valued assignment, the arguments of a traced query read
back as the row values. -/
theorem tracedArguments_readout {context : GeneralPremise.Context}
    (zero : context.spec = GeneralRuleBindingInference.inferredSpec context.rule)
    {chosen : Assignment} (roots : GeneralPremise.RootValues context.bound.length chosen)
    {index : Nat} {initial final : Assignment} {schemas values : List Pattern}
    {modes : List RelationArgMode} {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : GeneralPremise.TracedArgumentsHold context index initial schemas values modes final origins) :
    (∀ schema ∈ schemas, FirstOrder schema) → GeneralScopedMatch.Extends final chosen →
      schemas.map (applyBindings (ordinary chosen)) = values := by
  induction held with
  | nil => intro _ _; rfl
  | input instantiated rest inductionHypothesis =>
    intro shapes later
    have shape := shapes _ (List.mem_cons_self ..)
    rw [zero] at instantiated
    have initialLater : GeneralScopedMatch.Extends _ chosen :=
      fun name value found => later name value (rest.readout.extension name value found)
    rw [List.map_cons, readout_chosen (operation := Substitution.instantiateBVar) shape initialLater roots
      instantiated,
      inductionHypothesis (fun child member => shapes child (List.mem_cons_of_mem _ member)) later]
  | output matched rest inductionHypothesis =>
    intro shapes later
    have shape := shapes _ (List.mem_cons_self ..)
    have matching := matched.matching
    rw [zero] at matching
    have middleLater : GeneralScopedMatch.Extends _ chosen :=
      fun name value found => later name value (rest.readout.extension name value found)
    rw [List.map_cons, matching_reconstructs shape matching middleLater roots,
      inductionHypothesis (fun child member => shapes child (List.mem_cons_of_mem _ member)) later]

/-- A traced query binds its output names. -/
theorem tracedArguments_bound {context : GeneralPremise.Context} {index : Nat}
    {initial final : Assignment} {schemas values : List Pattern} {modes : List RelationArgMode}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : GeneralPremise.TracedArgumentsHold context index initial schemas values modes final origins) :
    GeneralPremise.BoundNames final (GeneralPremise.queryOutputNames schemas modes) := by
  induction held with
  | nil => intro _ member; cases member
  | input _ _ inductionHypothesis =>
    rw [queryOutputNames_input]
    exact inductionHypothesis
  | output matched rest inductionHypothesis =>
    rw [queryOutputNames_output]
    intro name member
    rcases List.mem_append.mp member with here | later
    · obtain ⟨value, found⟩ := GeneralPremise.matching_bound_names matched.matching name here
      exact ⟨value, rest.readout.extension name value found⟩
    · exact inductionHypothesis name later

theorem sitePattern_query {rule : RewriteRule} {index position : Nat} {relation : String}
    {arguments : List Pattern} {schema : Pattern}
    (declared : rule.premises[index]? = some (.relationQuery relation arguments))
    (selected : arguments[position]? = some schema) :
    sitePattern? rule (.premise index 0 position) = some schema := by
  simp [sitePattern?, declared, quantifiedBody?, selected]

/-- Moded arguments reconstruct at their actual authored sites, including
arbitrary quantifier depth. The location hypotheses read the real rule tree. -/
theorem tracedArguments_construct_at {language : LanguageDef} {free : FreeTypeContext}
    {ruleIndex premiseIndex quantifierDepth : Nat} {rule : RewriteRule} {bound : List TypeExpr}
    (unique : (rule.typeContext.map Prod.fst).Nodup) {arguments : List Pattern}
    (locations : ∀ position schema, arguments[position]? = some schema →
      sitePattern? rule (.premise premiseIndex quantifierDepth position) = some schema)
    {environment : Bindings} (typed : CapturesTyped language free bound rule.typeContext environment) :
    ∀ (pending : List Pattern) (modes : List RelationArgMode) (offset : Nat) {assignment : Assignment},
      (∀ position schema, pending[position]? = some schema → arguments[offset + position]? = some schema) →
      (∀ schema ∈ pending, FirstOrder schema) →
      pending.length = modes.length →
      Defined environment (pending.flatMap Pattern.freeFvarNames) →
      GeneralPremise.BoundNames assignment (GeneralPremise.queryInputNames pending modes) →
      ScopedCompatible bound.length environment assignment →
      ∃ final origins, GeneralPremise.TracedArgumentsHold
          ⟨ruleIndex, rule, GeneralRuleBindingInference.inferredSpec rule, bound, premiseIndex, quantifierDepth⟩
          offset assignment pending (pending.map (applyBindings environment)) modes final origins ∧
        ScopedCompatible bound.length environment final ∧
        GeneralPremise.BoundNames final (GeneralPremise.queryOutputNames pending modes) ∧
        GeneralScopedMatch.Extends assignment final
  | [], [], _, assignment, _, _, _, _, _, compatible =>
    ⟨assignment, [], .nil, compatible, (fun _ member => nomatch member), GeneralScopedMatch.Extends.refl _⟩
  | [], _ :: _, _, _, _, _, lengths, _, _, _ => by simp at lengths
  | _ :: _, [], _, _, _, _, lengths, _, _, _ => by simp at lengths
  | schema :: pending, mode :: modes, offset, assignment, located, shapes, lengths, defined, inputs,
      compatible => by
    have shape := shapes schema (List.mem_cons_self ..)
    have here : arguments[offset]? = some schema := by simpa using located 0 schema rfl
    have locatedRest : ∀ position later, pending[position]? = some later →
        arguments[offset + 1 + position]? = some later := fun position later selected => by
      simpa [Nat.add_assoc, Nat.add_comm 1 position] using located (position + 1) later selected
    have coherent : NameCoherent rule (.premise premiseIndex quantifierDepth offset) [] schema := by
      intro suffix
      simp only [List.nil_append, locations offset schema here, Option.bind_some]
    have schemaDefined : Defined environment schema.freeFvarNames := fun name member =>
      defined name (List.mem_flatMap.mpr ⟨schema, List.mem_cons_self .., member⟩)
    have restDefined : Defined environment (pending.flatMap Pattern.freeFvarNames) := fun name member =>
      defined name (by
        rw [List.flatMap_cons]
        exact List.mem_append_right _ member)
    have restShapes : ∀ child ∈ pending, FirstOrder child := fun child member =>
      shapes child (List.mem_cons_of_mem _ member)
    have restLengths : pending.length = modes.length := by simpa using lengths
    cases mode with
    | input =>
      rw [queryInputNames_input] at inputs
      have schemaBound : GeneralPremise.BoundNames assignment schema.freeFvarNames := fun name member =>
        inputs name (List.mem_append_left _ member)
      have roots : GeneralPremise.RootValues bound.length assignment := compatible.rootValues typed
      obtain ⟨subject, read⟩ := instantiation_total (operation := Substitution.instantiateBVar) shape
        coherent schemaBound roots (dependencies_of_typed unique schemaDefined typed)
      have same : subject = applyBindings environment schema :=
        (instantiation_readout shape roots read).symm.trans (compatible_apply_eq compatible shape schemaBound)
      subst same
      obtain ⟨final, origins, held, finalCompatible, finalBound, finalExtends⟩ :=
        tracedArguments_construct_at unique locations typed pending modes (offset + 1) locatedRest restShapes
          restLengths restDefined (fun name member => inputs name (List.mem_append_right _ member))
          compatible
      refine ⟨final, (offset, []) :: origins, .input read held, finalCompatible, ?_, finalExtends⟩
      rw [queryOutputNames_input]
      exact finalBound
    | output =>
      rw [queryInputNames_output] at inputs
      obtain ⟨next, matched, nextCompatible⟩ := scoped_instance (initial := assignment) shape coherent
        schemaDefined typed unique compatible
      obtain ⟨trace, traced⟩ := GeneralScopedMatchMachine.matches_trace matched
      obtain ⟨final, origins, held, finalCompatible, finalBound, finalExtends⟩ :=
        tracedArguments_construct_at unique locations typed pending modes (offset + 1) locatedRest restShapes
          restLengths restDefined
          (fun name member => let ⟨value, found⟩ := inputs name member
            ⟨value, matched.extends name value found⟩)
          nextCompatible
      refine ⟨final, (offset, trace) :: origins, .output traced held, finalCompatible, ?_,
        fun name value found => finalExtends name value (matched.extends name value found)⟩
      rw [queryOutputNames_output]
      intro name member
      rcases List.mem_append.mp member with fromSchema | later
      · obtain ⟨value, found⟩ := GeneralPremise.matching_bound_names matched name fromSchema
        exact ⟨value, finalExtends name value found⟩
      · exact finalBound name later


/-- **Construction.** Moded arguments whose instance under a typed environment is
a row are traced from any assignment compatible with that environment that binds
the input names. -/
theorem tracedArguments_construct {language : LanguageDef} {free : FreeTypeContext}
    {ruleIndex premiseIndex : Nat} {rule : RewriteRule} {bound : List TypeExpr}
    (unique : (rule.typeContext.map Prod.fst).Nodup) {relation : String} {arguments : List Pattern}
    (declared : rule.premises[premiseIndex]? = some (.relationQuery relation arguments))
    {environment : Bindings} (typed : CapturesTyped language free bound rule.typeContext environment) :
    ∀ (pending : List Pattern) (modes : List RelationArgMode) (offset : Nat) {assignment : Assignment},
      (∀ position schema, pending[position]? = some schema → arguments[offset + position]? = some schema) →
      (∀ schema ∈ pending, FirstOrder schema) →
      pending.length = modes.length →
      Defined environment (pending.flatMap Pattern.freeFvarNames) →
      GeneralPremise.BoundNames assignment (GeneralPremise.queryInputNames pending modes) →
      ScopedCompatible bound.length environment assignment →
      ∃ final origins, GeneralPremise.TracedArgumentsHold
          ⟨ruleIndex, rule, GeneralRuleBindingInference.inferredSpec rule, bound, premiseIndex, 0⟩
          offset assignment pending (pending.map (applyBindings environment)) modes final origins ∧
        ScopedCompatible bound.length environment final ∧
        GeneralPremise.BoundNames final (GeneralPremise.queryOutputNames pending modes) ∧
        GeneralScopedMatch.Extends assignment final := by
  intro pending modes offset assignment located shapes lengths defined inputs compatible
  exact tracedArguments_construct_at unique
    (fun position schema selected => sitePattern_query declared selected) typed
    pending modes offset located shapes lengths defined inputs compatible

#print axioms tracedArguments_construct_at
#print axioms tracedArguments_construct

theorem bindings_lookup_of_mem :
    ∀ {bindings : Bindings}, (bindings.map Prod.fst).Nodup →
      ∀ {entry : String × Pattern}, entry ∈ bindings → bindings.lookup entry.1 = some entry.2
  | [], _, _, member => nomatch member
  | head :: rest, unique, entry, member => by
    rw [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with rfl | later
    · simp [Bindings.lookup]
    · have distinct : (head.1 == entry.1) = false := by
        have outside : entry.1 ∈ rest.map Prod.fst := List.mem_map_of_mem later
        simpa using fun same : head.1 = entry.1 => unique.1 (same ▸ outside)
      have read := bindings_lookup_of_mem unique.2 later
      simpa [Bindings.lookup, List.find?_cons, distinct] using read

theorem mergeBindings_nodup :
    ∀ {first second combined : Bindings}, mergeBindings first second = some combined →
      (first.map Prod.fst).Nodup → (combined.map Prod.fst).Nodup
  | first, [], combined, merged, unique => by
    simp only [mergeBindings, List.foldlM_nil] at merged
    cases Option.some.inj merged
    exact unique
  | first, (name, value) :: rest, combined, merged, unique => by
    simp only [mergeBindings, List.foldlM_cons] at merged
    cases found : first.find? (fun entry => entry.1 == name) with
    | none =>
      simp only [found] at merged
      have fresh : name ∉ first.map Prod.fst := by
        intro member
        obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp member
        have tested := List.find?_eq_none.mp found entry entryMember
        simp [same] at tested
      exact mergeBindings_nodup (first := (name, value) :: first) merged
        (List.nodup_cons.mpr ⟨fresh, unique⟩)
    | some existing =>
      simp only [found] at merged
      split at merged
      · exact mergeBindings_nodup (first := first) merged unique
      · cases merged


#print axioms bindings_lookup_of_mem
#print axioms mergeBindings_nodup


mutual
/-- Every literal match has unique binding keys, for the complete pattern
syntax. Collection allocation and binder displays do not duplicate keys. -/
theorem matchRel_unique_names {schema target : Pattern} {bindings : Bindings}
    (matched : MatchRel schema target bindings) : (bindings.map Prod.fst).Nodup :=
  match matched with
  | .fvar => by simp
  | .bvar => by simp
  | .apply arguments _ => matchArgsRel_unique_names arguments
  | .lambda body => matchRel_unique_names body
  | .multiLambda body => matchRel_unique_names body
  | .collection _ elements => matchBagRel_unique_names elements
  | .vector elements => matchArgsRel_unique_names elements
  | .vectorRest elements merged => mergeBindings_nodup merged (matchArgsRel_unique_names elements)
  | .subst body _ merged => mergeBindings_nodup merged (matchRel_unique_names body)

theorem matchArgsRel_unique_names {schemas targets : List Pattern} {bindings : Bindings}
    (matched : MatchArgsRel schemas targets bindings) : (bindings.map Prod.fst).Nodup :=
  match matched with
  | .nil => by simp
  | .cons head _ merged => mergeBindings_nodup merged (matchRel_unique_names head)

theorem matchBagRel_unique_names {schemas targets : List Pattern} {bindings : Bindings}
    {rest : Option String} {kind : CollType}
    (matched : MatchBagRel schemas rest kind targets bindings) : (bindings.map Prod.fst).Nodup :=
  match matched with
  | .nilNoRest => by simp
  | .nilRest => by simp
  | .cons _ _ head _ merged => mergeBindings_nodup merged (matchRel_unique_names head)
end

#print axioms matchRel_unique_names
#print axioms matchArgsRel_unique_names
#print axioms matchBagRel_unique_names



/-- Literal binding application depends on the lookups of the schema's real
free names, including a collection-rest lookup. No collection order law is used. -/
theorem applyBindings_eq_of_lookup_agreement {first second : Bindings} (schema : Pattern)
    (same : ∀ name ∈ schema.freeFvarNames,first.lookup name = second.lookup name) :
    applyBindings first schema = applyBindings second schema := by
  have findSame : ∀ name,first.lookup name = second.lookup name →
      first.find? (fun entry => entry.1 == name) = second.find? (fun entry => entry.1 == name) := by
    intro name same
    cases left : first.find? (fun entry => entry.1 == name) with
    | none =>
      cases right : second.find? (fun entry => entry.1 == name) with
      | none => rfl
      | some entry => simp only [Bindings.lookup,left,right,Option.map_none,Option.map_some] at same; cases same
    | some firstEntry =>
      cases right : second.find? (fun entry => entry.1 == name) with
      | none => simp only [Bindings.lookup,left,right,Option.map_none,Option.map_some] at same; cases same
      | some secondEntry =>
        have firstKey : firstEntry.1 = name := beq_iff_eq.mp
          (List.find?_some (p := fun entry : String × Pattern => entry.1 == name) left)
        have secondKey : secondEntry.1 = name := beq_iff_eq.mp
          (List.find?_some (p := fun entry : String × Pattern => entry.1 == name) right)
        have bodies : firstEntry.2 = secondEntry.2 :=
          Option.some.inj (by simpa only [Bindings.lookup,left,right,Option.map_some] using same)
        exact congrArg some (Prod.ext (firstKey.trans secondKey.symm) bodies)
  induction schema using Pattern.inductionOn with
  | hfvar name => rw [apply_variable,apply_variable,same name (by simp [Pattern.freeFvarNames])]
  | hbvar => simp only [applyBindings]
  | happly label arguments ih =>
    simp only [applyBindings]
    apply congrArg (Pattern.apply label)
    apply List.map_congr_left
    intro child member
    exact ih child member (fun name occurs => same name (by
      simpa only [Pattern.freeFvarNames] using List.mem_flatMap.mpr ⟨child,member,occurs⟩))
  | hlambda name body ih =>
    simp only [Pattern.freeFvarNames] at same
    simpa only [applyBindings] using congrArg (Pattern.lambda name) (ih same)
  | hmultiLambda arity names body ih =>
    simp only [Pattern.freeFvarNames] at same
    simpa only [applyBindings] using congrArg (Pattern.multiLambda arity names) (ih same)
  | hsubst body replacement bodyIH replacementIH =>
    simp only [Pattern.freeFvarNames] at same
    simp only [applyBindings]
    rw [bodyIH (fun name member => same name (List.mem_append_left _ member)),
      replacementIH (fun name member => same name (List.mem_append_right _ member))]
  | hcollection kind schemas rest ih =>
    have children : schemas.map (applyBindings first) = schemas.map (applyBindings second) := by
      apply List.map_congr_left
      intro child member
      exact ih child member (fun name occurs => same name (by
        simp only [Pattern.freeFvarNames,List.mem_append]
        exact Or.inl (List.mem_flatMap.mpr ⟨child,member,occurs⟩)))
    cases rest with
    | none => simp only [applyBindings,children]
    | some name =>
      have restSame := findSame name (same name (by simp [Pattern.freeFvarNames]))
      simp only [applyBindings,children,restSame]

theorem binderFreeList_of_members {schemas : List Pattern}
    (shapes : ∀ schema ∈ schemas,binderFree schema = true) : binderFreeList schemas = true := by
  induction schemas with
  | nil => rfl
  | cons head tail ih =>
    exact Bool.and_eq_true_iff.mpr ⟨shapes head (List.mem_cons_self ..),
      ih (fun child member => shapes child (List.mem_cons_of_mem _ member))⟩

#print axioms applyBindings_eq_of_lookup_agreement
#print axioms binderFreeList_of_members

/-- An actual argument match is preserved when the relation matcher treats
an already-bound top-level variable as an exact value. Other schemas retain
the original ordinary relational witness, including collection selections. -/
theorem relationArgument_of_match {environment seed bindings : Bindings} {schema value : Pattern}
    (matched : MatchRel schema value bindings) (compatible : Compatible environment bindings)
    (names : SameNames bindings schema.freeFvarNames) (before : Compatible environment seed) :
    ∃ produced,produced ∈ matchRelationArgument seed schema value ∧
      Compatible environment produced ∧ (produced.map Prod.fst).Nodup ∧
      (∀ entry ∈ produced,entry.1 ∈ schema.freeFvarNames) ∧
      ∀ name ∈ schema.freeFvarNames,name ∈ seed.map Prod.fst ∨ name ∈ produced.map Prod.fst := by
  cases schema with
  | fvar name =>
    cases matched
    cases found : seed.lookup name with
    | none =>
      refine ⟨[(name,value)],RelationQueryAdmission.matchRelationArgument_unbound found,
        compatible,by simp,?_,?_⟩
      · intro entry member
        cases List.mem_singleton.mp member
        simp [Pattern.freeFvarNames]
      · intro key member
        exact Or.inr (by simpa only [Pattern.freeFvarNames,List.map_cons,List.map_nil] using member)
    | some existing =>
      have inSeed : (name,existing) ∈ seed := by
        unfold Bindings.lookup at found
        obtain ⟨entry,selected,same⟩ := Option.map_eq_some_iff.mp found
        have key : entry.1 = name := beq_iff_eq.mp
          (List.find?_some (p := fun entry : String × Pattern => entry.1 == name) selected)
        obtain ⟨keyName,body⟩ := entry
        dsimp only at key same
        subst keyName
        subst body
        exact List.mem_of_find?_eq_some selected
      have same : existing = value :=
        Option.some.inj ((before (name,existing) inSeed).symm.trans
          (compatible (name,value) (List.mem_singleton_self _)))
      subst existing
      refine ⟨[],RelationQueryAdmission.matchRelationArgument_bound_self found,
        by simp [Compatible],by simp,by simp,?_⟩
      intro key member
      have keySame : key = name := by simpa only [Pattern.freeFvarNames,List.mem_singleton] using member
      subst key
      exact Or.inl (List.mem_map_of_mem inSeed)
  | bvar | apply | lambda | multiLambda | subst | collection =>
    refine ⟨bindings,?_,compatible,matchRel_unique_names matched,?_,?_⟩
    · simpa only [matchRelationArgument] using matchRel_complete matched
    · intro entry member
      exact (names entry.1).mp (List.mem_map_of_mem member)
    · intro name member
      exact Or.inr ((names name).mpr member)

/-- Traced moded queries produce the engine's actual tuple matcher witness.
An output collection is matched in its retained row order; no substitution
reconstruction or equality with a sorted presentation is assumed. -/
theorem tracedArguments_relation {context : GeneralPremise.Context}
    {chosen : Assignment} (roots : GeneralPremise.RootValues context.bound.length chosen)
    {index : Nat} {initial final : Assignment} {schemas values : List Pattern}
    {modes : List RelationArgMode} {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : GeneralPremise.TracedArgumentsHold context index initial schemas values modes final origins)
    (shapes : binderFreeList schemas = true) (later : GeneralScopedMatch.Extends final chosen)
    {seed : Bindings} (before : Compatible (ordinary chosen) seed) (unique : (seed.map Prod.fst).Nodup) :
    ∃ extension,extension ∈ matchRelationArgs seed schemas values ∧
      Compatible (ordinary chosen) extension ∧ (extension.map Prod.fst).Nodup ∧
      (∀ entry ∈ extension,entry.1 ∈ schemas.flatMap Pattern.freeFvarNames) ∧
      ∀ name ∈ schemas.flatMap Pattern.freeFvarNames,
        name ∈ seed.map Prod.fst ∨ name ∈ extension.map Prod.fst := by
  induction held generalizing seed with
  | nil =>
    exact ⟨[],RelationQueryAdmission.matchRelationArgs_nil _,by simp [Compatible],by simp,
      by simp,by simp⟩
  | @input index initial final schema value schemas values modes origins read tail ih =>
    obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
    have initialLater : GeneralScopedMatch.Extends initial chosen :=
      fun key value found => later key value (tail.readout.extension key value found)
    obtain ⟨head,headRaw,headCompatible,_,headNames⟩ :=
      binderFree_instantiation_matching headShape initialLater roots read
    obtain ⟨produced,headMember,producedCompatible,producedUnique,producedNames,headCovers⟩ :=
      relationArgument_of_match headRaw headCompatible headNames before
    obtain ⟨extended,seedMerge,extendedCompatible,extendedUnique,extendedNames⟩ :=
      merge_compatible (ordinary chosen) seed produced before producedCompatible unique
    obtain ⟨rest,tailMember,tailCompatible,_,tailNames,tailCovers⟩ :=
      ih tailShapes later extendedCompatible extendedUnique
    obtain ⟨extension,combined,compatible,extensionUnique,names⟩ :=
      merge_compatible (ordinary chosen) produced rest producedCompatible tailCompatible producedUnique
    refine ⟨extension,RelationQueryAdmission.matchRelationArgs_cons headMember seedMerge tailMember combined,
      compatible,extensionUnique,?_,?_⟩
    · intro entry member
      simp only [List.flatMap_cons,List.mem_append]
      rcases List.mem_append.mp (merge_members combined member) with first | rest
      · exact Or.inl (producedNames entry first)
      · exact Or.inr (tailNames entry rest)
    · intro name member
      simp only [List.flatMap_cons,List.mem_append] at member
      rcases member with first | rest
      · rcases headCovers name first with earlier | produced
        · exact Or.inl earlier
        · exact Or.inr ((names name).mpr (Or.inl produced))
      · rcases tailCovers name rest with earlier | fromTail
        · rcases (extendedNames name).mp earlier with earlier | fromHead
          · exact Or.inl earlier
          · exact Or.inr ((names name).mpr (Or.inl fromHead))
        · exact Or.inr ((names name).mpr (Or.inr fromTail))
  | @output index initial middle final schema value schemas values modes trace origins matched tail ih =>
    obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
    have middleLater : GeneralScopedMatch.Extends middle chosen :=
      fun key value found => later key value (tail.readout.extension key value found)
    have matching := matched.matching
    obtain ⟨head,headRaw,headCompatible,_,headNames⟩ :=
      binderFree_matching_readback headShape matching middleLater roots
    obtain ⟨produced,headMember,producedCompatible,producedUnique,producedNames,headCovers⟩ :=
      relationArgument_of_match headRaw headCompatible headNames before
    obtain ⟨extended,seedMerge,extendedCompatible,extendedUnique,extendedNames⟩ :=
      merge_compatible (ordinary chosen) seed produced before producedCompatible unique
    obtain ⟨rest,tailMember,tailCompatible,_,tailNames,tailCovers⟩ :=
      ih tailShapes later extendedCompatible extendedUnique
    obtain ⟨extension,combined,compatible,extensionUnique,names⟩ :=
      merge_compatible (ordinary chosen) produced rest producedCompatible tailCompatible producedUnique
    refine ⟨extension,RelationQueryAdmission.matchRelationArgs_cons headMember seedMerge tailMember combined,
      compatible,extensionUnique,?_,?_⟩
    · intro entry member
      simp only [List.flatMap_cons,List.mem_append]
      rcases List.mem_append.mp (merge_members combined member) with first | rest
      · exact Or.inl (producedNames entry first)
      · exact Or.inr (tailNames entry rest)
    · intro name member
      simp only [List.flatMap_cons,List.mem_append] at member
      rcases member with first | rest
      · rcases headCovers name first with earlier | produced
        · exact Or.inl earlier
        · exact Or.inr ((names name).mpr (Or.inl produced))
      · rcases tailCovers name rest with earlier | fromTail
        · rcases (extendedNames name).mp earlier with earlier | fromHead
          · exact Or.inl earlier
          · exact Or.inr ((names name).mpr (Or.inl fromHead))
        · exact Or.inr ((names name).mpr (Or.inr fromTail))

#print axioms relationArgument_of_match
#print axioms tracedArguments_relation


/-! ## Actual recursive relation-row witnesses -/

/-- The reference relation matcher either uses the actual structural raw
match or reads a bound top-level variable as one exact value. -/
theorem matchRelationArgument_cases_recursive {seed extension : Bindings} {schema value : Pattern}
    (member : extension ∈ matchRelationArgument seed schema value) :
    MatchRel schema value extension ∨
      ∃ name,schema = .fvar name ∧ seed.lookup name = some value ∧ extension = [] := by
  cases schema with
  | fvar name =>
    cases found : seed.lookup name with
    | none =>
      simp only [matchRelationArgument,found,List.mem_singleton] at member
      subst extension
      exact Or.inl .fvar
    | some existing =>
      by_cases same : existing = value
      · subst existing
        simp only [matchRelationArgument,found,↓reduceIte,List.mem_singleton] at member
        exact Or.inr ⟨name,rfl,found,member⟩
      · simp only [matchRelationArgument,found,if_neg same,List.not_mem_nil] at member
  | bvar | apply | lambda | multiLambda | subst | collection =>
    exact Or.inl (matchPattern_sound (by simpa only [matchRelationArgument] using member))

/-- A successful actual tuple match has precisely the query's arity. -/
theorem matchRelationArgs_lengths : ∀ {arguments values : List Pattern} {seed extension : Bindings},
    extension ∈ matchRelationArgs seed arguments values → arguments.length = values.length
  | [],values,_,_,member => by obtain ⟨rfl,_⟩ := matchRelationArgs_nil_inv member; rfl
  | _::_,[],_,_,member => by rw [matchRelationArgs_cons_nil] at member; cases member
  | _::arguments,_::values,_,_,member => by
    obtain ⟨_,_,_,_,_,tailMember,_⟩ := matchRelationArgs_cons_inv member
    exact congrArg Nat.succ (matchRelationArgs_lengths tailMember)

#print axioms matchRelationArgs_lengths

/-- Recursive relation outputs retain every authored capture role, including
collection rests, when matched against actually typed provider values. -/
theorem relationArgs_typed_recursive {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {context : List (String × TypeExpr)} (valid : language.validate = [])
    (choices : CollectionChoiceDeterministic language) :
    ∀ {arguments values : List Pattern} {types : List TypeExpr} {seed extension : Bindings},
    binderFreeList arguments = true → extension ∈ matchRelationArgs seed arguments values →
    List.Forall₂ (Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType language (FreeTypeContext.ofList context) []) arguments types →
    GeneralPremise.ValuesTyped language free bound values types →
    CapturesTyped language free bound context extension
  | [], values, _, seed, extension, _, member, _, _ => by
    obtain ⟨_,rfl⟩ := matchRelationArgs_nil_inv member
    exact fun _ inside => False.elim (List.not_mem_nil inside)
  | _ :: _, [], _, _, _, _, member, _, _ => by
    rw [matchRelationArgs_cons_nil] at member
    cases member
  | argument :: arguments, value :: values, _, seed, extension, shapes, member, schemasTyped,valuesTyped => by
    obtain ⟨head,extended,tail,headMember,_,tailMember,combined⟩ := matchRelationArgs_cons_inv member
    obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
    cases schemasTyped with
    | cons schemaTyped schemasTyped =>
      cases valuesTyped with
      | cons valueTyped valuesTyped =>
        have rest := relationArgs_typed_recursive valid choices tailShapes tailMember schemasTyped valuesTyped
        have headTyped : CapturesTyped language free bound context head := by
          rcases matchRelationArgument_cases_recursive headMember with matched | ⟨_,_,_,rfl⟩
          · exact matching_recursive_captures_typed valid choices headShape matched schemaTyped valueTyped
          · exact fun _ inside => False.elim (List.not_mem_nil inside)
        exact capturesTyped_merge headTyped rest combined

/-- Structural argument matching introduces only names from those schemas,
independently of bag order, explicit substitutions or binder display metadata. -/
theorem relationArgs_names_recursive : ∀ {arguments values : List Pattern} {seed extension : Bindings},
    extension ∈ matchRelationArgs seed arguments values →
    ∀ entry ∈ extension,entry.1 ∈ arguments.flatMap Pattern.freeFvarNames
  | [], values, seed, extension, member => by
    obtain ⟨_,rfl⟩ := matchRelationArgs_nil_inv member
    exact fun _ inside => False.elim (List.not_mem_nil inside)
  | _ :: _, [], _, _, member => by
    rw [matchRelationArgs_cons_nil] at member
    cases member
  | argument :: arguments,value :: values,seed,extension,member => by
    obtain ⟨head,extended,tail,headMember,_,tailMember,combined⟩ := matchRelationArgs_cons_inv member
    have rest := relationArgs_names_recursive tailMember
    intro entry inside
    simp only [List.flatMap_cons,List.mem_append]
    rcases List.mem_append.mp (merge_members combined inside) with earlier | later
    · apply Or.inl
      rcases matchRelationArgument_cases_recursive headMember with matched | ⟨_,_,_,rfl⟩
      · exact (raw_matching_names_recursive matched entry.1).mp (List.mem_map_of_mem earlier)
      · cases earlier
    · exact Or.inr (rest entry later)

/-- Every schema name is retained either by the original seed or by the
actual extension. No reconstruction of an unordered tuple is assumed. -/
theorem relationArgs_covers_recursive : ∀ {arguments values : List Pattern} {seed extension : Bindings},
    extension ∈ matchRelationArgs seed arguments values →
    ∀ name ∈ arguments.flatMap Pattern.freeFvarNames,
      name ∈ seed.map Prod.fst ∨ name ∈ extension.map Prod.fst
  | [], _, _, _, _ => by intro _ member; cases member
  | _ :: _, [], _, _, member => by
    rw [matchRelationArgs_cons_nil] at member
    cases member
  | argument :: arguments,value :: values,seed,extension,member => by
    obtain ⟨head,extended,tail,headMember,firstMerged,tailMember,combined⟩ := matchRelationArgs_cons_inv member
    intro name present
    simp only [List.flatMap_cons,List.mem_append] at present
    rcases present with here | later
    · rcases matchRelationArgument_cases_recursive headMember with matched | ⟨key,rfl,found,_⟩
      · exact Or.inr ((mergeBindings_name_union combined name).mpr (Or.inl
          ((raw_matching_names_recursive matched name).mpr here)))
      · have same : name = key := by simpa only [Pattern.freeFvarNames,List.mem_singleton] using here
        subst name
        exact Or.inl ((lookup_some_iff_mem_names seed key).mp ⟨value,found⟩)
    · rcases relationArgs_covers_recursive tailMember name later with earlier | produced
      · rcases (mergeBindings_name_union firstMerged name).mp earlier with original | fromHead
        · exact Or.inl original
        · exact Or.inr ((mergeBindings_name_union combined name).mpr (Or.inl fromHead))
      · exact Or.inr ((mergeBindings_name_union combined name).mpr (Or.inr produced))

#print axioms matchRelationArgument_cases_recursive
#print axioms relationArgs_typed_recursive
#print axioms relationArgs_names_recursive
#print axioms relationArgs_covers_recursive


/-- An actual reference tuple reconstructs the retained moded continuation.
Outputs use their real recursive matching witness. Inputs keep the established
first-order literal-read boundary and the actual projection-site certificate;
no equality of unordered raw presentations is assumed. -/
theorem tracedArguments_construct_recursive {language : LanguageDef} {free : FreeTypeContext}
    (context : GeneralPremise.Context)
    (admitted : admittedFor context.rule context.spec = true)
    (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    {chosen : Bindings} (typed : CapturesTyped language free context.bound context.rule.typeContext chosen) :
    ∀ (pending : List Pattern) (modes : List RelationArgMode) (offset : Nat)
      {values : List Pattern} {assignment : Assignment} {seed extension : Bindings},
      binderFreeList pending = true → pending.length = modes.length →
      (∀ (position : Nat) (schema : Pattern),pending[position]? = some schema →
        sitePattern? context.rule (context.site (offset + position)) = some schema) →
      (∀ (position : Nat) (schema : Pattern),pending[position]? = some schema → modes[position]? = some RelationArgMode.input →
        FirstOrder schema) →
      (∀ (position : Nat) (schema : Pattern),pending[position]? = some schema → modes[position]? = some RelationArgMode.input →
        GeneralPremise.checkRootProjectionSchema context.rule context.spec
          (context.site (offset + position)) [] schema = true) →
      (∀ value ∈ values,isObjectPattern value = true ∧ value.isWellScopedAt context.bound.length = true) →
      extension ∈ matchRelationArgs seed pending values →
      BindingsExtends seed chosen → BindingsExtends extension chosen →
      GeneralPremise.BoundNames assignment (GeneralPremise.queryInputNames pending modes) →
      ScopedCompatible context.bound.length chosen assignment →
      ∃ final origins,GeneralPremise.TracedArgumentsHold context offset assignment pending values modes final origins ∧
        ScopedCompatible context.bound.length chosen final ∧
        GeneralPremise.BoundNames final (GeneralPremise.queryOutputNames pending modes) ∧
        GeneralScopedMatch.Extends assignment final
  | [],[],_,values,assignment,seed,extension,_,_,_,_,_,_,member,_,_,_,before => by
    obtain ⟨rfl,rfl⟩ := matchRelationArgs_nil_inv member
    exact ⟨assignment,[],.nil,before,(fun _ member => nomatch member),.refl _⟩
  | [],_::_,_,_,_,_,_,_,lengths,_,_,_,_,_,_,_,_,_ => by simp at lengths
  | _::_,[],_,_,_,_,_,_,lengths,_,_,_,_,_,_,_,_,_ => by simp at lengths
  | schema::pending,mode::modes,offset,values,assignment,seed,extension,
      shapes,lengths,locations,inputShapes,inputReady,valueShapes,member,seedPreserved,extensionPreserved,inputs,before => by
    cases values with
    | nil => rw [matchRelationArgs_cons_nil] at member; cases member
    | cons value values =>
      obtain ⟨head,extended,tail,headMember,firstMerged,tailMember,combined⟩ := matchRelationArgs_cons_inv member
      obtain ⟨headShape,tailShapes⟩ := Bool.and_eq_true_iff.mp shapes
      have headPreserved : BindingsExtends head chosen := fun name target found =>
        extensionPreserved name target (mergeBindings_subsumed_left combined found)
      have tailPreserved : BindingsExtends tail chosen := fun name target found =>
        extensionPreserved name target (mergeBindings_subsumed_right combined found)
      have nextSeedPreserved := extends_merge firstMerged seedPreserved headPreserved
      have tailLengths : pending.length = modes.length := by simpa only [List.length_cons,Nat.succ.injEq] using lengths
      have tailLocations : ∀ (position : Nat) (later : Pattern),pending[position]? = some later →
          sitePattern? context.rule (context.site (offset + 1 + position)) = some later := by
        intro position later selected
        simpa only [Nat.add_assoc,Nat.add_comm 1 position] using locations (position+1) later
          (by simpa using selected)
      have tailInputShapes : ∀ (position : Nat) (later : Pattern),pending[position]? = some later →
          modes[position]? = some RelationArgMode.input → FirstOrder later := by
        intro position later selected input
        exact inputShapes (position+1) later (by simpa using selected) (by simpa using input)
      have tailInputReady : ∀ (position : Nat) (later : Pattern),pending[position]? = some later → modes[position]? = some RelationArgMode.input →
          GeneralPremise.checkRootProjectionSchema context.rule context.spec
            (context.site (offset + 1 + position)) [] later = true := by
        intro position later selected input
        simpa only [Nat.add_assoc,Nat.add_comm 1 position] using inputReady (position+1) later
          (by simpa using selected) (by simpa using input)
      have tailValueShapes : ∀ later ∈ values,isObjectPattern later = true ∧
          later.isWellScopedAt context.bound.length = true :=
        fun later present => valueShapes later (List.mem_cons_of_mem _ present)
      cases mode with
      | input =>
        have inputShape : FirstOrder schema := inputShapes 0 schema rfl rfl
        have checked : GeneralPremise.checkRootProjectionSchema context.rule context.spec
            (context.site offset) [] schema = true := by
          simpa only [Nat.add_zero] using inputReady 0 schema rfl rfl
        rw [queryInputNames_input] at inputs
        have schemaBound : GeneralPremise.BoundNames assignment schema.freeFvarNames :=
          fun name present => inputs name (List.mem_append_left _ present)
        have roots := before.rootValues typed
        obtain ⟨actual,read⟩ := GeneralPremise.checkRootProjectionSchema_sound Substitution.instantiateBVar (depth := 0)
          checked roots schemaBound
        have rawValue : applyBindings chosen schema = value := by
          rcases matchRelationArgument_cases_recursive headMember with matched | ⟨name,rfl,found,_⟩
          · exact matchRel_correct_of_extends matched inputShape.isMatchCorrect headPreserved
          · have retained := MatchBindingExtension.lookup_preserved seedPreserved found
            simp only [apply_variable,retained,Option.getD_some]
        have same : actual = value :=
          ((binderFree_instantiation_readout inputShape.binderFree roots read).symm.trans
            (compatible_apply_eq before inputShape schemaBound)).trans rawValue
        rw [same] at read
        obtain ⟨final,origins,held,after,outputs,extended⟩ := tracedArguments_construct_recursive context admitted zero typed
          pending modes (offset+1) tailShapes tailLengths tailLocations tailInputShapes tailInputReady tailValueShapes
          tailMember nextSeedPreserved tailPreserved
          (fun name present => inputs name (List.mem_append_right _ present)) before
        exact ⟨final,(offset,[])::origins,.input read held,after,outputs,extended⟩
      | output =>
        rw [queryInputNames_output] at inputs
        obtain ⟨rawBindings,rawMatched,rawCompatible⟩ :
            ∃ rawBindings,MatchRel schema value rawBindings ∧ Compatible chosen rawBindings := by
          rcases matchRelationArgument_cases_recursive headMember with matched | ⟨name,rfl,found,_⟩
          · refine ⟨head,matched,?_⟩
            intro entry present
            exact MatchBindingExtension.lookup_preserved headPreserved
              (bindings_lookup_of_mem (matchRel_unique_names matched) present)
          · refine ⟨[(name,value)],.fvar,?_⟩
            intro entry present
            cases List.mem_singleton.mp present
            exact MatchBindingExtension.lookup_preserved seedPreserved found
        have dependencies : ∀ name ∈ schema.freeFvarNames,dependencies? context.spec name = some [] := by
          intro name present
          obtain ⟨body,found⟩ := raw_matching_defined_recursive rawMatched name present
          have retained := rawCompatible (name,body) (raw_lookup_member found)
          obtain ⟨expected,declared,_⟩ := typed (name,body) (raw_lookup_member retained)
          exact dependencies_empty_of_admitted admitted zero declared
        have coherent : NameCoherent context.rule (context.site offset) [] schema := by
          intro suffix
          simp only [List.nil_append,show sitePattern? context.rule (context.site offset) = some schema from by
            simpa only [Nat.add_zero] using locations 0 schema rfl,Option.bind_some]
        have target := valueShapes value (List.mem_cons_self ..)
        obtain ⟨next,matched,nextCompatible⟩ := binderFree_scoped_of_matchRel_admitted admitted headShape
          coherent dependencies rawMatched rawCompatible target.2 target.1 before
        obtain ⟨trace,traced⟩ := GeneralScopedMatchMachine.matches_trace matched
        obtain ⟨final,origins,held,after,outputs,extended⟩ := tracedArguments_construct_recursive context admitted zero typed
          pending modes (offset+1) tailShapes tailLengths tailLocations tailInputShapes tailInputReady tailValueShapes
          tailMember nextSeedPreserved tailPreserved
          (fun name present => let ⟨value,found⟩ := inputs name present
            ⟨value,matched.extends name value found⟩) nextCompatible
        refine ⟨final,(offset,trace)::origins,.output traced held,after,?_,matched.extends.trans extended⟩
        rw [queryOutputNames_output]
        intro name present
        rcases List.mem_append.mp present with here | later
        · obtain ⟨value,found⟩ := GeneralPremise.matching_bound_names matched name here
          exact ⟨value,extended name value found⟩
        · exact outputs name later

#print axioms tracedArguments_construct_recursive

end Mettapedia.OSLF.Framework.GeneralCanonicalAgreement
