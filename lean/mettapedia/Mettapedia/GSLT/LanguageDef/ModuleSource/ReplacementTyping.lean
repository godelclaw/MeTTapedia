import Mettapedia.GSLT.LanguageDef.ModuleSource.Elaborate
import Mettapedia.GSLT.LanguageDef.WellSortedFillInversion
import Mathlib.Data.List.Perm.Subperm

/-!
# Typed argument transport for actual module replacements

The executable replacement check uses the declaration-derived type and
binding representation at each selected parameter position. The proofs below
relate its successful name permutation to `argumentMap`, including the fact
that the map's out-of-range default is never used on a typed argument spine.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource

open Mettapedia.OSLF.MeTTaIL.Syntax WellSorted

theorem compatibleParameter_type {old new : TermParam}
    (checked : compatibleParameter? old new = true) : parameterType? old = parameterType? new := by
  unfold compatibleParameter? at checked
  simp only [Bool.and_eq_true, beq_iff_eq] at checked
  exact checked.2

theorem compatibleParameter_representation {old new : TermParam}
    (checked : compatibleParameter? old new = true) (argument : Pattern) :
    MatchesParameterRepresentation old argument ↔ MatchesParameterRepresentation new argument := by
  cases old <;> cases new <;> first
    | rfl
    | simp_all [compatibleParameter?, matchesParameterRepresentation_abstractionNamed_iff,
        matchesParameterRepresentation_multiAbstractionNamed_iff]

theorem checkReplacementTyping_category {old new : GrammarRule}
    (checked : checkReplacementTyping old new = true) : old.category = new.category := by
  unfold checkReplacementTyping at checked
  simp only [Bool.and_eq_true, beq_iff_eq] at checked
  exact checked.1

theorem checkReplacementTyping_named {old new : GrammarRule}
    (checked : checkReplacementTyping old new = true) (named : namedArguments? old new = true) :
    usesBareCollection? old = usesBareCollection? new ∧
      ∀ parameter ∈ new.params, ∃ previous,
        old.params[(old.params.map paramName).idxOf (paramName parameter)]? = some previous ∧
          compatibleParameter? previous parameter = true := by
  unfold checkReplacementTyping at checked
  simp only [named, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at checked
  refine ⟨checked.2.1, ?_⟩
  intro parameter member
  have accepted := List.all_eq_true.mp checked.2.2 parameter member
  cases selected : old.params[(old.params.map paramName).idxOf (paramName parameter)]? with
  | none => simp [selected] at accepted
  | some previous => exact ⟨previous, rfl, by simpa only [selected, Option.any_some] using accepted⟩

theorem namedArguments_parameter_occurrences {old new : GrammarRule}
    (named : namedArguments? old new = true) :
    (new.params.map paramName).Perm (old.params.map paramName) := by
  simp only [namedArguments?, Bool.and_eq_true, decide_eq_true_eq] at named
  have subset : new.params.map paramName ⊆ old.params.map paramName := by
    intro name member
    exact List.contains_iff_mem.mp (List.all_eq_true.mp named.1.2 name member)
  exact (List.subperm_of_subset named.2 subset).perm_of_length_le (Nat.le_of_eq named.1.1.symm)

private theorem recover_arguments (names : List String) (distinct : names.Nodup)
    (arguments : List Pattern) (arity : arguments.length = names.length) :
    (names.map fun name => (arguments[names.idxOf name]?).getD (.fvar name)) = arguments := by
  apply List.ext_getElem
  · simp only [List.length_map, arity]
  · intro index inNames inArguments
    simp only [List.getElem_map, distinct.idxOf_getElem]
    simp only [List.getElem?_eq_getElem inArguments, Option.getD_some]

/-- Named replacement is a permutation of actual argument occurrences,
even when several arguments have equal values or share one type. -/
theorem argumentMap_named_occurrences {old new : GrammarRule} {arguments : List Pattern}
    (named : namedArguments? old new = true) (arity : arguments.length = old.params.length)
    {map : List Pattern → List Pattern} (computed : argumentMap old new = some map) :
    (map arguments).Perm arguments := by
  have names := namedArguments_parameter_occurrences named
  have checked := named
  simp only [namedArguments?, Bool.and_eq_true, decide_eq_true_eq] at checked
  have distinct := names.nodup checked.2
  have actual : map = fun arguments => (new.params.map paramName).map fun name =>
      (arguments[(old.params.map paramName).idxOf name]?).getD (.fvar name) := by
    apply Option.some.inj
    simpa only [argumentMap, named, ↓reduceIte] using computed.symm
  rw [actual]
  have mapped := names.map (fun name =>
    (arguments[(old.params.map paramName).idxOf name]?).getD (.fvar name))
  rw [recover_arguments _ distinct arguments (by simpa using arity)] at mapped
  exact mapped

/-- The actual argument permutation preserves the whole typed spine,
including the required binder representation at each destination slot. -/
theorem argumentMap_named_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {old new : GrammarRule} {arguments : List Pattern}
    (checked : checkReplacementTyping old new = true) (named : namedArguments? old new = true)
    (typed : ArgumentsHaveTypes language free bound arguments old.params)
    {map : List Pattern → List Pattern} (computed : argumentMap old new = some map) :
    ArgumentsHaveTypes language free bound (map arguments) new.params := by
  have selected := (checkReplacementTyping_named checked named).2
  have actual : map = fun arguments => (new.params.map paramName).map fun name =>
      (arguments[(old.params.map paramName).idxOf name]?).getD (.fvar name) := by
    apply Option.some.inj
    simpa only [argumentMap, named, ↓reduceIte] using computed.symm
  rw [actual]
  dsimp only
  rw [List.map_map]
  change ArgumentsHaveTypes language free bound
    (new.params.map fun parameter =>
      (arguments[(old.params.map paramName).idxOf (paramName parameter)]?).getD (.fvar (paramName parameter)))
    new.params
  have build : ∀ parameters : List TermParam,
      (∀ parameter ∈ parameters, ∃ previous,
        old.params[(old.params.map paramName).idxOf (paramName parameter)]? = some previous ∧
          compatibleParameter? previous parameter = true) →
      ArgumentsHaveTypes language free bound
        (parameters.map fun parameter =>
          (arguments[(old.params.map paramName).idxOf (paramName parameter)]?).getD (.fvar (paramName parameter)))
        parameters := by
    intro parameters
    induction parameters with
    | nil => intro _; exact .nil
    | cons parameter parameters ih =>
      intro selected
      obtain ⟨previous, atParameter, compatible⟩ := selected parameter List.mem_cons_self
      obtain ⟨argument, expected, atArgument, previousType, represented, argumentTyped⟩ :=
        typed.argument_at atParameter
      have parameterType := (compatibleParameter_type compatible).symm.trans previousType
      simpa only [List.map_cons, atArgument, Option.getD_some] using
        ArgumentsHaveTypes.cons ((compatibleParameter_representation compatible argument).mp represented)
          parameterType argumentTyped (ih (fun p member => selected p (List.mem_cons_of_mem _ member)))
  exact build new.params selected

theorem checkReplacementTyping_packed {old new : GrammarRule} {name sort : String} {kind : CollType}
    (checked : checkReplacementTyping old new = true) (named : namedArguments? old new = false)
    (shape : new.params = [.simple name (.collection kind (.base sort))]) :
    old.category = new.category ∧ old.params.length = 2 ∧ old.category = sort ∧
      ∀ parameter ∈ old.params, ∃ parameterName, parameter = .simple parameterName (.base sort) := by
  unfold checkReplacementTyping at checked
  simp only [named, shape, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at checked
  refine ⟨checked.1, checked.2.1.1, checked.2.1.2, ?_⟩
  intro parameter member
  have accepted := List.all_eq_true.mp checked.2.2 parameter member
  cases parameter with
  | simple parameterName type =>
    cases type with
    | base actual =>
      have same : actual = sort := by simpa using accepted
      exact ⟨parameterName, same ▸ rfl⟩
    | arrow | multiBinder | collection => cases accepted
  | abstractionNamed | multiAbstractionNamed => cases accepted

private theorem homogeneous_arguments {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam} {type : TypeExpr}
    (typed : ArgumentsHaveTypes language free bound arguments parameters)
    (homogeneous : ∀ parameter ∈ parameters, ∃ name, parameter = .simple name type) :
    ElementsHaveType language free bound arguments type := by
  induction parameters generalizing arguments with
  | nil => cases typed; exact .nil bound type
  | cons parameter parameters ih =>
    obtain ⟨name, same⟩ := homogeneous parameter List.mem_cons_self
    subst parameter
    cases typed with
    | cons represented parameterTyped argumentTyped rest =>
      have expected := Option.some.inj parameterTyped
      exact .cons (expected.symm ▸ argumentTyped)
        (ih rest (fun p member => homogeneous p (List.mem_cons_of_mem _ member)))

/-- Binary collection packing preserves the declared element type in the
actual argument mapper. It does not identify the enclosing named constructor
with its bare representation; that remains a core-lowering comparison. -/
theorem argumentMap_packed_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {old new : GrammarRule} {arguments : List Pattern}
    {name sort : String} {kind : CollType}
    (checked : checkReplacementTyping old new = true) (named : namedArguments? old new = false)
    (shape : new.params = [.simple name (.collection kind (.base sort))])
    (typed : ArgumentsHaveTypes language free bound arguments old.params)
    {map : List Pattern → List Pattern} (computed : argumentMap old new = some map) :
    ArgumentsHaveTypes language free bound (map arguments) new.params := by
  have uniform := (checkReplacementTyping_packed checked named shape).2.2.2
  have elements := homogeneous_arguments typed uniform
  have actual : map = fun arguments => [.collection kind arguments none] := by
    apply Option.some.inj
    unfold argumentMap at computed
    simp only [named, Bool.false_eq_true, ↓reduceIte, shape] at computed
    split at computed
    · exact computed.symm
    · cases computed
  rw [actual, shape]
  exact .cons trivial rfl (.collection elements) .nil

/-- Every successful typed argument layout, either a name permutation or
homogeneous collection packing, transports the actual mapper's result. -/
theorem argumentMap_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {old new : GrammarRule} {arguments : List Pattern}
    (checked : checkReplacementTyping old new = true)
    (typed : ArgumentsHaveTypes language free bound arguments old.params)
    {map : List Pattern → List Pattern} (computed : argumentMap old new = some map) :
    ArgumentsHaveTypes language free bound (map arguments) new.params := by
  by_cases named : namedArguments? old new = true
  · exact argumentMap_named_typed checked named typed computed
  · have unnamed : namedArguments? old new = false := Bool.eq_false_iff.mpr named
    have packed := checked
    simp only [checkReplacementTyping, unnamed, Bool.false_eq_true, ↓reduceIte,
      Bool.and_eq_true] at packed
    have shape := packed.2
    split at shape
    · rename_i name kind sort shapeEq
      exact argumentMap_packed_typed checked unnamed shapeEq typed computed
    · cases shape

/-- Success of the real elaborator supplies the selected source declaration,
its actual argument map, and the executable typing-profile certificate. -/
theorem replaceRow_typing_readout (value : Value) (row : Replacement) {result : Value}
    (accepted : replaceRow value row = .ok result) :
    ∃ item old map,
      value.entries.find? (·.label == (.term, row.old)) = some item ∧
      item.body = .term old ∧ argumentMap old row.rule = some map ∧
      checkReplacementTyping old row.rule = true ∧ checkFaithful value old row.rule = .ok () := by
  cases found : value.entries.find? (·.label == (.term, row.old)) with
  | none => simp [replaceRow, found] at accepted
  | some item =>
    cases body : item.body with
    | term old =>
      cases mapped : argumentMap old row.rule with
      | none => simp [replaceRow, found, body, mapped] at accepted
      | some map =>
        by_cases checked : checkReplacementTyping old row.rule = true
        · cases faithful : checkFaithful value old row.rule with
          | error failure =>
            simp [replaceRow, found, body, mapped, checked, faithful, bind, Except.bind] at accepted
          | ok resultUnit =>
            cases resultUnit
            exact ⟨item, old, map, rfl, body, mapped, checked, faithful⟩
        · simp [replaceRow, found, body, mapped, checked, bind, Except.bind] at accepted
    | sort | equation | rewrite => simp [replaceRow, found, body] at accepted

/-- The successful authoring operation earns result-sort equality and typed
transport for its actual selected argument function. Whole-pattern transport
through constructor representation lowering is a separate comparison. -/
theorem replaceRow_arguments_typed (value : Value) (row : Replacement) {result : Value}
    (accepted : replaceRow value row = .ok result) :
    ∃ item old map,
      value.entries.find? (·.label == (.term, row.old)) = some item ∧ item.body = .term old ∧
      argumentMap old row.rule = some map ∧ old.category = row.rule.category ∧
      ∀ (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
        (arguments : List Pattern), ArgumentsHaveTypes language free bound arguments old.params →
          ArgumentsHaveTypes language free bound (map arguments) row.rule.params := by
  obtain ⟨item, old, map, found, body, computed, checked, _⟩ := replaceRow_typing_readout value row accepted
  exact ⟨item, old, map, found, body, computed, checkReplacementTyping_category checked,
    fun _ _ _ _ typed => argumentMap_typed checked typed computed⟩

/-- The existing structural algebra action changes exactly unit references.
Its presence and flattening flag are retained. -/
theorem renameUnitReferences_algebra (old new : String) (rule : GrammarRule) :
    (renameUnitReferences old new rule).algebra?.map (·.flatten) = rule.algebra?.map (·.flatten) ∧
      (renameUnitReferences old new rule).algebra?.bind (·.unit) =
        (rule.algebra?.bind (·.unit)).map (renameName old new) := by
  cases algebra : rule.algebra? <;>
    simp [renameUnitReferences, StructuralMorphism.mapCollectionAlgebra, algebra]

theorem replaceRow_rechecked_entries (value : Value) (row : Replacement) {result : Value}
    (accepted : replaceRow value row = .ok result) :
    ∃ map, recheck (replaceItems value.entries row map) = .ok result.entries := by
  obtain ⟨item, old, map, found, body, computed, checked, faithful⟩ :=
    replaceRow_typing_readout value row accepted
  cases rechecked : recheck (replaceItems value.entries row map) with
  | error failure =>
    simp [replaceRow, found, body, computed, checked, faithful, rechecked, bind, Except.bind] at accepted
  | ok entries =>
    have same := accepted
    simp [replaceRow, found, body, computed, checked, faithful, rechecked, bind, Except.bind] at same
    cases same
    exact ⟨map, rechecked⟩

private theorem recheck_retains_member {items checked : List Item}
    (accepted : recheck items = .ok checked) {item : Item} (member : item ∈ items) : item ∈ checked := by
  unfold recheck at accepted
  cases found : ModuleAlgebra.orderedCheck? items with
  | none => simp [found] at accepted
  | some result =>
    rw [found] at accepted
    have sameResult := Except.ok.inj accepted
    subst result
    have same := ModuleAlgebra.orderedCheck_toFinset items checked found
    apply List.mem_toFinset.mp
    rw [same]
    exact List.mem_toFinset.mpr member

/-- Every retained constructor of the successful producer follows the unit
symbol action, with the same declaration origin and label. Ordered rechecking
does not discard the transported declaration. -/
theorem replaceRow_retains_unit_transport (value : Value) (row : Replacement) {result : Value}
    (accepted : replaceRow value row = .ok result) {item : Item} {rule : GrammarRule}
    (member : item ∈ value.entries) (body : item.body = .term rule)
    (retained : item.label ≠ (.term, row.old)) :
    ∃ image ∈ result.entries, image.origin = item.origin ∧ image.label = item.label ∧
      image.body = .term (renameUnitReferences row.old row.rule.label rule) := by
  obtain ⟨map, checked⟩ := replaceRow_rechecked_entries value row accepted
  let image : Item := { item with body := .term (renameUnitReferences row.old row.rule.label rule) }
  have produced : image ∈ replaceItems value.entries row map := by
    apply List.mem_map.mpr
    refine ⟨item, member, ?_⟩
    simp [retained, body, replaceDecl, image]
  exact ⟨image, recheck_retains_member checked produced, rfl, rfl, rfl⟩

/-- A retained declaration naming the replaced unit names its replacement
after the real producer succeeds. The source origin and label still identify
the same declaration; the flattening choice is preserved. -/
theorem replaceRow_transports_named_unit (value : Value) (row : Replacement) {result : Value}
    (accepted : replaceRow value row = .ok result) {item : Item} {rule : GrammarRule}
    (member : item ∈ value.entries) (body : item.body = .term rule)
    (retained : item.label ≠ (.term, row.old))
    (unit : rule.algebra?.bind (·.unit) = some row.old) :
    ∃ image ∈ result.entries, ∃ target,
      image.origin = item.origin ∧ image.label = item.label ∧ image.body = .term target ∧
      target.algebra?.bind (·.unit) = some row.rule.label ∧
      target.algebra?.map (·.flatten) = rule.algebra?.map (·.flatten) := by
  obtain ⟨image, present, origin, label, mapped⟩ :=
    replaceRow_retains_unit_transport value row accepted member body retained
  have algebra := renameUnitReferences_algebra row.old row.rule.label rule
  refine ⟨image, present, renameUnitReferences row.old row.rule.label rule, origin, label, mapped, ?_, algebra.1⟩
  rw [algebra.2, unit]
  simp [renameName]

end Mettapedia.GSLT.LanguageDef.ModuleSource
