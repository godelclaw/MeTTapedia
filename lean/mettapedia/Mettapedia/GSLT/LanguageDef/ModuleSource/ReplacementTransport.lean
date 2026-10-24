import Mettapedia.GSLT.LanguageDef.ModuleSource.ReplacementTyping

/-!
# Whole-pattern typing transport for named constructor replacements

The action is the actual authoring traversal, including argument permutation
and unit-reference transport. Local signature facts suffice for all terms,
binders, explicit substitutions and bare collection carriers. Packing a binary
operation into a new collection representation is a separate case.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.ReplacementTransport

open Mettapedia.OSLF.MeTTaIL.Syntax WellSorted

theorem named_bare_iff {old new : GrammarRule}
    (checked : checkReplacementTyping old new = true) (named : namedArguments? old new = true) :
    UsesBareCollection new ↔ UsesBareCollection old := by
  have same := (checkReplacementTyping_named checked named).1
  rw [← usesBareCollection?_eq_true_iff, ← usesBareCollection?_eq_true_iff, same]

theorem named_bare_shape {old new : GrammarRule}
    (checked : checkReplacementTyping old new = true) (named : namedArguments? old new = true)
    {parameter : String} {kind : CollType} {element : TypeExpr}
    (shape : old.bareParams = [.simple parameter (.collection kind element)]) :
    ∃ name, new.bareParams = [.simple name (.collection kind element)] := by
  have oldShape := (GrammarRule.bareParams_cons_iff _ _ _).mp shape
  obtain ⟨name, newKind, newElement, newShape⟩ :=
    (named_bare_iff checked named).mpr ⟨parameter, kind, element, shape⟩
  have newParams := (GrammarRule.bareParams_cons_iff _ _ _).mp newShape
  obtain ⟨previous, selected, compatible⟩ :=
    (checkReplacementTyping_named checked named).2 (.simple name (.collection newKind newElement))
      (by rw [newParams.2]; exact List.mem_cons_self)
  have member := List.mem_of_getElem? selected
  rw [oldShape.2] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst previous
  have types := compatibleParameter_type compatible
  simp only [parameterType?, Option.some.injEq] at types
  cases TypeExpr.collection.inj types with
  | intro kindEq elementEq =>
    exact ⟨name, kindEq ▸ elementEq ▸ newShape⟩

theorem representation_preserved (old new : String) (map : List Pattern → List Pattern)
    (parameter : TermParam) (pattern : Pattern)
    (represented : MatchesParameterRepresentation parameter pattern) :
    MatchesParameterRepresentation parameter (renameConstructor old new map pattern) := by
  cases parameter with
  | simple => trivial
  | abstractionNamed binder name type =>
    obtain ⟨body, rfl⟩ := (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp represented
    exact (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mpr
      ⟨renameConstructor old new map body, by rw [renameConstructor]⟩
  | multiAbstractionNamed binders name type =>
    obtain ⟨arity, body, rfl⟩ := (matchesParameterRepresentation_multiAbstractionNamed_iff _ _ _ _).mp represented
    exact (matchesParameterRepresentation_multiAbstractionNamed_iff _ _ _ _).mpr
      ⟨arity, renameConstructor old new map body, by rw [renameConstructor]⟩

/-- Per-declaration membership and uniqueness, rather than a supplied
whole-term preservation theorem. The actual producer supplies these facts. -/
structure Signature (source target : LanguageDef) (old new : GrammarRule) : Prop where
  selected : old ∈ source.terms
  unique : ∀ rule ∈ source.terms, rule.label = old.label → rule = old
  replaced : renameUnitReferences old.label new.label new ∈ target.terms
  retained : ∀ rule ∈ source.terms, rule.label ≠ old.label →
    renameUnitReferences old.label new.label rule ∈ target.terms

variable {source target : LanguageDef} {old new : GrammarRule}
    {map : List Pattern → List Pattern}

mutual
  theorem typed (signature : Signature source target old new)
      (checked : checkReplacementTyping old new = true) (named : namedArguments? old new = true)
      (computed : argumentMap old new = some map) {free : FreeTypeContext} (bound : List TypeExpr) {pattern : Pattern} {type : TypeExpr}
      (original : HasType source free bound pattern type) :
      HasType target free bound (renameConstructor old.label new.label map pattern) type := by
    cases original with
    | bvar found => simpa only [renameConstructor] using (HasType.bvar (language := target) found)
    | fvar found => simpa only [renameConstructor] using (HasType.fvar (language := target) found)
    | @constructor bound rule arguments member notBare argumentsTyped =>
      have mapped := arguments_typed signature checked named computed bound argumentsTyped
      by_cases selected : rule.label = old.label
      · have same := signature.unique rule member selected
        subst rule
        have newNotBare : ¬ UsesBareCollection new := fun bare =>
          notBare ((named_bare_iff checked named).mp bare)
        have packed := argumentMap_typed checked mapped computed
        have result : HasType target free bound
            (.apply new.label (map (arguments.map (renameConstructor old.label new.label map))))
            (.base new.category) :=
          .constructor (rule := renameUnitReferences old.label new.label new) signature.replaced newNotBare packed
        simpa only [renameConstructor, ↓reduceIte, checkReplacementTyping_category checked] using result
      · have result : HasType target free bound
            (.apply rule.label (arguments.map (renameConstructor old.label new.label map)))
            (.base rule.category) :=
          .constructor (rule := renameUnitReferences old.label new.label rule) (signature.retained rule member selected) notBare mapped
        simpa only [renameConstructor, if_neg selected] using result
    | @lambda bound binder body domain codomain bodyTyped =>
      simpa only [renameConstructor] using
        (HasType.lambda (binder := binder) (typed signature checked named computed (domain :: bound) bodyTyped))
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
      simpa only [renameConstructor] using
        (HasType.multiLambda (binders := binders) (typed signature checked named computed (List.replicate arity domain ++ bound) bodyTyped))
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
      simpa only [renameConstructor] using
        (HasType.subst (typed signature checked named computed (domain :: bound) bodyTyped) (typed signature checked named computed bound replacementTyped))
    | @collection bound kind elements rest elementType elementsTyped =>
      simpa only [renameConstructor] using
        (HasType.collection (collectionType := kind) (rest := rest) (elements_typed signature checked named computed bound elementsTyped))
    | @collectionConstructor bound rule parameter kind elements rest element member shape elementsTyped =>
      have mapped := elements_typed signature checked named computed bound elementsTyped
      by_cases selected : rule.label = old.label
      · have same := signature.unique rule member selected
        subst rule
        obtain ⟨name, newShape⟩ := named_bare_shape checked named shape
        have result : HasType target free bound
            (.collection kind (elements.map (renameConstructor old.label new.label map)) rest)
            (.base new.category) := .collectionConstructor (rule := renameUnitReferences old.label new.label new) signature.replaced newShape mapped
        simpa only [renameConstructor, checkReplacementTyping_category checked] using result
      · simpa only [renameConstructor, renameUnitReferences] using
          (HasType.collectionConstructor (rule := renameUnitReferences old.label new.label rule)
            (rest := rest) (signature.retained rule member selected) shape mapped)
  termination_by sizeOf pattern

  theorem arguments_typed (signature : Signature source target old new)
      (checked : checkReplacementTyping old new = true) (named : namedArguments? old new = true)
      (computed : argumentMap old new = some map) {free : FreeTypeContext} (bound : List TypeExpr)
      {arguments : List Pattern} {parameters : List TermParam}
      (original : ArgumentsHaveTypes source free bound arguments parameters) :
      ArgumentsHaveTypes target free bound
        (arguments.map (renameConstructor old.label new.label map)) parameters := by
    cases original with
    | nil => exact .nil
    | cons represented parameterType argument rest =>
      exact .cons (representation_preserved _ _ _ _ _ represented) parameterType
        (typed signature checked named computed bound argument)
        (arguments_typed signature checked named computed bound rest)
  termination_by sizeOf arguments

  theorem elements_typed (signature : Signature source target old new)
      (checked : checkReplacementTyping old new = true) (named : namedArguments? old new = true)
      (computed : argumentMap old new = some map) {free : FreeTypeContext} (bound : List TypeExpr)
      {elements : List Pattern} {type : TypeExpr}
      (original : ElementsHaveType source free bound elements type) :
      ElementsHaveType target free bound
        (elements.map (renameConstructor old.label new.label map)) type := by
    cases original with
    | nil => exact .nil _ _
    | cons element rest =>
      exact .cons (typed signature checked named computed bound element)
        (elements_typed signature checked named computed bound rest)
  termination_by sizeOf elements
end

/-- Declaration keys agree with their term bodies. This is a local source
well-formedness condition, independent of any term-transport conclusion. -/
def TermLabelsCoherent (value : Value) : Prop :=
  ∀ item ∈ value.entries, ∀ rule, item.body = .term rule → item.label = (.term, rule.label)

def checkTermLabelsCoherent (value : Value) : Bool :=
  value.entries.all fun item => match item.body with
    | .term rule => decide (item.label = (.term, rule.label))
    | _ => true

theorem checkTermLabelsCoherent_iff (value : Value) :
    checkTermLabelsCoherent value = true ↔ TermLabelsCoherent value := by
  constructor
  · intro checked item member rule body
    have selected := List.all_eq_true.mp checked item member
    simpa only [body, decide_eq_true_eq] using selected
  · intro coherent
    apply List.all_eq_true.mpr
    intro item member
    cases body : item.body <;> simp only
    case term rule => exact decide_eq_true (coherent item member rule body)

theorem raw_term_member (name : String) (value : Value) (rule : GrammarRule) :
    rule ∈ (flattenRaw name value).terms ↔
      ∃ item ∈ value.entries, item.body = .term rule := by
  simp only [flattenRaw, List.mem_filterMap]
  constructor
  · rintro ⟨item, member, produced⟩
    cases body : item.body <;> try { simp [body] at produced }
    rename_i actual
    have same : actual = rule := by simpa only [body, Option.some.injEq] using produced
    exact ⟨item, member, same ▸ body⟩
  · rintro ⟨item, member, body⟩
    exact ⟨item, member, by rw [body]⟩

private theorem recheck_member {items result : List Item}
    (checked : recheck items = .ok result) {item : Item} (member : item ∈ items) : item ∈ result := by
  unfold recheck at checked
  cases found : ModuleAlgebra.orderedCheck? items with
  | none => simp [found] at checked
  | some entries =>
    rw [found] at checked
    have sameResult : entries = result := Except.ok.inj checked
    rw [← sameResult]
    apply List.mem_toFinset.mp
    rw [ModuleAlgebra.orderedCheck_toFinset items entries found]
    exact List.mem_toFinset.mpr member

private theorem rechecked_mapper {value result : Value} {row : Replacement} {item : Item}
    {old : GrammarRule} {map : List Pattern → List Pattern}
    (accepted : replaceRow value row = .ok result)
    (found : value.entries.find? (·.label == (.term, row.old)) = some item)
    (body : item.body = .term old) (computed : argumentMap old row.rule = some map)
    (checked : checkReplacementTyping old row.rule = true)
    (faithful : checkFaithful value old row.rule = .ok ()) :
    recheck (replaceItems value.entries row map) = .ok result.entries := by
  cases rechecked : recheck (replaceItems value.entries row map) with
  | error failure =>
    simp [replaceRow, found, body, computed, checked, faithful, rechecked, bind, Except.bind] at accepted
  | ok entries =>
    have same := accepted
    simp [replaceRow, found, body, computed, checked, faithful, rechecked, bind, Except.bind] at same
    cases same
    rfl

/-- The actual successful producer supplies the local signature transport.
The source checks concern declaration labels/origins, not target typing. -/
theorem signature_of_replaceRow (value : Value) (row : Replacement) {result : Value}
    (accepted : replaceRow value row = .ok result)
    (coherent : TermLabelsCoherent value) (valid : ModuleAlgebra.Valid value.entries.toFinset)
    (sourceName targetName : String) :
    ∃ old map, old.label = row.old ∧ argumentMap old row.rule = some map ∧
      checkReplacementTyping old row.rule = true ∧
      Signature (flattenRaw sourceName value) (flattenRaw targetName result) old row.rule := by
  obtain ⟨item, old, map, found, body, computed, checked, faithful⟩ :=
    replaceRow_typing_readout value row accepted
  have member := List.mem_of_find?_eq_some found
  have key : item.label = (.term, row.old) := by simpa using List.find?_some found
  have oldLabel : old.label = row.old :=
    (Prod.mk.inj ((coherent item member old body).symm.trans key)).2
  have rechecked := rechecked_mapper accepted found body computed checked faithful
  refine ⟨old, map, oldLabel, computed, checked, ?_⟩
  refine ⟨(raw_term_member _ _ _).mpr ⟨item, member, body⟩, ?_, ?_, ?_⟩
  · intro rule selected sameLabel
    obtain ⟨other, otherMember, otherBody⟩ := (raw_term_member _ _ _).mp selected
    have sameKey : other.label = item.label :=
      (coherent other otherMember rule otherBody).trans
        ((congrArg (fun label => (Kind.term, label)) sameLabel).trans (coherent item member old body).symm)
    have sameItem := valid other (List.mem_toFinset.mpr otherMember) item (List.mem_toFinset.mpr member)
      (.inr sameKey)
    have sameBody := congrArg (fun entry : Item => entry.body) sameItem
    rw [otherBody, body] at sameBody
    exact Decl.term.inj sameBody
  · let image : Item := ⟨item.origin, (.term, row.rule.label),
        .term (renameUnitReferences row.old row.rule.label row.rule)⟩
    have produced : image ∈ replaceItems value.entries row map := by
      apply List.mem_map.mpr
      refine ⟨item, member, ?_⟩
      simp only [key, ↓reduceIte, image]
    apply (raw_term_member _ _ _).mpr
    exact ⟨image, recheck_member rechecked produced, by simp only [image, oldLabel]⟩
  · intro rule selected different
    obtain ⟨other, otherMember, otherBody⟩ := (raw_term_member _ _ _).mp selected
    have retained : other.label ≠ (.term, row.old) := by
      rw [coherent other otherMember rule otherBody]
      intro sameKey
      exact different ((Prod.mk.inj sameKey).2.trans oldLabel.symm)
    obtain ⟨image, imageMember, _, _, imageBody⟩ :=
      replaceRow_retains_unit_transport value row accepted otherMember otherBody retained
    exact (raw_term_member _ _ _).mpr ⟨image, imageMember, by simpa only [oldLabel] using imageBody⟩

/-- Successful named replacement preserves the whole typed pattern in the
actual raw declaration output, not only the selected argument spine. -/
theorem typed_of_replaceRow (value : Value) (row : Replacement) {result : Value}
    (accepted : replaceRow value row = .ok result)
    (coherent : TermLabelsCoherent value) (valid : ModuleAlgebra.Valid value.entries.toFinset)
    (sourceName targetName : String) :
    ∃ old map, old.label = row.old ∧ argumentMap old row.rule = some map ∧
      ∀ (_ : namedArguments? old row.rule = true) (free : FreeTypeContext) (bound : List TypeExpr)
        (pattern : Pattern) (type : TypeExpr),
        HasType (flattenRaw sourceName value) free bound pattern type →
          HasType (flattenRaw targetName result) free bound
            (renameConstructor row.old row.rule.label map pattern) type := by
  obtain ⟨old, map, oldLabel, computed, checked, signature⟩ :=
    signature_of_replaceRow value row accepted coherent valid sourceName targetName
  refine ⟨old, map, oldLabel, computed, ?_⟩
  intro named free bound pattern type original
  simpa only [oldLabel] using typed signature checked named computed bound original

end Mettapedia.GSLT.LanguageDef.ModuleSource.ReplacementTransport
