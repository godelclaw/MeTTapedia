import Mettapedia.GSLT.LanguageDef.ModuleSource.ReplacementTransport
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef

/-!
# Typed binary packing through the actual representation lowering

Binary replacement first constructs an application to a collection. Its
declared representation then decides whether the application is retained or
unwrapped. This comparison uses the executable replacement traversal and
`CoreReduction.unwrap`; it does not infer collection equations or authorize
normalization in a collection-data fibre.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.BinaryCollectionLowering

open Mettapedia.OSLF.MeTTaIL Syntax WellSorted ReplacementTransport

def packing (kind : CollType) (arguments : List Pattern) : List Pattern :=
  [.collection kind arguments none]

abbrev translated (target : LanguageDef) (old new : GrammarRule) (kind : CollType)
    (pattern : Pattern) : Pattern :=
  CoreReduction.unwrap (CoreReduction.bareLabels target)
    (renameConstructor old.label new.label (packing kind) pattern)

/-- Local lookups in the actual lowering table. Other ordinary constructors
retain their labels, while the selected constructor follows its declaration.
These are finite signature conditions, not whole-term transport assumptions. -/
structure Representation (source target : LanguageDef) (old new : GrammarRule)
    (kind : CollType) : Prop where
  selected : (CoreReduction.bareLabels target).lookup new.label =
    if new.collectionRepresentation = .bare then some kind else none
  retained : ∀ rule ∈ source.terms, rule.label ≠ old.label →
    ¬ UsesBareCollection rule →
    (CoreReduction.bareLabels target).lookup rule.label = none

def checkRepresentation (source target : LanguageDef) (old new : GrammarRule)
    (kind : CollType) : Bool :=
  decide ((CoreReduction.bareLabels target).lookup new.label =
    if new.collectionRepresentation = .bare then some kind else none) &&
  source.terms.all fun rule => rule.label == old.label || usesBareCollection? rule ||
    decide ((CoreReduction.bareLabels target).lookup rule.label = none)

theorem checkRepresentation_iff (source target : LanguageDef) (old new : GrammarRule)
    (kind : CollType) :
    checkRepresentation source target old new kind = true ↔
      Representation source target old new kind := by
  simp only [checkRepresentation, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨selected, retained⟩
    refine ⟨selected, ?_⟩
    intro rule member different ordinary
    rcases retained rule member with (same | bare) | absent
    · exact False.elim (different same)
    · exact False.elim (ordinary ((usesBareCollection?_eq_true_iff rule).mp bare))
    · exact absent
  · intro represented
    refine ⟨represented.selected, ?_⟩
    intro rule member
    by_cases same : rule.label = old.label
    · exact .inl (.inl same)
    · by_cases bare : UsesBareCollection rule
      · exact .inl (.inr ((usesBareCollection?_eq_true_iff rule).mpr bare))
      · exact .inr (represented.retained rule member same bare)

theorem computed_packing {old new : GrammarRule} {name sort : String} {kind : CollType}
    (checked : checkReplacementTyping old new = true)
    (named : namedArguments? old new = false)
    (shape : new.params = [.simple name (.collection kind (.base sort))]) :
    argumentMap old new = some (packing kind) := by
  have uniform := (checkReplacementTyping_packed checked named shape).2.2.2
  have all : old.params.all (fun parameter => match parameter with
      | .simple _ (.base actual) => decide (actual = sort)
      | _ => false) = true := by
    apply List.all_eq_true.mpr
    intro parameter member
    obtain ⟨_, rfl⟩ := uniform parameter member
    simp
  simp only [argumentMap, named, Bool.false_eq_true, ↓reduceIte, shape]
  change (if old.params.all (fun parameter => match parameter with
      | .simple _ (.base actual) => decide (actual = sort)
      | _ => false) then some (packing kind) else none) = some (packing kind)
  rw [all]
  rfl

theorem old_not_bare {old new : GrammarRule} {name sort : String} {kind : CollType}
    (checked : checkReplacementTyping old new = true)
    (named : namedArguments? old new = false)
    (shape : new.params = [.simple name (.collection kind (.base sort))]) :
    ¬ UsesBareCollection old := by
  obtain ⟨_, arity, _, _⟩ := checkReplacementTyping_packed checked named shape
  rintro ⟨parameter, actual, element, bare⟩
  have params := (GrammarRule.bareParams_cons_iff _ _ _).mp bare
  rw [params.2] at arity
  simp at arity

theorem translated_representation (target : LanguageDef) (old new : GrammarRule)
    (kind : CollType) (parameter : TermParam) (pattern : Pattern)
    (represented : MatchesParameterRepresentation parameter pattern) :
    MatchesParameterRepresentation parameter (translated target old new kind pattern) := by
  cases parameter with
  | simple => trivial
  | abstractionNamed binder name type =>
    obtain ⟨body, rfl⟩ := (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp represented
    exact (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mpr
      ⟨translated target old new kind body, by
        simp only [translated, renameConstructor, CoreReduction.unwrap]⟩
  | multiAbstractionNamed binders name type =>
    obtain ⟨arity, body, rfl⟩ := (matchesParameterRepresentation_multiAbstractionNamed_iff _ _ _ _).mp represented
    exact (matchesParameterRepresentation_multiAbstractionNamed_iff _ _ _ _).mpr
      ⟨arity, translated target old new kind body, by
        simp only [translated, renameConstructor, CoreReduction.unwrap]⟩

private theorem homogeneous {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
    {type : TypeExpr} (typed : ArgumentsHaveTypes language free bound arguments parameters)
    (uniform : ∀ parameter ∈ parameters, ∃ name, parameter = .simple name type) :
    ElementsHaveType language free bound arguments type := by
  induction parameters generalizing arguments with
  | nil => cases typed; exact .nil _ _
  | cons parameter parameters ih =>
    obtain ⟨name, same⟩ := uniform parameter List.mem_cons_self
    subst parameter
    cases typed with
    | cons represented declared first rest =>
      have same : type = _ := Option.some.inj declared
      exact .cons (same ▸ first)
        (ih rest (fun parameter member => uniform parameter (List.mem_cons_of_mem _ member)))

variable {source target : LanguageDef} {old new : GrammarRule}
    {name sort : String} {kind : CollType}

mutual
  /-- Whole-pattern typing after the actual packing and representation
  traversals, with the bound context retained through every recursive case. -/
  theorem typed (signature : Signature source target old new)
      (representation : Representation source target old new kind)
      (checked : checkReplacementTyping old new = true)
      (named : namedArguments? old new = false)
      (shape : new.params = [.simple name (.collection kind (.base sort))])
      (free : FreeTypeContext) (bound : List TypeExpr) {pattern : Pattern} {type : TypeExpr}
      (original : HasType source free bound pattern type) :
      HasType target free bound (translated target old new kind pattern) type := by
    cases original with
    | bvar found =>
      simpa only [translated, renameConstructor, CoreReduction.unwrap] using
        (HasType.bvar (language := target) found)
    | fvar found =>
      simpa only [translated, renameConstructor, CoreReduction.unwrap] using
        (HasType.fvar (language := target) found)
    | @constructor bound rule arguments member notBare argumentsTyped =>
      have mapped := arguments_typed signature representation checked named shape free bound argumentsTyped
      by_cases selected : rule.label = old.label
      · have same := signature.unique rule member selected
        subst rule
        have uniform := (checkReplacementTyping_packed checked named shape).2.2.2
        have elements := homogeneous mapped uniform
        have category := checkReplacementTyping_category checked
        cases mode : new.collectionRepresentation with
        | bare =>
          have lookup : (CoreReduction.bareLabels target).lookup new.label = some kind := by
            simpa [mode] using representation.selected
          have newShape : (renameUnitReferences old.label new.label new).bareParams =
              [.simple name (.collection kind (.base sort))] := by
            simp only [renameUnitReferences, GrammarRule.bareParams, mode, shape]
          have result := HasType.collectionConstructor (rule := renameUnitReferences old.label new.label new)
            (rest := none) signature.replaced newShape elements
          simpa only [translated, renameConstructor, ↓reduceIte, packing, List.map_cons,
            List.map_nil, CoreReduction.unwrap, lookup,
            List.map_map, Function.comp_def, renameUnitReferences, ← category] using result
        | wrapped =>
          have lookup : (CoreReduction.bareLabels target).lookup new.label = none := by
            simpa [mode] using representation.selected
          have ordinary : ¬ UsesBareCollection (renameUnitReferences old.label new.label new) := by
            rintro ⟨_, _, _, bare⟩
            change new.bareParams = _ at bare
            rw [GrammarRule.bareParams_of_wrapped _ mode] at bare
            cases bare
          have packed : ArgumentsHaveTypes target free bound
              [.collection kind (arguments.map (translated target old new kind)) none] new.params := by
            rw [shape]
            exact .cons trivial rfl (.collection elements) .nil
          have result := HasType.constructor (rule := renameUnitReferences old.label new.label new)
            signature.replaced ordinary packed
          simpa only [translated, renameConstructor, ↓reduceIte, packing, List.map_cons,
            List.map_nil, CoreReduction.unwrap, lookup,
            List.map_map, Function.comp_def, renameUnitReferences, ← category] using result
      · have result := HasType.constructor (rule := renameUnitReferences old.label new.label rule)
          (signature.retained rule member selected) notBare mapped
        simpa only [translated, renameConstructor, if_neg selected, CoreReduction.unwrap,
          representation.retained rule member selected notBare, List.map_map, Function.comp_def,
          renameUnitReferences] using result
    | @lambda bound binder body domain codomain bodyTyped =>
      simpa only [translated, renameConstructor, CoreReduction.unwrap] using
        (HasType.lambda (binder := binder) (typed signature representation checked named shape free (domain :: bound) bodyTyped))
    | @multiLambda bound arity binders body domain codomain bodyTyped =>
      simpa only [translated, renameConstructor, CoreReduction.unwrap] using
        (HasType.multiLambda (binders := binders)
          (typed signature representation checked named shape free (List.replicate arity domain ++ bound) bodyTyped))
    | @subst bound body replacement domain codomain bodyTyped replacementTyped =>
      simpa only [translated, renameConstructor, CoreReduction.unwrap] using
        (HasType.subst (typed signature representation checked named shape free (domain :: bound) bodyTyped)
          (typed signature representation checked named shape free bound replacementTyped))
    | @collection bound actual elements rest elementType elementsTyped =>
      have result := HasType.collection (collectionType := actual) (rest := rest)
        (elements_typed signature representation checked named shape free bound _ elementsTyped)
      simpa only [translated, renameConstructor, CoreReduction.unwrap, List.map_map, Function.comp_def] using
        result
    | @collectionConstructor bound rule parameter actual elements rest element member bare elementsTyped =>
      have mapped := elements_typed signature representation checked named shape free bound _ elementsTyped
      have selected : rule.label ≠ old.label := by
        intro sameLabel
        have same := signature.unique rule member sameLabel
        subst rule
        exact old_not_bare checked named shape ⟨parameter, actual, element, bare⟩
      simpa only [translated, renameConstructor, CoreReduction.unwrap, List.map_map,
        Function.comp_def, renameUnitReferences] using
        (HasType.collectionConstructor (rule := renameUnitReferences old.label new.label rule)
          (rest := rest) (signature.retained rule member selected) bare mapped)
  termination_by sizeOf pattern

  theorem arguments_typed (signature : Signature source target old new)
      (representation : Representation source target old new kind)
      (checked : checkReplacementTyping old new = true)
      (named : namedArguments? old new = false)
      (shape : new.params = [.simple name (.collection kind (.base sort))])
      (free : FreeTypeContext) (bound : List TypeExpr)
      {arguments : List Pattern} {parameters : List TermParam}
      (original : ArgumentsHaveTypes source free bound arguments parameters) :
      ArgumentsHaveTypes target free bound
        (arguments.map (translated target old new kind)) parameters := by
    cases original with
    | nil => exact .nil
    | cons represented declared first rest =>
      exact .cons (translated_representation _ _ _ _ _ _ represented) declared
        (typed signature representation checked named shape free bound first)
        (arguments_typed signature representation checked named shape free bound rest)
  termination_by sizeOf arguments

  theorem elements_typed (signature : Signature source target old new)
      (representation : Representation source target old new kind)
      (checked : checkReplacementTyping old new = true)
      (named : namedArguments? old new = false)
      (shape : new.params = [.simple name (.collection kind (.base sort))])
      (free : FreeTypeContext) (bound : List TypeExpr)
      (type : TypeExpr) {elements : List Pattern}
      (original : ElementsHaveType source free bound elements type) :
      ElementsHaveType target free bound
        (elements.map (translated target old new kind)) type := by
    cases original with
    | nil => exact .nil _ _
    | cons first rest =>
      exact .cons (typed signature representation checked named shape free bound first)
        (elements_typed signature representation checked named shape free bound type rest)
  termination_by sizeOf elements
end

/-- The real producer supplies declaration membership and type compatibility;
the finite lowering-table check supplies the representation comparison. -/
theorem typed_of_replaceRow (value : Value) (row : Replacement) {result : Value}
    (accepted : replaceRow value row = .ok result)
    (coherent : TermLabelsCoherent value) (valid : ModuleAlgebra.Valid value.entries.toFinset)
    (sourceName targetName : String) :
    ∃ old, old.label = row.old ∧
      ∀ (name sort : String) (kind : CollType),
        namedArguments? old row.rule = false →
        row.rule.params = [.simple name (.collection kind (.base sort))] →
        checkRepresentation (flattenRaw sourceName value) (flattenRaw targetName result)
          old row.rule kind = true →
        ∀ (free : FreeTypeContext) (bound : List TypeExpr) (pattern : Pattern) (type : TypeExpr),
          HasType (flattenRaw sourceName value) free bound pattern type →
          HasType (flattenRaw targetName result) free bound
            (CoreReduction.unwrap (CoreReduction.bareLabels (flattenRaw targetName result))
              (renameConstructor row.old row.rule.label (packing kind) pattern)) type := by
  obtain ⟨old, _, oldLabel, _, checked, signature⟩ :=
    signature_of_replaceRow value row accepted coherent valid sourceName targetName
  refine ⟨old, oldLabel, ?_⟩
  intro name sort kind named shape representation free bound pattern type original
  simpa only [← oldLabel] using
    typed signature ((checkRepresentation_iff _ _ _ _ _).mp representation)
      checked named shape free bound original

end Mettapedia.GSLT.LanguageDef.ModuleSource.BinaryCollectionLowering
