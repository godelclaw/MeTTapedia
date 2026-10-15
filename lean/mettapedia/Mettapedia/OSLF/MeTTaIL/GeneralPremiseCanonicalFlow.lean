import Mettapedia.OSLF.MeTTaIL.GeneralPremiseCanonicalCaptures

/-!
# Canonical object captures through actual premise histories

Provider outputs and directed child targets use their checked canonical
carriers. Quantifiers bind canonical elements from the actual collection
read and restore their lexical parameter. These laws preserve the complete
captured bodies independently of equality between answer readouts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching

theorem CanonicalValues.empty : CanonicalValues [] := by
  intro name value found
  simp [lookup] at found

theorem CanonicalValues.bindParameter {assignment : Assignment}
    (before : CanonicalValues assignment) (parameter : String) {bound : List TypeExpr}
    {element : Pattern} (canonical : element.hasCanonicalBinderMetadata = true) :
    CanonicalValues (bindParameter parameter (localValue bound element) assignment) := by
  intro name value found
  by_cases same : name = parameter
  · subst name
    rw [lookup_bind_parameter] at found
    cases Option.some.inj found
    exact canonical
  · exact before name value (by rw [lookup_bind_other _ _ _ _ same] at found; exact found)

theorem finiteCollection?_canonical {ambient : Nat} {assignment : Assignment}
    (before : CanonicalValues assignment) {name : String} {kind : CollType} {elements : List Pattern}
    (read : finiteCollection? ambient assignment name = some (kind, elements)) :
    Pattern.hasCanonicalBinderMetadataList elements = true := by
  unfold finiteCollection? at read
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at read
  obtain ⟨value, found, actual, projected, read⟩ := read
  have canonical := instantiateValue?_canonical (before name value found) projected
  unfold concreteCollection? at read
  split at read <;> try contradiction
  cases Prod.mk.inj (Option.some.inj read) with
  | intro kindEqual elementsEqual =>
    simpa only [Pattern.hasCanonicalBinderMetadata, elementsEqual] using canonical

theorem ValuesTyped.canonical {language : LanguageDef}
    {free : Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {values : List Pattern} {types : List TypeExpr}
    (typed : ValuesTyped language free bound values types) :
    Pattern.hasCanonicalBinderMetadataList values = true := by
  induction typed with
  | nil => rfl
  | cons head tail ih =>
    simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true]
    exact ⟨head.2.1, ih⟩

theorem ArgumentsHold.canonical {context : Context} {index : Nat}
    {initial final : Assignment} {schemas values : List Pattern} {modes : List RelationArgMode}
    (held : ArgumentsHold context index initial schemas values modes final)
    (before : CanonicalValues initial)
    (valuesCanonical : Pattern.hasCanonicalBinderMetadataList values = true) :
    CanonicalValues final := by
  induction held with
  | nil => exact before
  | cons head tail ih =>
    simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at valuesCanonical
    cases head with
    | input _ => exact ih before valuesCanonical.2
    | output matching =>
      exact ih (matching_canonicalValues before valuesCanonical.1 matching) valuesCanonical.2

theorem TracedQuery.canonical {environment : Environment} {context : Context}
    {relation : String} {arguments : List Pattern} {initial final : Assignment}
    {rowIndex : Nat} {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (held : TracedQuery environment context relation arguments initial rowIndex final origins)
    (before : CanonicalValues initial) : CanonicalValues final := by
  cases held with
  | row _ _ rowTyped arguments _ => exact arguments.readout.canonical before rowTyped.2.canonical

theorem RootFiring.target_canonical {environment : Environment} {bound : List TypeExpr}
    {type : TypeExpr} {source target : Pattern} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List Event}
    (held : RootFiring environment bound type source index trace captured completed history target) :
    target.hasCanonicalBinderMetadata = true := by
  cases held with
  | fire _ _ _ _ _ _ _ _ targetTyped => exact targetTyped.2.1

mutual
  theorem PremiseHolds.canonical {environment : Environment} {context : Context}
      {premise : Premise} {initial final : Assignment} {event : Event}
      (held : PremiseHolds environment context premise initial final event)
      (before : CanonicalValues initial) : CanonicalValues final := by
    cases held with
    | query query => exact query.canonical before
    | freshness _ _ => exact before
    | step _ _ child matching _ =>
      exact matching_canonicalValues before child.target_canonical matching.matching
    | scopedStep _ child matching _ =>
      exact matching_canonicalValues before child.target_canonical matching.matching
    | quantified read elements =>
      exact elements.canonical before (finiteCollection?_canonical before read)

  theorem PremisesHold.canonical {environment : Environment} {context : Context}
      {premises : List Premise} {initial final : Assignment} {events : List Event}
      (held : PremisesHold environment context premises initial final events)
      (before : CanonicalValues initial) : CanonicalValues final :=
    match held with
    | .nil => before
    | .cons head tail => tail.canonical (head.canonical before)

  theorem QuantifiedElements.canonical {environment : Environment} {context : Context}
      {parameter : String} {body : Premise} {index : Nat} {elements : List Pattern}
      {initial final : Assignment} {events : List (Nat × Pattern × List Event)}
      (held : QuantifiedElements environment context parameter body index elements initial final events)
      (before : CanonicalValues initial)
      (elementsCanonical : Pattern.hasCanonicalBinderMetadataList elements = true) :
      CanonicalValues final := by
    cases held with
    | nil => exact before
    | cons _ head tail =>
      simp only [Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true] at elementsCanonical
      exact tail.canonical
        (before.restoreParameter
          (head.canonical (before.bindParameter parameter elementsCanonical.1)) parameter)
        elementsCanonical.2
end

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
