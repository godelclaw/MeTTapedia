import Mettapedia.GSLT.LanguageDef.WellSorted

/-!
# Evidence for a collection constructor's authored row

An unlabelled collection pattern may receive a carrier type from a
single-collection grammar row. The ordinary typing proposition states only
the resulting type; this evidence retains the exact authored row, parameter
name, and element sort. It makes the information loss from bare-pattern
typing explicit. Bare collection evidence retains the constructor's bare
representation premise; wrapped constructors use their named application.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CollectionConstructorEvidence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- A witness that a bare collection is admitted by one particular authored
constructor. Two distinct rows can have the same bare representation. -/
structure RowEvidence (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr)
    (kind : CollType) (elements : List Pattern)
    (rest : Option String)
    (resultSort : String) where
  rule : GrammarRule
  parameterName : String
  elementType : TypeExpr
  member : rule ∈ language.terms
  result : rule.category = resultSort
  representation : rule.collectionRepresentation = .bare
  parameterShape :
    rule.params = [.simple parameterName (.collection kind elementType)]
  elementsTyped : ElementsHaveType language free bound elements elementType

/-- Forgetting the selected row recovers the existing bare-collection typing
judgment. This map need not be injective. -/
theorem RowEvidence.toHasType
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {kind : CollType}
    {elements : List Pattern} {rest : Option String}
    {resultSort : String}
    (evidence : RowEvidence language free bound kind elements rest resultSort) :
    HasType language free bound (.collection kind elements rest)
      (.base resultSort) := by
  have typed : HasType language free bound
      (.collection kind elements rest) (.base evidence.rule.category) :=
    HasType.collectionConstructor evidence.member
      ((evidence.rule.bareParams_of_bare evidence.representation).trans
        evidence.parameterShape) evidence.elementsTyped
  simpa only [evidence.result] using typed

/-- The constructor label is retained as data rather than reconstructed from
the proof-irrelevant typing proposition. -/
def RowEvidence.label
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {kind : CollType}
    {elements : List Pattern} {rest : Option String}
    {resultSort : String}
    (evidence : RowEvidence language free bound kind elements rest resultSort) :
    String :=
  evidence.rule.label

theorem RowEvidence.ne_of_label_ne
    {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {kind : CollType}
    {elements : List Pattern} {rest : Option String}
    {resultSort : String}
    {first second : RowEvidence language free bound kind elements rest resultSort}
    (different : first.label ≠ second.label) :
    first ≠ second := by
  intro equal
  exact different (congrArg RowEvidence.label equal)

end Mettapedia.GSLT.LanguageDef.CollectionConstructorEvidence
