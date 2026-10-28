import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourceViews
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16Scalar

/-! Closed lexical leaves in the actual compositional Datalog Core.
The source grammar and lexical profile stay unchanged. The semantic module
adds the fixed radix data constructors and one wrapper per lexical sort.
Typing and scalar-class formation are proved separately. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
namespace ScalarSource

open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

#module_file "../../../../../../metta/gslt/module/gold/SouffleDatalog/ScalarRealization.module"
#module_roundtrip ScalarRealization

end ScalarSource

namespace ScalarCore

open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

private instance : DecidableEq LanguageDef := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (LanguageDef.mk.injEq _ _ _ _ _ _ _ _ _ _))

def language? : Option LanguageDef := ScalarSource.ScalarRealization.language.toOption
def language : LanguageDef := module_language_view% language?

theorem language_exact : language? = some language := by decide +kernel

theorem radix_rows : Radix16Codec.language.terms ⊆ language.terms := by decide +kernel
theorem source_rows : SourceViews.grammar.terms ⊆ language.terms := by decide +kernel
theorem ast_carriers : ∀ (declaration : TypeDecl), List.Mem declaration language.types →
    declaration.carrier = .ast := by decide +kernel

abbrev Row := Fin SourceViews.profile.states.length

def lexicalState (row : Row) : LexicalStateDecl := SourceViews.profile.states.get row

def leafRule (row : Row) : GrammarRule :=
  language.terms[116 + row.val]'(by have bound := row.isLt; change row.val < 12 at bound; change _ < 171; omega)

theorem leafRule_shape (row : Row) :
    (leafRule row).label = "dl-scalar:" ++ (lexicalState row).resultSort ∧
      (leafRule row).category = (lexicalState row).resultSort ∧
      (leafRule row).params = [.simple "point" (.base "R16Word24")] ∧
      (leafRule row).collectionRepresentation = .bare := by
  fin_cases row <;> decide +kernel

def leafSort (row : Row) : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort language :=
  ⟨(lexicalState row).resultSort, by fin_cases row <;> decide +kernel⟩

def wordLeaf (row : Row) (point : Fin (16 ^ 6)) : Pattern :=
  .apply ("dl-scalar:" ++ (lexicalState row).resultSort) [Radix16Codec.encode point]

theorem wordLeaf_typed (row : Row) (point : Fin (16 ^ 6)) :
    HasType language FreeTypeContext.empty [] (wordLeaf row point) (.base (lexicalState row).resultSort) := by
  obtain ⟨label, category, parameters, representation⟩ := leafRule_shape row
  have member : leafRule row ∈ language.terms := List.getElem_mem _
  have notBare : ¬UsesBareCollection (leafRule row) := by
    simp [UsesBareCollection, GrammarRule.bareParams, representation, parameters]
  have arguments : ArgumentsHaveTypes language FreeTypeContext.empty []
      [Radix16Codec.encode point] (leafRule row).params := by
    rw [parameters]
    exact .cons trivial rfl (HasType.of_terms_subset radix_rows (Radix16Codec.encode_typed point)) .nil
  have typed := HasType.constructor member notBare arguments
  simpa only [wordLeaf, label, category] using typed

theorem wordLeaf_closed (row : Row) (point : Fin (16 ^ 6)) :
    ClosedTermWellSorted language (leafSort row) (wordLeaf row point) :=
  ⟨wordLeaf_typed row point, by rfl, by rfl, by rfl, (wordLeaf_typed row point).isWellScopedAt⟩

def leaf (row : Row) (point : Nat)
    (formed : SourceViews.profile.ClassEvidence (lexicalState row).className point) : Pattern :=
  wordLeaf row ⟨point, Radix16Scalar.scalar_word_bound point
    (Radix16Scalar.classEvidence_scalar _ _ _ formed)⟩

theorem leaf_closed (row : Row) (point : Nat)
    (formed : SourceViews.profile.ClassEvidence (lexicalState row).className point) :
    ClosedTermWellSorted language (leafSort row) (leaf row point formed) :=
  wordLeaf_closed _ _

def readLeaf? (row : Row) : Pattern → Option Nat
  | .apply label [word] =>
    if label = "dl-scalar:" ++ (lexicalState row).resultSort then do
      let point ← Radix16Scalar.decode? word
      if SourceViews.profile.ClassEvidence (lexicalState row).className point then some point else none
    else none
  | _ => none

theorem readLeaf?_leaf (row : Row) (point : Nat)
    (formed : SourceViews.profile.ClassEvidence (lexicalState row).className point) :
    readLeaf? row (leaf row point formed) = some point := by
  have scalar := Radix16Scalar.classEvidence_scalar _ _ _ formed
  simp [readLeaf?, leaf, wordLeaf, Radix16Scalar.decode?, Radix16Codec.decode?_encode, scalar, formed]

theorem actual_unicode_controls :
    readLeaf? ⟨6, by decide⟩ (wordLeaf ⟨6, by decide⟩ 955) = some 955 ∧
      readLeaf? ⟨6, by decide⟩ (wordLeaf ⟨6, by decide⟩ 128512) = some 128512 ∧
      readLeaf? ⟨3, by decide⟩ (wordLeaf ⟨3, by decide⟩ 955) = none ∧
      readLeaf? ⟨6, by decide⟩ (wordLeaf ⟨6, by decide⟩ 34) = none ∧
      readLeaf? ⟨3, by decide⟩ (wordLeaf ⟨6, by decide⟩ 49) = none := by decide +kernel

#print axioms language_exact
#print axioms radix_rows
#print axioms source_rows
#print axioms wordLeaf_closed
#print axioms leaf_closed
#print axioms readLeaf?_leaf
#print axioms actual_unicode_controls

end ScalarCore
end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog
