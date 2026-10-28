import Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

/-! Data quotation keeps literal contents even when field names are keywords
in the caller. These equalities certify data proposals, not language admission. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

private def source : LanguageDef := {
  name := "name := \"quoted\"\nλ😀",
  types := [⟨"Value", .ast⟩],
  terms := [{ label := "Quoted", category := "Value", params := [], syntaxPattern := [.terminal "first line\nsecond line", .terminal "name := \\\"kept\\\""] }],
  equations := [], rewrites := [] }

private def profile : ParserProfileLayer := {
  name := "profile\nname := \"kept\"", startSort := "Value",
  classes := [⟨"name := λ😀", .points [955,128512]⟩],
  states := [⟨"Value", "name := λ😀", "quoted\\leaf"⟩] }

local syntax "name" : term

private def quotedSource : LanguageDef := module_language_view% (some source)
private def quotedProfile : ParserProfileLayer := module_profile_view% (some profile)

theorem source_proposal_exact : quotedSource = source := by rfl
theorem profile_proposal_exact : quotedProfile = profile := by rfl

theorem changed_literal_refused : quotedSource.name ≠ "name := quoted λ😀" := by decide
theorem lexical_class_literal_retained :
    quotedProfile.classAccepts? "name := λ😀" 955 = some true ∧
      quotedProfile.classAccepts? "name := λ😀" 49 = some false ∧
      quotedProfile.classAccepts? "name := kept" 955 = none := by decide

#print axioms source_proposal_exact
#print axioms profile_proposal_exact
#print axioms changed_literal_refused
#print axioms lexical_class_literal_retained

end Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews.Controls
