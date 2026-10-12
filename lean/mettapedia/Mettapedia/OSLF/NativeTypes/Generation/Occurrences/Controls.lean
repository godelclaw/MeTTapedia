import Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Typing

open Mettapedia.OSLF.Framework

/-!
# Binding and declaration-origin controls for the generated input

These controls follow the whole-language soundness/completeness laws. A
nonempty binding equation is retained while every body and abstraction
position is generated. Equal authored rules have different original origins.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted

def termType : TypeExpr := .base "Term"
def nameType : TypeExpr := .base "Name"

def rewrite : RewriteRule where
  name := "erase"
  typeContext := [("body", termType), ("outside", termType)]
  premises := []
  left := .apply "Pair" [.lambda none (.fvar "body"), .fvar "outside"]
  right := .fvar "outside"

def bindingEquation : Equation where
  name := "binding-associativity"
  typeContext := [("p", termType), ("q", termType), ("r", termType)]
  premises := []
  left := .lambda none (.apply "Join" [.apply "Join" [.fvar "p", .fvar "q"], .fvar "r"])
  right := .lambda none (.apply "Join" [.fvar "p", .apply "Join" [.fvar "q", .fvar "r"]])

def language : LanguageDef where
  name := "GeneratedBindingSites"
  types := ["Term", "Name"]
  terms := [
    { label := "Pair", category := "Term",
      params := [.simple "body" (.arrow nameType termType), .simple "outside" termType],
      syntaxPattern := [] },
    { label := "Join", category := "Term",
      params := [.simple "left" termType, .simple "right" termType], syntaxPattern := [] }]
  equations := [bindingEquation]
  rewrites := [rewrite, rewrite]

def bodyContext : OneHoleContext :=
  .apply "Pair" [] (.lambda none .hole) [.fvar "outside"]

def bodySite (index : Nat) : Site where
  context := bodyContext
  focus := .fvar "body"
  declaration := index
  rule := rewrite

theorem all_authored_origins_generate_the_binder_body (index : Nat) (within : index < 2) :
    bodySite index ∈ generate language := by
  apply (generate_spec _ _).mpr
  constructor
  · apply List.mk_mem_zipIdx_iff_getElem?.mpr
    match index with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => omega
  · exact Selects.apply (Selects.lambda Selects.here)

theorem same_focus_distinct_authored_origins :
    (bodySite 0).focus = (bodySite 1).focus ∧ bodySite 0 ≠ bodySite 1 := by
  refine ⟨rfl, ?_⟩
  intro equal
  have indices := congrArg Site.declaration equal
  contradiction

theorem generated_exact_binder_address : (bodySite 0).position = [0, 0] := rfl

theorem exact_rely_and_hidden_variables :
    (bodySite 0).relyNames = ["outside"] ∧
      (bodySite 0).hiddenNames = ["body"] := by decide

theorem local_slots_are_computed :
    (bodySite 0).localSlots = [.rely "outside", .output] := by decide

theorem invalid_child_has_no_decomposition :
    ¬ ∃ context, Selects (.fvar "absent") context rewrite.left := by
  rintro ⟨context, selected⟩
  have member := selected_focus_mem_subterms selected
  simp [rewrite, subterms, subtermsList] at member

theorem the_binding_equation_is_nonempty : language.equations ≠ [] := by
  intro empty
  cases empty

theorem equation_changes_do_not_prune_binder_positions :
    generate {language with equations := []} = generate language :=
  equations_preserve_generated_sites language []

def typedBodyData : SiteData where
  address := [0, 0]
  context := bodyContext
  focus := .fvar "body"
  focusBound := [nameType]
  focusType := termType
  typingFrames := [.application 0 0, .lambda nameType]

def typedBodySite : TypedSite := ⟨0, rewrite, termType, typedBodyData⟩

theorem binder_carrier_is_generated : typedBodySite ∈ typedGenerate language := by
  apply (typedGenerate_spec _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · exact List.mk_mem_zipIdx_iff_getElem?.mpr (by rfl)
  · simp [sourceCandidates, typedBodySite, language, termType, TypeDecl.plain]
  · apply Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.generate_sound
    decide +kernel

theorem binder_carrier_and_bound_context_are_earned :
    HasType language (ruleFree rewrite) [nameType] (.fvar "body") termType ∧
      typedBodySite.data.focusBound.length = 1 := by
  exact ⟨typed_generated_focus_carrier binder_carrier_is_generated, rfl⟩

end Mettapedia.OSLF.NativeTypes.Generation.Occurrences.Controls
