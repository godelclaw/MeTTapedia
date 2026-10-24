import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.OSLF.MeTTaIL.Match
import Mathlib.Data.List.Flatten

/-!
# Partial discovery of identity interpretations

Finite signature search constructs the existing typing morphism. Constructor
notation is not part of that obligation. Failure to find the identity action
does not refute other symbol maps or elaborations. Literal equation membership
and ordered rewrite inclusion are additional declaration obligations; ordered
inclusion preserves the premise-free engine's answers as a sublist, without
claiming reflection or conservativity. Native decoding and correspondence to
this checker remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.IdentityInterface

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted

def profile (rule : GrammarRule) : String × String × List TermParam × CollectionRepresentation :=
  (rule.label, rule.category, rule.params, rule.collectionRepresentation)

/-- Exact parameter metadata is a sufficient search profile, not a necessary
condition on all interpretations. The search does not identify renamed sorts. -/
def signatureFits (source target : LanguageDef) : Bool :=
  source.types.all (fun declaration => target.types.any (fun other => decide (other = declaration))) &&
  source.terms.all (fun rule => target.terms.any (fun other =>
    decide (profile other = profile rule)))

private theorem types_of_fits {source target : LanguageDef}
    (fits : signatureFits source target = true) :
    ∀ declaration, List.Mem declaration source.types → List.Mem declaration target.types := by
  simp only [signatureFits, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq] at fits
  intro declaration member
  obtain ⟨other, otherMem, same⟩ := fits.1 declaration member
  exact same ▸ otherMem

private theorem terms_of_fits {source target : LanguageDef}
    (fits : signatureFits source target = true) (rule : GrammarRule)
    (member : rule ∈ source.terms) :
    ∃ other ∈ target.terms, profile other = profile rule := by
  simp only [signatureFits, Bool.and_eq_true] at fits
  have terms := fits.2
  have found := (List.all_eq_true.mp terms) rule member
  simpa only [List.any_eq_true, decide_eq_true_eq] using found

def typingOfFits (source target : ValidatedLanguageDef)
    (fits : signatureFits source.language target.language = true) :
    TypingMorphism source target where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration member := by
    simpa only [mapTypeDecl_id] using types_of_fits fits declaration member
  mapsTerms rule member := by
    obtain ⟨other, otherMem, same⟩ := terms_of_fits fits rule member
    have label := congrArg Prod.fst same
    have category := congrArg (fun p => p.2.1) same
    have parameters := congrArg (fun p => p.2.2.1) same
    have representation := congrArg (fun p => p.2.2.2) same
    refine ⟨other, otherMem, label, category, ?_, representation⟩
    have parameterId : mapTermParam LanguageDefSymbolMap.id = id := funext mapTermParam_id
    simpa only [profile, parameterId, List.map_id] using parameters

/-- The successful result contains the established interface; `none` carries
no claim that another interpretation is impossible. -/
def findTyping? (source target : ValidatedLanguageDef) :
    Option (TypingMorphism source target) :=
  if fits : signatureFits source.language target.language = true then
    some (typingOfFits source target fits)
  else none

theorem typing_preserved {source target : ValidatedLanguageDef}
    (fits : signatureFits source.language target.language = true)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {term : Pattern} {type : TypeExpr}
    (typed : HasType source.language free bound term type) :
    HasType target.language free bound term type := by
  have mapped := typed.mapTyping (typingOfFits source target fits)
  have typeId : mapTypeExpr LanguageDefSymbolMap.id = id := funext mapTypeExpr_id
  simpa only [typingOfFits, FreeTypeContext.map_id, mapTypeExpr_id,
    mapPattern_id, typeId, List.map_id] using mapped

theorem ordered_rewrite_answers_preserved {source target : LanguageDef}
    (included : source.rewrites.Sublist target.rewrites) (term : Pattern) :
    (rewriteStep source term).Sublist (rewriteStep target term) :=
  included.flatMap (fun rule => applyRule rule term)

/-- The operational helper consumes premises and patterns, independently of
the display name. A correspondence must still retain occurrence identities. -/
theorem rule_name_independent (rule : RewriteRule) (name : String) (term : Pattern) :
    applyRule { rule with name := name } term = applyRule rule term := rfl

private def nullary (name spelling : String) : GrammarRule :=
  { label := name, category := "T", params := [], syntaxPattern := [.terminal spelling] }

private def source : LanguageDef :=
  { name := "source", types := [TypeDecl.plain "T"],
    terms := [nullary "A" "a", nullary "B" "b"], equations := [], rewrites := [] }

private def notationChange : LanguageDef :=
  { source with terms := [nullary "A" "zero", nullary "B" "one"] }

theorem different_notation_succeeds : signatureFits source notationChange = true := by decide

private def collectionRule : GrammarRule where
  label := "Sequence"
  category := "T"
  params := [.simple "elements" (.collection .vec (.base "T"))]
  syntaxPattern := []

private def bareCollection : LanguageDef :=
  { source with terms := [collectionRule] }

private def wrappedCollection : LanguageDef :=
  { bareCollection with terms := bareCollection.terms.map fun rule =>
      { rule with collectionRepresentation := .wrapped } }

theorem identical_collection_signature_succeeds :
    signatureFits bareCollection bareCollection = true := by decide

theorem changed_collection_representation_refused :
    signatureFits bareCollection wrappedCollection = false := by decide

private def renamed : LanguageDef :=
  { source with terms := [nullary "Z" "zero", nullary "S" "one"] }

theorem renamed_identity_search_fails : signatureFits source renamed = false := by decide

private def validatedSource : ValidatedLanguageDef := ⟨source, by
  simp [source, nullary, LanguageDef.validate, LanguageDef.typeNames, TypeDecl.plain]⟩
private def validatedRenamed : ValidatedLanguageDef := ⟨renamed, by
  simp [renamed, source, nullary, LanguageDef.validate, LanguageDef.typeNames, TypeDecl.plain]⟩

private def renameSymbols : LanguageDefSymbolMap :=
  { LanguageDefSymbolMap.id with constructor := fun name =>
      if name = "A" then "Z" else if name = "B" then "S" else name }

/-- The failed identity search coexists with an explicit successful symbol map. -/
def renamedTyping : TypingMorphism validatedSource validatedRenamed where
  symbols := renameSymbols
  mapsTypes declaration member := by
    simpa [validatedSource, validatedRenamed, renamed, source,
      mapTypeDecl, renameSymbols, LanguageDefSymbolMap.id] using member
  mapsTerms rule member := by
    change rule ∈ [nullary "A" "a", nullary "B" "b"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · refine ⟨nullary "Z" "zero", ?_, rfl, rfl, rfl, rfl⟩
      exact List.Mem.head _
    · refine ⟨nullary "S" "one", ?_, rfl, rfl, rfl, rfl⟩
      exact List.Mem.tail _ (List.Mem.head _)

theorem unknown_identity_has_another_interpretation :
    signatureFits source renamed = false ∧
      Nonempty (TypingMorphism validatedSource validatedRenamed) :=
  ⟨renamed_identity_search_fails, ⟨renamedTyping⟩⟩

private def extraRule : RewriteRule :=
  { name := "added", typeContext := [], premises := [],
    left := .apply "A" [], right := .apply "B" [] }

private def extra : LanguageDef := { source with rewrites := [extraRule] }

theorem extra_signature_succeeds : signatureFits source extra = true := by decide

theorem extra_rules_include_source : source.rewrites.Sublist extra.rewrites := by
  exact List.nil_sublist _

/-- A successful inclusion can add an observable old-term step. -/
theorem inclusion_does_not_imply_reflection :
    rewriteStep source (.apply "A" []) = [] ∧
    rewriteStep extra (.apply "A" []) = [.apply "B" []] := by
  constructor
  · rfl
  · simp [rewriteStep, extra, extraRule, applyRule, matchPattern, applyRuleBindings,
      applyBindingsScoped, matchArgs]

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.IdentityInterface
