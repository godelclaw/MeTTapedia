import Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingNamedSource
import Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonical

/-!
# Original binder metadata alongside contextual semantic terms

An authored source may use arbitrary binder display names. An actual typed
alpha representative earns its source typing, and the source is retained
verbatim in a receipt; its semantic term is compared
with the source's alpha representative. All finite declared free contexts
and ambient bound contexts participate in the same construction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.WellSorted BindingSemanticAdmission
open BindingCarrierSemantics (FreeDeclarations freeContext openFree)

variable {language : LanguageDef}

def AuthoredTyping (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (pattern : Pattern) (type : TypeExpr) : Prop :=
  ∃ representative, HasType language free bound representative type ∧
    Pattern.AlphaEquiv pattern representative

theorem authoredTyping_of_typed {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr} (typed : HasType language free bound pattern type) :
    AuthoredTyping language free bound pattern type := ⟨pattern, typed, rfl⟩

theorem authoredTyping_canonical {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr}
    (typed : AuthoredTyping language free bound pattern type) :
    HasType language free bound pattern.eraseBinderMetadata type := by
  obtain ⟨representative, representativeTyped, equivalent⟩ := typed
  rw [show pattern.eraseBinderMetadata = representative.eraseBinderMetadata from equivalent]
  exact Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonical.typed_erase representativeTyped

abbrev AuthoredSource (language : LanguageDef) (declarations : FreeDeclarations)
    (context : List String) (sort : String) :=
  {pattern : Pattern // AuthoredTyping language (freeContext declarations)
      (Mettapedia.GSLT.Poly.BindingLanguage.typeContext context) pattern (.base sort) ∧
    isObjectPattern pattern = true}

def canonicalSource {declarations : FreeDeclarations} {context : List String} {sort : String}
    (source : AuthoredSource language declarations context sort) :
    NamedSource language declarations context sort :=
  ⟨source.val.eraseBinderMetadata,
    authoredTyping_canonical source.2.1,
    (Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonical.object_erase source.val).trans source.2.2,
    source.val.eraseBinderMetadata_hasCanonicalBinderMetadata⟩

noncomputable def encodeAuthored (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup) (declarations : FreeDeclarations)
    (context : List String) (sort : String)
    (source : AuthoredSource language declarations context sort) :
    Term (signature language) (context ++ declarations.map Prod.snd) sort :=
  encodeNamed admitted labels declarations context sort (canonicalSource source)

theorem encodeAuthored_readback (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup) (declarations : FreeDeclarations)
    (context : List String) (sort : String)
    (source : AuthoredSource language declarations context sort) :
    openFree context.length declarations
      (toPattern (encodeAuthored admitted labels declarations context sort source)) =
      source.val.eraseBinderMetadata :=
  encodeNamed_readback admitted labels declarations context sort (canonicalSource source)

structure AuthoredReceipt (language : LanguageDef) (declarations : FreeDeclarations)
    (context : List String) (sort : String) where
  source : AuthoredSource language declarations context sort
  term : Term (signature language) (context ++ declarations.map Prod.snd) sort
  readback : openFree context.length declarations (toPattern term) = source.val.eraseBinderMetadata

noncomputable def authoredReceipt (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup) (declarations : FreeDeclarations)
    (context : List String) (sort : String)
    (source : AuthoredSource language declarations context sort) :
    AuthoredReceipt language declarations context sort where
  source := source
  term := encodeAuthored admitted labels declarations context sort source
  readback := encodeAuthored_readback admitted labels declarations context sort source

theorem authoredReceipt_original (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup) (declarations : FreeDeclarations)
    (context : List String) (sort : String)
    (source : AuthoredSource language declarations context sort) :
    (authoredReceipt admitted labels declarations context sort source).source = source := rfl

theorem authoredReceipt_alpha_readout {declarations : FreeDeclarations}
    {context : List String} {sort : String}
    (receipt : AuthoredReceipt language declarations context sort) :
    Pattern.AlphaEquiv receipt.source.val
      (openFree context.length declarations (toPattern receipt.term)) := by
  rw [Pattern.AlphaEquiv, receipt.readback, Pattern.eraseBinderMetadata_idempotent]

theorem original_metadata_distinguishes_receipts {declarations : FreeDeclarations}
    {context : List String} {sort : String}
    (first second : AuthoredReceipt language declarations context sort)
    (different : first.source.val ≠ second.source.val) : first ≠ second := by
  intro same
  exact different (congrArg (fun receipt => receipt.source.val) same)

theorem alpha_sources_equal_semantic_terms (admitted : Admitted language)
    (labels : (language.terms.map (·.label)).Nodup) (declarations : FreeDeclarations)
    (context : List String) (sort : String)
    (first second : AuthoredSource language declarations context sort)
    (same : Pattern.AlphaEquiv first.val second.val) :
    encodeAuthored admitted labels declarations context sort first =
      encodeAuthored admitted labels declarations context sort second := by
  apply congrArg (encodeNamed admitted labels declarations context sort)
  exact Subtype.ext same

end Mettapedia.OSLF.NativeTypes.Generation.CurriedBindingLanguage
