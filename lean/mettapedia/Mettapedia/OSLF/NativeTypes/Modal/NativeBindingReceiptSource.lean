import Mettapedia.OSLF.NativeTypes.Modal.NativeAuthoredEventAction

/-!
# Every valid operational receipt has its actual authored source inhabitant

The independent firing judgment requires typed canonical object sources.
Its receipt therefore reconstructs an original contextual term with the exact
same source pattern, rather than asking the caller to supply that term.
Conversion preserves the full receipt payload. Arbitrary raw matching is not
claimed invariant under binder display normalization.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingReceiptSource

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise StructuralDescent
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage BindingSemanticAdmission
open NativeReceiptRechecking
open NativeBindingEventAction (bound)

variable {environment : Environment} {language : LanguageDef}

def source {context : List String} {sort : String} {pattern : Pattern}
    (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = FreeTypeContext.empty)
    (receipt : Execution.RootAnswer environment (bound context) (.base sort) pattern) :
    Source language context sort := by
  have sorted : OpenPatternWellSorted environment.language environment.free
      (bound context) (.base sort) pattern := by
    cases receipt.valid with
    | fire _ _ _ sourceTyped _ _ _ _ _ => exact sourceTyped
  refine ⟨pattern, ?_, sorted.2.2.1, sorted.2.1⟩
  rw [freeEmpty] at sorted
  exact GeneralLanguageTyping.type_transport grammar sorted.1

theorem source_canonical {context : List String} {sort : String} {pattern : Pattern}
    (receipt : Execution.RootAnswer environment (bound context) (.base sort) pattern) :
    pattern.hasCanonicalBinderMetadata = true := by
  cases receipt.valid with
  | fire _ _ _ sourceTyped _ _ _ _ _ => exact sourceTyped.2.1

noncomputable def term {context : List String} {sort : String} {pattern : Pattern}
    (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = FreeTypeContext.empty)
    (admitted : Admitted language) (labels : (language.terms.map (·.label)).Nodup)
    (receipt : Execution.RootAnswer environment (bound context) (.base sort) pattern) :
    Mettapedia.OSLF.Binding.Term (signature language) context sort :=
  (sourceEquiv admitted labels context sort).symm (source grammar freeEmpty receipt)

theorem term_read {context : List String} {sort : String} {pattern : Pattern}
    (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = FreeTypeContext.empty)
    (admitted : Admitted language) (labels : (language.terms.map (·.label)).Nodup)
    (receipt : Execution.RootAnswer environment (bound context) (.base sort) pattern) :
    toPattern (term grammar freeEmpty admitted labels receipt) = pattern :=
  congrArg Subtype.val ((sourceEquiv admitted labels context sort).apply_symm_apply
    (source grammar freeEmpty receipt))

noncomputable def point {context : List String} {sort : String} {pattern : Pattern}
    (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = FreeTypeContext.empty)
    (admitted : Admitted language) (labels : (language.terms.map (·.label)).Nodup)
    (receipt : Execution.RootAnswer environment (bound context) (.base sort) pattern) :
    NativeAuthoredEventAction.Point environment language context sort where
  source := term grammar freeEmpty admitted labels receipt
  receipt := NativeBindingEventAction.castReceipt (term_read grammar freeEmpty admitted labels receipt).symm receipt

theorem point_read {context : List String} {sort : String} {pattern : Pattern}
    (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = FreeTypeContext.empty)
    (admitted : Admitted language) (labels : (language.terms.map (·.label)).Nodup)
    (receipt : Execution.RootAnswer environment (bound context) (.base sort) pattern) :
    read (point grammar freeEmpty admitted labels receipt).receipt = read receipt :=
  NativeBindingEventAction.castReceipt_read _ _

theorem point_index {context : List String} {sort : String} {pattern : Pattern}
    (grammar : environment.language.terms = language.terms)
    (freeEmpty : environment.free = FreeTypeContext.empty)
    (admitted : Admitted language) (labels : (language.terms.map (·.label)).Nodup)
    (receipt : Execution.RootAnswer environment (bound context) (.base sort) pattern) :
    (point grammar freeEmpty admitted labels receipt).receipt.index = receipt.index :=
  congrArg Payload.index (point_read grammar freeEmpty admitted labels receipt)

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingReceiptSource
