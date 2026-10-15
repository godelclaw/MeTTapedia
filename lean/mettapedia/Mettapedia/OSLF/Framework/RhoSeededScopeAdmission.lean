import Mettapedia.OSLF.Framework.RhoSeededScopeReceipts
import Mettapedia.OSLF.Syntax.RhoIntrinsicSealedCanonical

/-!
# Seeded scopes have actual authored closed rho names

Each retained derivation constructs a sorted raw source term with a proved
quotation-safety check. Its equation class is the derivation's readout.
Consequently every member of the seeded scope lies in the earned sealed
carrier, and its independently authored canonical name decodes to precisely
the supplied source class. This is a static admission comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoSeededScopeReceipts

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoSchema.IntrinsicEncoding RhoIntrinsicReadback RhoCanonicalNamePairs
open RhoSeededScopeStages RhoSeededScopeInterpretation RhoSeededScopeParser

def Derivation.term : Derivation → Term sig [] Srt.nm
  | .nullSeed => quoteRaw null
  | .outputSeed => quoteRaw RhoSourceOutputPredicate.output
  | .pair first second => quoteRaw (parallel (dropRaw first.term) (dropRaw second.term))

theorem Derivation.project_term (derivation : Derivation) :
    project derivation.term = derivation.readout := by
  induction derivation with
  | nullSeed => rfl
  | outputSeed => rfl
  | pair first second firstIH secondIH =>
    change combine (project first.term) (project second.term) = combine first.readout second.readout
    rw [firstIH, secondIH]

theorem Derivation.term_safe (derivation : Derivation) :
    ∀ level, intrinsicQuoteSafe level derivation.term = true := by
  induction derivation with
  | nullSeed => intro level; rfl
  | outputSeed => intro level; rfl
  | pair first second firstIH secondIH =>
    intro level
    simp [Derivation.term, quoteRaw, parallel, dropRaw,
      intrinsicQuoteSafe, intrinsicQuoteSafeArgs, firstIH, secondIH]

theorem Derivation.has_safe_representative (derivation : Derivation) :
    HasQuoteSafeRepresentative derivation.readout :=
  ⟨derivation.term, derivation.project_term, derivation.term_safe 0⟩

theorem receipt_has_safe_representative (name : Name []) (receipt : Receipt name) :
    HasQuoteSafeRepresentative name := by
  rw [← receipt.property]
  exact receipt.val.has_safe_representative

theorem scope_has_safe_representative {name : Name []} (member : finiteScope name) :
    HasQuoteSafeRepresentative name := by
  obtain ⟨limit, admitted⟩ := member
  obtain ⟨actual, readout, _⟩ := stage_depth_complete limit admitted
  have present : (recognize (encodeEquationClass name)).isSome := by
    have same := recognize_depth (encodeEquationClass name)
    cases recognized : recognize (encodeEquationClass name) with
    | none => simp [recognized, readout] at same
    | some derivation => rfl
  let derivation := (recognize (encodeEquationClass name)).get present
  have decoded : recognize (encodeEquationClass name) = some derivation := (Option.some_get present).symm
  exact receipt_has_safe_representative name ⟨derivation, recognize_class_readout decoded⟩

def authoredReceipt (name : Name []) (receipt : Receipt name) : AuthoredCanonicalCarrier Srt.nm :=
  authoredClosedClassEquiv Srt.nm ⟨name, receipt_has_safe_representative name receipt⟩

theorem authoredReceipt_pattern (name : Name []) (receipt : Receipt name) :
    (authoredReceipt name receipt).val.val = encodeEquationClass name :=
  authoredClosedClassEquiv_pattern Srt.nm ⟨name, receipt_has_safe_representative name receipt⟩

theorem authoredReceipt_decodes (name : Name []) (receipt : Receipt name) :
    ((authoredClosedClassEquiv Srt.nm).symm (authoredReceipt name receipt)).val = name := by
  exact congrArg Subtype.val ((authoredClosedClassEquiv Srt.nm).symm_apply_apply
    ⟨name, receipt_has_safe_representative name receipt⟩)

end Mettapedia.OSLF.Framework.RhoSeededScopeReceipts
