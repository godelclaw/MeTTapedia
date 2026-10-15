import Mettapedia.OSLF.Syntax.RhoScopedFiniteSuccessors

/-!
# Finite rho outcomes do not erase authored firing receipts

Reflection ignores the continuation assignment declared by the common schema
signature. Infinitely many distinct actual assignments consequently inhabit
one endpoint-reading fibre. A separate communication control uses a name
bound underneath a quotation and executes by the original substitution rule.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoScopedReactionReceiptControls

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls RhoIntrinsicReadback
open RhoScopedInstanceReadout RhoScopedReactionReadout RhoScopedFiniteSuccessors
open RhoScopedParallelEvents RhoScopedParallelReactiveSystem RhoScopedParallelInventory
open RhoSchema.IntrinsicEncoding
open Mettapedia.OSLF.MeTTaIL.ScopedPattern

def spareContinuation : Nat → Term sig [Srt.nm] Srt.pr
  | 0 => null
  | count + 1 => parallel (outputRaw (.var .zero) null) (spareContinuation count)

theorem spareContinuation_count (count : Nat) : outputCount (spareContinuation count) = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [spareContinuation, parallel, outputRaw, null, outputCount, outputCountArgs,
        outputHeadCount, ih]
      omega

def authoredReceipt (count : Nat) : Receipt withReflection (.reflection (zero [])) :=
  ⟨⟨⟨.reflection, trivial⟩,
    RhoScopedInstanceReadout.reflection null (spareContinuation count)⟩, rfl⟩

theorem authoredReceipt_injective : Function.Injective authoredReceipt := by
  intro first second same
  have bodies := congrArg (fun receipt : Receipt withReflection (.reflection (zero [])) =>
    outputCount (receipt.val.2.body 0)) same
  change outputCount (spareContinuation first) = outputCount (spareContinuation second) at bodies
  simpa only [spareContinuation_count] using bodies

theorem actual_receipt_fibre_infinite : Infinite (Receipt withReflection (.reflection (zero []))) :=
  Infinite.of_injective authoredReceipt authoredReceipt_injective

theorem same_source_all_receipts (first second : Nat) :
    (authoredReceipt first).val.source = (authoredReceipt second).val.source := by
  rw [← rootReading_source, ← rootReading_source,
    (authoredReceipt first).property, (authoredReceipt second).property]

theorem same_target_all_receipts (first second : Nat) :
    (authoredReceipt first).val.target = (authoredReceipt second).val.target := by
  rw [← rootReading_target, ← rootReading_target,
    (authoredReceipt first).property, (authoredReceipt second).property]

def quotedBoundContinuation : Term sig [Srt.nm] Srt.pr :=
  dropRaw (quoteRaw (outputRaw (.var .zero) null))

def quotedBoundRoot : Root sourceRules core [] :=
  ⟨⟨.communication, trivial⟩,
    RhoScopedInstanceReadout.communication (quoteRaw null) null quotedBoundContinuation⟩

def quotedBoundTarget : Process [] :=
  project (dropRaw (quoteRaw (outputRaw (quoteRaw null) null)))

theorem quoted_bound_target_readout : quotedBoundRoot.target = quotedBoundTarget := by
  change project (ContextualRootEvents.Instance.target
    (RhoScopedInstanceReadout.communication (quoteRaw null) null quotedBoundContinuation)) = _
  rw [Communication.target_readout]
  rfl

theorem quoted_bound_input_not_sealed :
    binderSafeAt "NQuote" 0 (encodeEquationClass
      (inputClass (quote (zero [])) (project quotedBoundContinuation))) = false := by
  change binderSafeAt "NQuote" 0
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize
      (encodeTerm (inputRaw (quoteRaw null) quotedBoundContinuation))) = false
  decide +kernel

theorem actual_quoted_bound_outcome :
    quotedBoundTarget ∈ successors core quotedBoundRoot.source (zero []) := by
  have target := supplied_root_target_listed quotedBoundRoot.source (zero []) quotedBoundRoot
    (by simp only [leastLabel, tsub_self, write_zero])
  simpa only [reactionRemainder, tsub_self, write_zero, join_zero_right,
    quoted_bound_target_readout] using target

end Mettapedia.OSLF.Binding.RhoScopedReactionReceiptControls
