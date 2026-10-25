import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeCostLayerReceiptPolicyAdmission
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.CostElaborationKeyTransport

/-!
# Language-independent cost, receipt and replay interface

This import gate exposes the candidate-facing Cost boundary without selecting a
concrete language:

* proof-relevant cost layer operational schedules and chronological receipts;
* `WorkSpan` as a valuation of retained execution evidence;
* policy-relative cache and replay keys;
* the cost-layer iteration information order and SemanticService admission boundary; and
* displayed transport of compact policy keys.

A consumer of this module may state scheduling, metering, receipt, cache, and
replay obligations for any `Cost.Layer`.  Concrete inhabitants and
language-specific counterexamples belong in separate annexes.
-/
