import Mettapedia.Languages.HOLLight.MeTTa.InferenceSchedule
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativePeTTaConfigurations

/-!
# Complete authored HOL inference plans have native typed execution paths

The actual quoted replay loop is transported into the existing configuration
graph. This certifies execution of the retained program, separately from a
native term inhabiting the guest's proposition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLSourceReplay

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.HOLLight.MeTTa
open InferenceSchedule CacheAuthorization
open NativePeTTaConfigurations (encode)

/-- Arbitrary admitted finite primitive plans execute as one complete native
state path, preserving the earned final cache and exact receipt count. -/
theorem plan_path (frame : Frame) {cache : Cache} {receipts : List ReceiptKeys.Entry} {length : Nat}
    (plan : Plan frame cache receipts length) (valid : Valid frame.policy frame.world cache)
    (state : Effects.State) (names : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    ∃ (afterCache : Cache) (afterReceipts : List ReceiptKeys.Entry) (commands : List SourceReplay.Command)
      (finalNames : List String),
      commands.length = length ∧ afterReceipts.length = receipts.length + length ∧
      Valid frame.policy frame.world afterCache ∧
      (NativePeTTaConfigurations.theory program).MultiStep
        (encode
          { state := state,
            control := .evaluate (SourceReplay.environment (frame.source cache receipts) commands)
              (.expression [.symbol "hol-light:run-from", .var "state", .var "commands"])} names)
        (encode (Eval.finished state [.expression [.symbol "Some", frame.source afterCache afterReceipts]] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail state [] ∧
      (∀ name, name ∉ finalNames → state.cells name = none) := by
  obtain ⟨afterCache, afterReceipts, commands, count, receiptCount, authorized, executed⟩ :=
    authored_plan_returns frame plan valid state
  obtain ⟨finalNames, path, retained, support⟩ :=
    NativePeTTaConfigurations.path_lifts executed names vacant covers
  exact ⟨afterCache, afterReceipts, commands, finalNames, count, receiptCount, authorized, path, retained, support⟩

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeHOLSourceReplay
