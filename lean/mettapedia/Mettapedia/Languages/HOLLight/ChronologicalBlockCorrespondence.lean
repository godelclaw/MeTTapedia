import Mettapedia.Languages.HOLLight.RelocatedCertificateInsertion
import Mettapedia.Languages.HOLLight.ChronologicalDriver

/-!
# Controller extensions and the original physical block path

The controller extends its proof book through original graph replay. The
physical block path computes relocation, parses its emitted certificate and
appends receipts. These two independently defined operations have the same
certificate readout for an admitted descriptor image. Earlier checked claims
retain their original addresses and remain independently kernel-checkable.

This is a block-operation correspondence. Realizing the task scheduler and
installing every updated physical cache are further driver obligations.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.ChronologicalBlockCorrespondence

open Turing
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Computability.WordTemplateMachine
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.OpenTheory
open Mettapedia.Logic.DerivationGraph
open ProofExecution ProofDataEncoding ChronologicalDriver
open FirstOrder.InferenceTranslation InferenceHosting

variable (definition : ValidatedCalculusLanguageDef)

/-- The smart extension's dependent proof fields are earned by actual replay;
erasing them recovers the exact result of the original emitter operation. -/
theorem extension_emitted {before : Prefix definition}
    (roots : List Nat) (certificate : ProofSystem.Certificate)
    {extension : Extension definition before}
    (computed : extend? definition before roots certificate = some extension) :
    GraphExpansion.emitBlock (policy (inferenceRules definition.1)) roots certificate before.val =
      some (extension.after.val, extension.root) := by
  unfold extend? at computed
  split at computed
  · cases computed
  · rename_i after root emitted
    have same := congrArg (fun ext : Extension definition before => (ext.after.val, ext.root))
      (Option.some.inj computed)
    exact emitted.trans (congrArg some same)

/-- Physical relocation, parsing and receipt insertion return exactly the
certificate published by the successful original controller extension. -/
theorem run_extension {arity premiseCount : Nat} (internalCount : Nat)
    (descriptor : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount descriptor)
    (receipts : List Receipt) (payload : Fin arity → List Binary.Alphabet)
    (roots : Fin premiseCount → Nat)
    (aligned : RelocatedCertificateInsertion.Aligned descriptor receipts payload)
    {before : Prefix definition} {extension : Extension definition before}
    (computed : extend? definition before (List.ofFn roots) (receipts, descriptor.2) = some extension)
    {word : List Binary.Alphabet}
    (finished : TM2Outputs (RelocatedCertificateInsertion.machine premiseCount internalCount descriptor safe)
      (RelocatedCertificateInsertion.inputWire payload roots before.val.cache.size
        before.val.receipts.toList) (some word)) :
    decodeCertificate word = some (GraphExpansion.finish extension.after.val extension.root) ∧
      ∃ conclusion, extension.after.val.cache[extension.root]? = some conclusion ∧
        (ProofSystem.checker (policy (inferenceRules definition.1))).check conclusion
          (GraphExpansion.finish extension.after.val extension.root) = true := by
  have emitted := extension_emitted definition (List.ofFn roots) (receipts, descriptor.2) computed
  have decoded := RelocatedCertificateInsertion.run_decodes internalCount descriptor safe
    receipts payload roots before.val.cache.size before.val.receipts.toList aligned finished
  obtain ⟨receiptImage, rootImage⟩ := GraphExpansion.emitBlock_expanded emitted
  have exactReadout : decodeCertificate word =
      some (GraphExpansion.finish extension.after.val extension.root) := by
    simpa only [GraphExpansion.finish, receiptImage, rootImage] using decoded
  obtain ⟨checked, ⟨conclusion, found⟩, _⟩ :=
    GraphExpansion.emitBlock_preserves_checked before.property emitted
  exact ⟨exactReadout, conclusion, found,
    (ProofSystem.checker_check_iff _ _ _).mpr ⟨extension.after.val.cache, checked, found⟩⟩

/-- Equal-valued occurrences retain their positions in the actual controller
book, including all witness and origin payloads carried through relocation. -/
theorem run_extension_occurrences {arity premiseCount : Nat} (internalCount : Nat)
    (descriptor : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount descriptor)
    (receipts : List Receipt) (payload : Fin arity → List Binary.Alphabet)
    (roots : Fin premiseCount → Nat)
    (aligned : RelocatedCertificateInsertion.Aligned descriptor receipts payload)
    {before : Prefix definition} {extension : Extension definition before}
    (computed : extend? definition before (List.ofFn roots) (receipts, descriptor.2) = some extension)
    {word : List Binary.Alphabet} {certificate : ProofSystem.Certificate}
    (finished : TM2Outputs (RelocatedCertificateInsertion.machine premiseCount internalCount descriptor safe)
      (RelocatedCertificateInsertion.inputWire payload roots before.val.cache.size
        before.val.receipts.toList) (some word))
    (decoded : decodeCertificate word = some certificate) :
    certificate.1 = extension.after.val.receipts.toList ∧
      certificate.2 = extension.root ∧
      certificate.1.map (fun receipt => (receipt.witness, receipt.origin)) =
        before.val.receipts.toList.map (fun receipt => (receipt.witness, receipt.origin)) ++
          receipts.map (fun receipt => (receipt.witness, receipt.origin)) := by
  have same := Option.some.inj (decoded.symm.trans
    (run_extension definition internalCount descriptor safe receipts payload roots
      aligned computed finished).1)
  subst certificate
  have emitted := extension_emitted definition (List.ofFn roots) (receipts, descriptor.2) computed
  obtain ⟨receiptImage, _⟩ := GraphExpansion.emitBlock_expanded emitted
  refine ⟨rfl, rfl, ?_⟩
  simp only [GraphExpansion.finish, receiptImage, List.map_append]
  congr 1
  simp only [GraphExpansion.expandBlock, List.map_map,
    Function.comp_def, Node.relocate]

/-- Old controller claims continue to select their exact theorem in the
extended book. Their validity follows from original replay, not copying. -/
theorem saved_claim_authorized {before : Prefix definition}
    (roots : List Nat) (certificate : ProofSystem.Certificate)
    {extension : Extension definition before}
    (computed : extend? definition before roots certificate = some extension)
    (claim : Claim definition before) :
    extension.after.val.cache[claim.root]? = some claim.out ∧
      (ProofSystem.checker (policy (inferenceRules definition.1))).check claim.out
        (GraphExpansion.finish extension.after.val claim.root) = true := by
  have emitted := extension_emitted definition roots certificate computed
  obtain ⟨checked, _, kept⟩ := GraphExpansion.emitBlock_preserves_checked before.property emitted
  have retained := kept claim.root claim.out claim.found
  exact ⟨retained,
    (ProofSystem.checker_check_iff _ _ _).mpr ⟨extension.after.val.cache, checked, retained⟩⟩

end Mettapedia.Languages.HOLLight.ChronologicalBlockCorrespondence
