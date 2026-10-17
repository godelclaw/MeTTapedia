import Mettapedia.Computability.OriginalMachineTraceCode
import Mettapedia.Languages.HOLLight.EffectiveEvidenceCompilation
import Mettapedia.Languages.HOLLight.ProofDataEncoding

/-!
# Generated original-machine trace checking hosted by HOL Light

The finite transition descriptor generates an actual finite code. Bounded
evaluation evidence is extracted into the admitted twenty-three-rule source
calculus and compiled by the original shared HOL compiler. Arbitrary proofs in
the same finite HOL theory reflect the generated code's acceptance, hence every
original transition and its complete canonical endpoint.

Nested natural pairing and the source calculus's unary numerals can inflate
artifacts. Numeric fuel, trace transitions, packet bit lengths, extracted source
payload and emitted HOL bytes are accounted separately. No polynomial bound in
the original configuration or trace bytes is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.OriginalMachineTraceHosting

open Mettapedia.Computability
open OriginalMachineTraceEncoding
open OriginalMachineTraceCode
open Mettapedia.GSLT.LanguageDef.PartialRecursive (Judgment)
open Mettapedia.Languages.OpenTheory

def claim (descriptor : Descriptor) (request : Request) : Judgment :=
  .eval (Traces.checker descriptor) request.encode 1

def sourceCertificate (fuel : Nat) (descriptor : Descriptor) (request : Request) :=
  EffectiveEvidenceCompilation.sourceCertificate fuel (Traces.checker descriptor) request.encode 1

def compile (fuel : Nat) (descriptor : Descriptor) (request : Request) :
    Option ProofSystem.Certificate :=
  EffectiveEvidenceCompilation.compile fuel (Traces.checker descriptor) request.encode 1

theorem compile_iff_evidence (fuel : Nat) (descriptor : Descriptor) (request : Request) :
    (∃ certificate, compile fuel descriptor request = some certificate) ↔
      UniversalEffectiveEvidence.check (Traces.checker descriptor) request.encode 1 fuel = true :=
  EffectiveEvidenceCompilation.compile_iff_evidence fuel _ _ _

theorem compile_complete (fuel : Nat) (descriptor : Descriptor) (request : Request)
    (accepted : UniversalEffectiveEvidence.check (Traces.checker descriptor) request.encode 1 fuel = true) :
    ∃ certificate, compile fuel descriptor request = some certificate :=
  EffectiveEvidenceCompilation.compile_complete fuel _ _ _ accepted

/-- The actual original graph authority independently replays the emitted graph. -/
theorem compile_kernel_checked (fuel : Nat) (descriptor : Descriptor) (request : Request)
    {certificate : ProofSystem.Certificate} (emitted : compile fuel descriptor request = some certificate) :
    ∃ out, (ProofSystem.checker (InferenceHosting.policy EffectiveEvidenceHosting.universalRules)).check
        out certificate = true ∧ out.sequent.hyp = ∅ ∧
      out.sequent.concl = InferenceCompiler.compileClaim (claim descriptor request).pattern :=
  EffectiveEvidenceCompilation.compile_kernel_checked fuel _ _ _ emitted

theorem target_checked_iff (descriptor : Descriptor) (request : Request) :
    EffectiveEvidenceHosting.TargetChecked (claim descriptor request) ↔ request.check descriptor = true := by
  rw [EffectiveEvidenceHosting.target_checked_iff]
  change 1 ∈ (Traces.checker descriptor).eval request.encode ↔ _
  rw [← Part.eq_some_iff, Traces.accepted_iff]

/-- Refusal follows from the generated code, without a separate soundness callback. -/
theorem target_refused (descriptor : Descriptor) (request : Request)
    (rejected : request.check descriptor = false) :
    ¬ EffectiveEvidenceHosting.TargetChecked (claim descriptor request) := by
  rw [target_checked_iff, rejected]
  decide

theorem arbitrary_proof_checked (descriptor : Descriptor) (request : Request) {out : Theorem}
    (proof : Mettapedia.Logic.Derives
      (Rule (InferenceHosting.policy EffectiveEvidenceHosting.universalRules)) out)
    (hypotheses : out.sequent.hyp = ∅)
    (conclusion : out.sequent.concl = InferenceCompiler.compileClaim (claim descriptor request).pattern) :
    request.check descriptor = true := by
  have evaluated := EffectiveEvidenceHosting.arbitrary_proof_reflects
    (claim descriptor request) proof hypotheses conclusion
  exact (Traces.accepted_iff descriptor request).mp (Part.eq_some_iff.mpr evaluated)

def packetClaim (descriptor : Descriptor) (packet : Nat) : Judgment :=
  .eval (Traces.checker descriptor) packet 1

/-- Every numeric packet is in scope: malformed nested fields are refused by the
generated code itself, before replay. -/
theorem packet_target_checked_iff (descriptor : Descriptor) (packet : Nat) :
    EffectiveEvidenceHosting.TargetChecked (packetClaim descriptor packet) ↔
      Request.canonical packet = true ∧ (Request.decode packet).check descriptor = true := by
  rw [EffectiveEvidenceHosting.target_checked_iff]
  change 1 ∈ (Traces.checker descriptor).eval packet ↔ _
  rw [← Part.eq_some_iff, Traces.accepted_raw_iff]

theorem arbitrary_packet_proof_checked (descriptor : Descriptor) (packet : Nat) {out : Theorem}
    (proof : Mettapedia.Logic.Derives
      (Rule (InferenceHosting.policy EffectiveEvidenceHosting.universalRules)) out)
    (hypotheses : out.sequent.hyp = ∅)
    (conclusion : out.sequent.concl = InferenceCompiler.compileClaim (packetClaim descriptor packet).pattern) :
    Request.canonical packet = true ∧ (Request.decode packet).check descriptor = true := by
  have evaluated := EffectiveEvidenceHosting.arbitrary_proof_reflects
    (packetClaim descriptor packet) proof hypotheses conclusion
  exact (Traces.accepted_raw_iff descriptor packet).mp (Part.eq_some_iff.mpr evaluated)

def executionOfCheck {machine : Turing.FinTM2} (profile : FiniteProfile machine)
    (input : List (machine.Γ machine.k₀)) (output : List (machine.Γ machine.k₁))
    (trace : List Configuration) (count : Nat)
    (checked : (Request.mk (profile.encodeWord machine.k₀ input) (profile.encodeWord machine.k₁ output)
      trace count).check profile.descriptor = true) :
    Turing.TM2OutputsInTime machine input (some output) count := by
  have complete := (TraceCursor.accepts_iff profile.descriptor _ _ count trace).mp checked
  simpa only [complete.1] using profile.accepts_reflects input output trace complete.2

/-- Any original HOL proof of this claim earns the exact counted original execution,
including every register and scratch stack at the canonical halting endpoint. -/
def arbitrary_proof_execution {machine : Turing.FinTM2} (profile : FiniteProfile machine)
    (input : List (machine.Γ machine.k₀)) (output : List (machine.Γ machine.k₁))
    (trace : List Configuration) (count : Nat) {out : Theorem}
    (proof : Mettapedia.Logic.Derives
      (Rule (InferenceHosting.policy EffectiveEvidenceHosting.universalRules)) out)
    (hypotheses : out.sequent.hyp = ∅)
    (conclusion : out.sequent.concl = InferenceCompiler.compileClaim
      (claim profile.descriptor (Request.mk (profile.encodeWord machine.k₀ input)
        (profile.encodeWord machine.k₁ output) trace count)).pattern) :
    Turing.TM2OutputsInTime machine input (some output) count :=
  executionOfCheck profile input output trace count
    (arbitrary_proof_checked profile.descriptor _ proof hypotheses conclusion)

def arbitrary_graph_execution {machine : Turing.FinTM2} (profile : FiniteProfile machine)
    (input : List (machine.Γ machine.k₀)) (output : List (machine.Γ machine.k₁))
    (trace : List Configuration) (count : Nat) {out : Theorem} {certificate : ProofSystem.Certificate}
    (checked : (ProofSystem.checker (InferenceHosting.policy EffectiveEvidenceHosting.universalRules)).check
      out certificate = true)
    (hypotheses : out.sequent.hyp = ∅)
    (conclusion : out.sequent.concl = InferenceCompiler.compileClaim
      (claim profile.descriptor (Request.mk (profile.encodeWord machine.k₀ input)
        (profile.encodeWord machine.k₁ output) trace count)).pattern) :
    Turing.TM2OutputsInTime machine input (some output) count :=
  arbitrary_proof_execution profile input output trace count
    ((ProofSystem.checker_authority _).sound out certificate checked) hypotheses conclusion

/-- Input/output alignment is equality of decoded data with the original typed
words. The trace and count are earned from an arbitrary original HOL proof. -/
def arbitrary_packet_proof_execution {machine : Turing.FinTM2} (profile : FiniteProfile machine)
    (input : List (machine.Γ machine.k₀)) (output : List (machine.Γ machine.k₁))
    (packet : Nat) {out : Theorem}
    (inputAligned : (Request.decode packet).input = profile.encodeWord machine.k₀ input)
    (outputAligned : (Request.decode packet).output = profile.encodeWord machine.k₁ output)
    (proof : Mettapedia.Logic.Derives
      (Rule (InferenceHosting.policy EffectiveEvidenceHosting.universalRules)) out)
    (hypotheses : out.sequent.hyp = ∅)
    (conclusion : out.sequent.concl = InferenceCompiler.compileClaim
      (packetClaim profile.descriptor packet).pattern) :
    Turing.TM2OutputsInTime machine input (some output) (Request.decode packet).count := by
  have checked : (Request.decode packet).check profile.descriptor = true :=
    (arbitrary_packet_proof_checked profile.descriptor packet (out := out) proof hypotheses conclusion).2
  exact Traces.originalOfAlignedCheck profile input output (Request.decode packet)
    inputAligned.symm outputAligned.symm checked

def originalClaim {machine : Turing.FinTM2} (profile : FiniteProfile machine) (packet : Nat) : Judgment :=
  .eval (Traces.originalChecker profile.descriptor (profile.symbols machine.k₀)
    (profile.symbols machine.k₁)) packet 1

def compileOriginal {machine : Turing.FinTM2} (fuel : Nat) (profile : FiniteProfile machine) (packet : Nat) :
    Option ProofSystem.Certificate :=
  EffectiveEvidenceCompilation.compile fuel
    (Traces.originalChecker profile.descriptor (profile.symbols machine.k₀) (profile.symbols machine.k₁)) packet 1

theorem compileOriginal_iff_evidence {machine : Turing.FinTM2} (fuel : Nat) (profile : FiniteProfile machine)
    (packet : Nat) :
    (∃ certificate, compileOriginal fuel profile packet = some certificate) ↔
      UniversalEffectiveEvidence.check
        (Traces.originalChecker profile.descriptor (profile.symbols machine.k₀) (profile.symbols machine.k₁))
        packet 1 fuel = true :=
  EffectiveEvidenceCompilation.compile_iff_evidence fuel _ _ _

theorem compileOriginal_kernel_checked {machine : Turing.FinTM2} (fuel : Nat) (profile : FiniteProfile machine)
    (packet : Nat) {certificate : ProofSystem.Certificate}
    (emitted : compileOriginal fuel profile packet = some certificate) :
    ∃ out, (ProofSystem.checker (InferenceHosting.policy EffectiveEvidenceHosting.universalRules)).check
        out certificate = true ∧ out.sequent.hyp = ∅ ∧
      out.sequent.concl = InferenceCompiler.compileClaim (originalClaim profile packet).pattern :=
  EffectiveEvidenceCompilation.compile_kernel_checked fuel _ _ _ emitted

/-- Arbitrary numeric input earns both original typed words and the complete
counted execution. Ordinal validity is proved by the generated finite code. -/
def arbitrary_original_proof_execution {machine : Turing.FinTM2} (profile : FiniteProfile machine)
    (packet : Nat) {out : Theorem}
    (proof : Mettapedia.Logic.Derives
      (Rule (InferenceHosting.policy EffectiveEvidenceHosting.universalRules)) out)
    (hypotheses : out.sequent.hyp = ∅)
    (conclusion : out.sequent.concl = InferenceCompiler.compileClaim (originalClaim profile packet).pattern) :
    Traces.OriginalExecution profile packet :=
  Traces.originalExecutionFromCode profile packet (Part.eq_some_iff.mpr
    (EffectiveEvidenceHosting.arbitrary_proof_reflects (originalClaim profile packet)
      proof hypotheses conclusion))

def arbitrary_original_graph_execution {machine : Turing.FinTM2} (profile : FiniteProfile machine)
    (packet : Nat) {out : Theorem} {certificate : ProofSystem.Certificate}
    (checked : (ProofSystem.checker (InferenceHosting.policy EffectiveEvidenceHosting.universalRules)).check
      out certificate = true)
    (hypotheses : out.sequent.hyp = ∅)
    (conclusion : out.sequent.concl = InferenceCompiler.compileClaim (originalClaim profile packet).pattern) :
    Traces.OriginalExecution profile packet :=
  arbitrary_original_proof_execution profile packet
    ((ProofSystem.checker_authority _).sound out certificate checked) hypotheses conclusion

def compiled_original_execution {machine : Turing.FinTM2} (fuel : Nat) (profile : FiniteProfile machine)
    (packet : Nat) {certificate : ProofSystem.Certificate}
    (emitted : compileOriginal fuel profile packet = some certificate) : Traces.OriginalExecution profile packet :=
  Traces.originalExecutionFromCode profile packet (Part.eq_some_iff.mpr
    (UniversalEffectiveEvidence.check_sound _ _ _ fuel
      (EffectiveEvidenceCompilation.compile_sound fuel _ _ _ emitted)))

theorem original_hosting_complete {machine : Turing.FinTM2} (profile : FiniteProfile machine) :
    (∃ packet, EffectiveEvidenceHosting.TargetChecked (originalClaim profile packet)) ↔
      ∃ input output, Nonempty (Turing.TM2Outputs machine input (some output)) := by
  rw [← Traces.originalChecker_complete profile]
  apply exists_congr
  intro packet
  rw [EffectiveEvidenceHosting.target_checked_iff]
  exact Part.eq_some_iff.symm

def compiled_execution {machine : Turing.FinTM2} (profile : FiniteProfile machine)
    (input : List (machine.Γ machine.k₀)) (output : List (machine.Γ machine.k₁))
    (trace : List Configuration) (count fuel : Nat) {certificate : ProofSystem.Certificate}
    (emitted : compile fuel profile.descriptor
      (Request.mk (profile.encodeWord machine.k₀ input) (profile.encodeWord machine.k₁ output)
        trace count) = some certificate) :
    Turing.TM2OutputsInTime machine input (some output) count :=
  Traces.originalExecution profile input output trace count fuel
    (EffectiveEvidenceCompilation.compile_sound fuel _ _ _ emitted)

/-- Generated source proofs and arbitrary target proofs have the same original
execution domain; this statement also quantifies over all supplied traces. -/
theorem original_execution_iff {machine : Turing.FinTM2} (profile : FiniteProfile machine)
    (input : List (machine.Γ machine.k₀)) (output : List (machine.Γ machine.k₁)) :
    (∃ trace count, EffectiveEvidenceHosting.TargetChecked
      (claim profile.descriptor (Request.mk (profile.encodeWord machine.k₀ input)
        (profile.encodeWord machine.k₁ output) trace count))) ↔
      Nonempty (Turing.TM2Outputs machine input (some output)) := by
  rw [← Traces.original_iff profile input output]
  exact exists_congr fun trace => exists_congr fun count =>
    (EffectiveEvidenceHosting.evidence_iff_target _ _ _).symm

theorem compiled_iff_original {machine : Turing.FinTM2} (profile : FiniteProfile machine)
    (input : List (machine.Γ machine.k₀)) (output : List (machine.Γ machine.k₁)) :
    (∃ trace count fuel certificate, compile fuel profile.descriptor
      (Request.mk (profile.encodeWord machine.k₀ input) (profile.encodeWord machine.k₁ output)
        trace count) = some certificate) ↔ Nonempty (Turing.TM2Outputs machine input (some output)) := by
  rw [← Traces.original_iff profile input output]
  exact exists_congr fun trace => exists_congr fun count => exists_congr fun fuel =>
    compile_iff_evidence fuel profile.descriptor _

structure SizeAccount where
  machine : Traces.SizeAccount
  extraction : EffectiveEvidenceCompilation.PayloadAccount
  holReceipts : Nat
  holSymbols : Nat
  deriving Repr

/-- Sizes are obtained from the actual extractor and emitted certificate. This
is an artifact account, not an extraction clock or a polynomial trace-byte bound. -/
def sizeAccount (fuel : Nat) (descriptor : Descriptor) (request : Request) : Option SizeAccount := do
  let extraction ← EffectiveEvidenceCompilation.payloadAccount fuel (Traces.checker descriptor) request.encode 1
  let certificate ← compile fuel descriptor request
  return {
    machine := Traces.sizeAccount descriptor request fuel
    extraction := extraction
    holReceipts := certificate.1.length
    holSymbols := (ProofDataEncoding.encodeCertificate certificate).length }

end Mettapedia.Languages.HOLLight.OriginalMachineTraceHosting
