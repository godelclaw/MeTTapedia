import Mettapedia.Logic.ProofSearch.Planning
import Mettapedia.Logic.ProofSearch.CertificateBounds
import Mettapedia.GSLT.LanguageDef.ResourceExecution
import Mettapedia.Computability.StackMachineSpaceGrowth

/-!
# Executed transport of successful proof searches

The existing proof-plan `Stage` retains the actual producer execution and its
accepted certificate. Its discovery cost is that execution's step count.
Following a search with an operational compiler executes both machines and
the original physical word handoff. The polynomial theorem requires bounds
on discovery and the complete produced packet, including the configuration.
When the producer's input and actual discovery time are bounded, the packet
bound follows from that machine's syntactic capacity to push output cells.

Reverse search additionally needs the original translation's `Extractor` and
a machine implementing it on complete packets. Scope reflection alone does
not provide such a machine. An extraction packet retains the source query
alongside the target proof; producing that physical packet is an obligation
of the preceding search or query adapter.

These are conditional successful-search transport theorems. They do not infer
automatizability relative to the shortest target proof from forward compilation:
that requires efficiently extracting arbitrary target proofs and comparing
their complete encoded sizes. Exhaustion and refusal remain separate from
refutation of the independently authored scope.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ProofSearch.SearchTransport

open Mettapedia.GSLT.LanguageDef
open SemanticEvidence HeterogeneousTheory ResourceTranslation ProofSystems
open Mettapedia.Computability
open Turing Polynomial

variable {SK TK Γ Δ : Type} [Fintype Γ] [Fintype Δ]
    {S : TheoryFamily SK} {T : TheoryFamily TK}
    {SA : AuthorityContract S} {TA : AuthorityContract T}
    {se : Computability.Encoding (Packet SA) Γ}
    {te : Computability.Encoding (Packet TA) Δ}

/-- The existing evidence-bearing stage, instantiated by a real producer run.
The accepted packet includes its original theory configuration and proof. -/
def successfulStage (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (encoding : Computability.Encoding (Packet SA) Γ) :
    Stage (List (producer.Γ producer.k₀)) (Packet SA) where
  Evidence input packet := TM2Outputs producer input
    (some ((encoding.encode packet).map producerOutput.symm)) ×
      PLift (checkPacket SA packet = true)

/-- Charge exactly the discovery execution, rather than a declared search clock. -/
def discoveryCost (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (encoding : Computability.Encoding (Packet SA) Γ) :
    Stage.Cost (successfulStage producer producerOutput encoding) Nat where
  charge evidence := evidence.1.steps

omit [Fintype Γ] in
theorem successfulStage_scope (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (encoding : Computability.Encoding (Packet SA) Γ)
    {input : List (producer.Γ producer.k₀)} {packet : Packet SA}
    (evidence : (successfulStage producer producerOutput encoding).Evidence input packet) :
    S.Scope packet.1 packet.2.1 :=
  (SA.scopeAuthority _).sound _ _ evidence.2.down

/-! ## Execute a producer followed by an implemented packet transformation -/

/-- Specialize the original sequential machine; no alternative transition
system or freely chosen clock is introduced. -/
noncomputable def followingMachine {Input Output : Type} [Inhabited Γ]
    {inputEncoding : Input → List Γ} {outputEncoding : Output → List Δ}
    {transform : Input → Output} (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (implementation : TM2ComputableInPolyTime inputEncoding outputEncoding transform) : FinTM2 := by
  letI : Fintype (producer.Γ producer.k₁) := Fintype.ofEquiv Γ producerOutput.symm
  letI : Inhabited (producer.Γ producer.k₁) := ⟨producerOutput.symm default⟩
  exact StackMachineComposition.machine producer implementation.tm
    (producerOutput.trans implementation.inputAlphabet.symm)

omit [Fintype Δ] in
/-- Finite control does not suffice if a scratch cell can hide an unbounded
term. Both phases must have finite alphabets on every stack. -/
theorem following_finiteAlphabet {Input Output : Type} [Inhabited Γ]
    {inputEncoding : Input → List Γ} {outputEncoding : Output → List Δ}
    {transform : Input → Output} (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (implementation : TM2ComputableInPolyTime inputEncoding outputEncoding transform)
    (producerFinite : ∀ key, Finite (producer.Γ key))
    (implementationFinite : ∀ key, Finite (implementation.tm.Γ key)) :
    ∀ key, Finite ((followingMachine producer producerOutput implementation).Γ key) := by
  intro key
  change Finite (StackMachineComposition.Alphabet producer implementation.tm key)
  cases key with
  | none => exact producerFinite _
  | some key => cases key with
    | inl key => exact producerFinite key
    | inr key => exact implementationFinite key

set_option backward.isDefEq.respectTransparency false in
/-- A partial producer suffices: only the actual successful run is needed.
The bound includes both passes over the full intermediate packet. -/
noncomputable def following_outputs {Input Output : Type} [Inhabited Γ]
    {inputEncoding : Input → List Γ} {outputEncoding : Output → List Δ}
    {transform : Input → Output} (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (implementation : TM2ComputableInPolyTime inputEncoding outputEncoding transform)
    (input : List (producer.Γ producer.k₀)) (packet : Input) (discovery : Nat)
    (produced : TM2OutputsInTime producer input
      (some ((inputEncoding packet).map producerOutput.symm)) discovery) :
    TM2OutputsInTime (followingMachine producer producerOutput implementation) input
      (some ((outputEncoding (transform packet)).map implementation.outputAlphabet.symm))
      (discovery + 2 * (inputEncoding packet).length + 2 +
        implementation.time.eval (inputEncoding packet).length) := by
  letI : Fintype (producer.Γ producer.k₁) := Fintype.ofEquiv Γ producerOutput.symm
  letI : Inhabited (producer.Γ producer.k₁) := ⟨producerOutput.symm default⟩
  let bridge := producerOutput.trans implementation.inputAlphabet.symm
  have transformed := implementation.outputsFun packet
  change TM2OutputsInTime implementation.tm
    ((inputEncoding packet).map implementation.inputAlphabet.symm)
    (some ((outputEncoding (transform packet)).map implementation.outputAlphabet.symm)) _
      at transformed
  have handoff : ((inputEncoding packet).map producerOutput.symm).map bridge =
      (inputEncoding packet).map implementation.inputAlphabet.symm := by
    simp [bridge, List.map_map, Function.comp_def]
  rw [← handoff] at transformed
  have joined := StackMachineComposition.outputs producer implementation.tm bridge input
    ((inputEncoding packet).map producerOutput.symm)
    ((outputEncoding (transform packet)).map implementation.outputAlphabet.symm)
    _ _ produced transformed
  convert joined using 1 <;> first | rfl | simp only [List.length_map]

omit [Fintype Δ] in
/-- The polynomial account bounds the original joined execution. Packet size
is an explicit hypothesis, so a large discovered proof is not silently free. -/
theorem following_polynomial {Index Input Output : Type} [Inhabited Γ]
    {inputEncoding : Input → List Γ} {outputEncoding : Output → List Δ}
    {transform : Input → Output} (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (implementation : TM2ComputableInPolyTime inputEncoding outputEncoding transform)
    (inputs : Index → List (producer.Γ producer.k₀)) (packets : Index → Input)
    (discovery : Index → Nat)
    (runs : ∀ index, TM2OutputsInTime producer (inputs index)
      (some ((inputEncoding (packets index)).map producerOutput.symm)) (discovery index))
    (resources : Index → Nat) (discoveryBound : PolyBoundedBy discovery resources)
    (packetBound : PolyBoundedBy (fun index => (inputEncoding (packets index)).length) resources) :
    PolyBoundedBy (fun index => (following_outputs producer producerOutput implementation
      (inputs index) (packets index) (discovery index) (runs index)).steps) resources := by
  apply PolyBoundedBy.of_le (fun index =>
    (following_outputs producer producerOutput implementation
      (inputs index) (packets index) (discovery index) (runs index)).steps_le_m)
  have translationBound : PolyBoundedBy
      (fun index => implementation.time.eval (inputEncoding (packets index)).length) resources :=
    (show PolyBoundedBy (fun index => implementation.time.eval
      (inputEncoding (packets index)).length)
      (fun index => (inputEncoding (packets index)).length) from
      ⟨implementation.time, fun _ => le_rfl⟩).trans packetBound
  exact ((discoveryBound.add ((PolyBoundedBy.const 2 _).mul packetBound)).add
    (PolyBoundedBy.const 2 _)).add translationBound

omit [Fintype Γ] in
/-- Writing the discovered packet is charged by the actual producer run.
The command's complete push count, rather than an assumed one-cell step,
bounds the output, including its original configuration and proof fields. -/
theorem produced_packet_length {Input : Type} {inputEncoding : Input → List Γ}
    (producer : FinTM2) (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (input : List (producer.Γ producer.k₀)) (packet : Input) (discovery : Nat)
    (run : TM2OutputsInTime producer input
      (some ((inputEncoding packet).map producerOutput.symm)) discovery) :
    (inputEncoding packet).length ≤ input.length +
      StackMachineSpaceGrowth.machinePushBound producer * discovery := by
  simpa only [List.length_map] using StackMachineSpaceGrowth.output_length_le producer run

omit [Fintype Γ] in
/-- Input length and executed discovery time already supply a polynomial bound
on complete produced packets. No separate packet-size premise is required. -/
theorem produced_packet_polynomial {Index Input : Type} {inputEncoding : Input → List Γ}
    (producer : FinTM2) (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (inputs : Index → List (producer.Γ producer.k₀)) (packets : Index → Input)
    (discovery : Index → Nat)
    (runs : ∀ index, TM2OutputsInTime producer (inputs index)
      (some ((inputEncoding (packets index)).map producerOutput.symm)) (discovery index))
    (resources : Index → Nat)
    (inputBound : PolyBoundedBy (fun index => (inputs index).length) resources)
    (discoveryBound : PolyBoundedBy discovery resources) :
    PolyBoundedBy (fun index => (inputEncoding (packets index)).length) resources := by
  apply PolyBoundedBy.of_le (fun index => produced_packet_length producer producerOutput
    (inputs index) (packets index) (discovery index) (runs index))
  exact inputBound.add
    ((PolyBoundedBy.const (StackMachineSpaceGrowth.machinePushBound producer) _).mul discoveryBound)

omit [Fintype Δ] in
/-- Successful producer runs with polynomial input and discovery bounds can
be followed by an implemented packet transformation at polynomial cost. -/
theorem following_polynomial_of_run_bounds {Index Input Output : Type} [Inhabited Γ]
    {inputEncoding : Input → List Γ} {outputEncoding : Output → List Δ}
    {transform : Input → Output} (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (implementation : TM2ComputableInPolyTime inputEncoding outputEncoding transform)
    (inputs : Index → List (producer.Γ producer.k₀)) (packets : Index → Input)
    (discovery : Index → Nat)
    (runs : ∀ index, TM2OutputsInTime producer (inputs index)
      (some ((inputEncoding (packets index)).map producerOutput.symm)) (discovery index))
    (resources : Index → Nat)
    (inputBound : PolyBoundedBy (fun index => (inputs index).length) resources)
    (discoveryBound : PolyBoundedBy discovery resources) :
    PolyBoundedBy (fun index => (following_outputs producer producerOutput implementation
      (inputs index) (packets index) (discovery index) (runs index)).steps) resources :=
  following_polynomial producer producerOutput implementation inputs packets discovery runs
    resources discoveryBound (produced_packet_polynomial producer producerOutput inputs packets
      discovery runs resources inputBound discoveryBound)

/-! ## Forward compiler transport -/

/-- Every discovered accepted packet remains an accepted target packet. -/
theorem forward_accepted (compiler : OperationalTranslation SA TA se te)
    (packet : Packet SA) (accepted : checkPacket SA packet = true) :
    checkPacket TA (compiler.packet packet) = true :=
  compiler.preserves _ _ _ accepted

/-- Refusal transports only under exact replay, rather than mere preservation. -/
theorem forward_refused (compiler : OperationalTranslation SA TA se te)
    (exactReplay : compiler.toTranslation.Exact) (packet : Packet SA)
    (refused : checkPacket SA packet = false) :
    checkPacket TA (compiler.packet packet) = false := (exactReplay packet).trans refused

set_option backward.isDefEq.respectTransparency false in
/-- Transport the existing successful stage, retaining the computed proof and
the real combined discovery/compilation execution. -/
noncomputable def forwardEvidence [Inhabited Γ]
    (compiler : OperationalTranslation SA TA se te) (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    {input : List (producer.Γ producer.k₀)} {packet : Packet SA}
    (evidence : (successfulStage producer producerOutput se).Evidence input packet) :
    (successfulStage (followingMachine producer producerOutput compiler.realization)
      compiler.realization.outputAlphabet te).Evidence input (compiler.packet packet) := by
  have produced : TM2OutputsInTime producer input
      (some ((se.encode packet).map producerOutput.symm)) evidence.1.steps :=
    { toEvalsTo := evidence.1, steps_le_m := le_rfl }
  exact ⟨(following_outputs producer producerOutput compiler.realization
    input packet evidence.1.steps produced).toTM2Outputs,
      ⟨forward_accepted compiler packet evidence.2.down⟩⟩

theorem forward_discovery_bound [Inhabited Γ]
    (compiler : OperationalTranslation SA TA se te) (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    {input : List (producer.Γ producer.k₀)} {packet : Packet SA}
    (evidence : (successfulStage producer producerOutput se).Evidence input packet) :
    (discoveryCost (followingMachine producer producerOutput compiler.realization)
      compiler.realization.outputAlphabet te).charge
        (forwardEvidence compiler producer producerOutput evidence) ≤
      (discoveryCost producer producerOutput se).charge evidence +
        2 * (se.encode packet).length + 2 +
          compiler.realization.time.eval (se.encode packet).length := by
  exact (following_outputs producer producerOutput compiler.realization input packet
    evidence.1.steps { toEvalsTo := evidence.1, steps_le_m := le_rfl }).steps_le_m

/-- A uniform family of successful source searches transports with a polynomial
bound on the actual joined executions. The complete discovered packet must
also be polynomially bounded in the explicitly supplied resource parameter. -/
theorem forward_polynomial {Index : Type} [Inhabited Γ]
    (compiler : OperationalTranslation SA TA se te) (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (producerFinite : ∀ key, Finite (producer.Γ key))
    (inputs : Index → List (producer.Γ producer.k₀)) (packets : Index → Packet SA)
    (evidence : ∀ index,
      (successfulStage producer producerOutput se).Evidence (inputs index) (packets index))
    (resources : Index → Nat)
    (discoveryBound : PolyBoundedBy
      (fun index => (discoveryCost producer producerOutput se).charge (evidence index)) resources)
    (packetBound : PolyBoundedBy (fun index => (se.encode (packets index)).length) resources) :
    (∀ key, Finite ((followingMachine producer producerOutput compiler.realization).Γ key)) ∧
    (∀ index, checkPacket TA (compiler.packet (packets index)) = true) ∧
    PolyBoundedBy (fun index =>
      (discoveryCost (followingMachine producer producerOutput compiler.realization)
        compiler.realization.outputAlphabet te).charge
          (forwardEvidence compiler producer producerOutput (evidence index))) resources := by
  refine ⟨following_finiteAlphabet producer producerOutput compiler.realization
    producerFinite compiler.finiteAlphabet,
      (fun index => forward_accepted compiler _ (evidence index).2.down), ?_⟩
  exact following_polynomial producer producerOutput compiler.realization inputs packets
    (fun index => (evidence index).1.steps)
    (fun index => { toEvalsTo := (evidence index).1, steps_le_m := le_rfl })
    resources discoveryBound packetBound

/-- Forward successful-search transport with its packet bound derived from
the original input length and the actual discovery execution. -/
theorem forward_polynomial_of_run_bounds {Index : Type} [Inhabited Γ]
    (compiler : OperationalTranslation SA TA se te) (producer : FinTM2)
    (producerOutput : producer.Γ producer.k₁ ≃ Γ)
    (producerFinite : ∀ key, Finite (producer.Γ key))
    (inputs : Index → List (producer.Γ producer.k₀)) (packets : Index → Packet SA)
    (evidence : ∀ index,
      (successfulStage producer producerOutput se).Evidence (inputs index) (packets index))
    (resources : Index → Nat)
    (inputBound : PolyBoundedBy (fun index => (inputs index).length) resources)
    (discoveryBound : PolyBoundedBy
      (fun index => (discoveryCost producer producerOutput se).charge (evidence index)) resources) :
    (∀ key, Finite ((followingMachine producer producerOutput compiler.realization).Γ key)) ∧
    (∀ index, checkPacket TA (compiler.packet (packets index)) = true) ∧
    PolyBoundedBy (fun index =>
      (discoveryCost (followingMachine producer producerOutput compiler.realization)
        compiler.realization.outputAlphabet te).charge
          (forwardEvidence compiler producer producerOutput (evidence index))) resources :=
  forward_polynomial compiler producer producerOutput producerFinite inputs packets evidence
    resources discoveryBound (produced_packet_polynomial producer producerOutput inputs packets
      (fun index => (evidence index).1.steps)
      (fun index => { toEvalsTo := (evidence index).1, steps_le_m := le_rfl })
      resources inputBound discoveryBound)

/-! ## Efficient extraction is an additional obligation -/

/-- The original source query retained beside an arbitrary target proof of its
translated claim. This is packet data, not an inverse theory translation. -/
abbrev ExtractionPacket (translation : Translation SA TA) :=
  (kind : SK) × (S.Claim kind × TA.Certificate (translation.mapKind kind))

def targetExtractionPacket (translation : Translation SA TA)
    (packet : ExtractionPacket translation) : Packet TA :=
  ⟨translation.mapKind packet.1, translation.mapClaim packet.1 packet.2.1, packet.2.2⟩

def sourceExtractionPacket {translation : Translation SA TA}
    (extractor : translation.Extractor) (packet : ExtractionPacket translation) : Packet SA :=
  ⟨packet.1, packet.2.1, extractor.extract packet.1 packet.2.1 packet.2.2⟩

theorem extraction_accepted {translation : Translation SA TA}
    (extractor : translation.Extractor) (packet : ExtractionPacket translation)
    (accepted : checkPacket TA (targetExtractionPacket translation packet) = true) :
    checkPacket SA (sourceExtractionPacket extractor packet) = true :=
  extractor.accepted _ _ _ accepted

set_option backward.isDefEq.respectTransparency false in
/-- Actual reverse search transport. The premise is a machine implementing the
original extractor on the complete retained source query and target proof.
A merely existential source derivation cannot replace this premise. -/
noncomputable def reverseEvidence {Ε : Type} [Fintype Ε] [Inhabited Ε]
    {translation : Translation SA TA} (extractor : translation.Extractor)
    (extractionEncoding : Computability.Encoding (ExtractionPacket translation) Ε)
    (implementation : TM2ComputableInPolyTime extractionEncoding.encode se.encode
      (sourceExtractionPacket extractor))
    (producer : FinTM2) (producerOutput : producer.Γ producer.k₁ ≃ Ε)
    (input : List (producer.Γ producer.k₀)) (packet : ExtractionPacket translation)
    (discovery : Nat)
    (produced : TM2OutputsInTime producer input
      (some ((extractionEncoding.encode packet).map producerOutput.symm)) discovery)
    (accepted : checkPacket TA (targetExtractionPacket translation packet) = true) :
    (successfulStage (followingMachine producer producerOutput implementation)
      implementation.outputAlphabet se).Evidence input (sourceExtractionPacket extractor packet) :=
  ⟨(following_outputs producer producerOutput implementation
    input packet discovery produced).toTM2Outputs, ⟨extraction_accepted extractor packet accepted⟩⟩

omit [Fintype Γ] in
/-- The reverse polynomial search statement requires an actual extractor
implementation, finite scratch alphabets, and a proved bound on complete
extraction-packet bytes. Propositional reflection supplies none of these. -/
theorem reverse_polynomial {Index Ε : Type} [Fintype Ε] [Inhabited Ε]
    {translation : Translation SA TA} (extractor : translation.Extractor)
    (extractionEncoding : Computability.Encoding (ExtractionPacket translation) Ε)
    (implementation : TM2ComputableInPolyTime extractionEncoding.encode se.encode
      (sourceExtractionPacket extractor))
    (implementationFinite : ∀ key, Finite (implementation.tm.Γ key))
    (producer : FinTM2) (producerOutput : producer.Γ producer.k₁ ≃ Ε)
    (producerFinite : ∀ key, Finite (producer.Γ key))
    (inputs : Index → List (producer.Γ producer.k₀))
    (packets : Index → ExtractionPacket translation) (discovery : Index → Nat)
    (runs : ∀ index, TM2OutputsInTime producer (inputs index)
      (some ((extractionEncoding.encode (packets index)).map producerOutput.symm)) (discovery index))
    (accepted : ∀ index,
      checkPacket TA (targetExtractionPacket translation (packets index)) = true)
    (resources : Index → Nat) (discoveryBound : PolyBoundedBy discovery resources)
    (packetBound : PolyBoundedBy
      (fun index => (extractionEncoding.encode (packets index)).length) resources) :
    (∀ key, Finite ((followingMachine producer producerOutput implementation).Γ key)) ∧
    (∀ index, checkPacket SA (sourceExtractionPacket extractor (packets index)) = true) ∧
    PolyBoundedBy (fun index =>
      (discoveryCost (followingMachine producer producerOutput implementation)
        implementation.outputAlphabet se).charge
          (reverseEvidence extractor extractionEncoding implementation producer producerOutput
            (inputs index) (packets index) (discovery index) (runs index) (accepted index))) resources := by
  exact ⟨following_finiteAlphabet producer producerOutput implementation
      producerFinite implementationFinite,
    (fun index => extraction_accepted extractor _ (accepted index)),
    following_polynomial producer producerOutput implementation inputs packets discovery runs
      resources discoveryBound packetBound⟩

omit [Fintype Γ] in
/-- Reverse successful-search transport still requires the actual extractor
machine. Its complete retained-query packet bound can be derived from the
producer's input length and discovery time, rather than separately assumed. -/
theorem reverse_polynomial_of_run_bounds {Index Ε : Type} [Fintype Ε] [Inhabited Ε]
    {translation : Translation SA TA} (extractor : translation.Extractor)
    (extractionEncoding : Computability.Encoding (ExtractionPacket translation) Ε)
    (implementation : TM2ComputableInPolyTime extractionEncoding.encode se.encode
      (sourceExtractionPacket extractor))
    (implementationFinite : ∀ key, Finite (implementation.tm.Γ key))
    (producer : FinTM2) (producerOutput : producer.Γ producer.k₁ ≃ Ε)
    (producerFinite : ∀ key, Finite (producer.Γ key))
    (inputs : Index → List (producer.Γ producer.k₀))
    (packets : Index → ExtractionPacket translation) (discovery : Index → Nat)
    (runs : ∀ index, TM2OutputsInTime producer (inputs index)
      (some ((extractionEncoding.encode (packets index)).map producerOutput.symm)) (discovery index))
    (accepted : ∀ index,
      checkPacket TA (targetExtractionPacket translation (packets index)) = true)
    (resources : Index → Nat)
    (inputBound : PolyBoundedBy (fun index => (inputs index).length) resources)
    (discoveryBound : PolyBoundedBy discovery resources) :
    (∀ key, Finite ((followingMachine producer producerOutput implementation).Γ key)) ∧
    (∀ index, checkPacket SA (sourceExtractionPacket extractor (packets index)) = true) ∧
    PolyBoundedBy (fun index =>
      (discoveryCost (followingMachine producer producerOutput implementation)
        implementation.outputAlphabet se).charge
          (reverseEvidence extractor extractionEncoding implementation producer producerOutput
            (inputs index) (packets index) (discovery index) (runs index) (accepted index))) resources :=
  reverse_polynomial extractor extractionEncoding implementation implementationFinite
    producer producerOutput producerFinite inputs packets discovery runs accepted resources
    discoveryBound (produced_packet_polynomial producer producerOutput inputs packets discovery
      runs resources inputBound discoveryBound)

namespace Controls

/-- Source failure within a short finite search is compatible with an actual
longer certificate; it must not be transported as a refutation. -/
theorem exhausted_search_still_has_certificate :
    CertificateBounds.boundedSearch CertificateBounds.Controls.lengthChecker 2 1 = none ∧
      CertificateBounds.Controls.lengthChecker.check 2 [0, 0] = true := ⟨rfl, rfl⟩

/-- Existing exact forward replay does not supply arbitrary-proof extraction. -/
theorem exact_forward_can_lack_extraction :
    ResourceTranslation.Controls.inclusion.Exact ∧
      IsEmpty ResourceTranslation.Controls.inclusion.Extractor :=
  ⟨ResourceTranslation.Controls.inclusion_exact, ResourceTranslation.Controls.no_extractor⟩

end Controls

end Mettapedia.Logic.ProofSearch.SearchTransport
