import Mettapedia.GSLT.LanguageDef.HeterogeneousTheory
import Mettapedia.GSLT.LanguageDef.ProofSystemExecution

/-!
# Resource-aware translations of configured authorities

A packet contains the theory configuration, claim and certificate. Machine
bounds therefore include the configuration's encoded size, rather than hiding
a changing library in a fixed-theory constant. Configurations are the existing
`TheoryFamily` indices; this module does not introduce a second theory format.

Forward certificate transport, exact replay, reflection of arbitrary target
proofs, and executable extraction are separate obligations. In particular,
exact replay constrains the image of the compiler, not all target certificates.
The operational interface executes complete packets and composes through a
physical word handoff. Its unit is a TM2 statement step, not wall-clock time.
The encoding interface concerns encoded packets; malformed byte admission is
a further machine obligation and is not implied by this interface.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ResourceTranslation

open SemanticEvidence HeterogeneousTheory ProofSystems
open Turing Polynomial

/-- The configuration is data, alongside the claim and native certificate. -/
abbrev Packet {Kind : Type} {theory : TheoryFamily Kind}
    (authority : AuthorityContract theory) :=
  (kind : Kind) × (theory.Claim kind × authority.Certificate kind)

def checkPacket {Kind : Type} {theory : TheoryFamily Kind}
    (authority : AuthorityContract theory) (packet : Packet authority) : Bool :=
  (authority.checker packet.1).check packet.2.1 packet.2.2

/-- Certificate transport may depend on the claim as well as the configuration.
Its semantic map remains independent of the proof supplied to the compiler. -/
structure Translation {SourceKind TargetKind : Type}
    {source : TheoryFamily SourceKind} {target : TheoryFamily TargetKind}
    (sourceAuthority : AuthorityContract source)
    (targetAuthority : AuthorityContract target)
    extends TheoryTranslation source target where
  translate : ∀ kind, source.Claim kind → sourceAuthority.Certificate kind →
    targetAuthority.Certificate (mapKind kind)
  preserves : ∀ kind claim certificate,
    (sourceAuthority.checker kind).check claim certificate = true →
    (targetAuthority.checker (mapKind kind)).check
      (mapClaim kind claim) (translate kind claim certificate) = true

namespace Translation

variable {SK MK TK : Type}
    {S : TheoryFamily SK} {M : TheoryFamily MK} {T : TheoryFamily TK}
    {SA : AuthorityContract S} {MA : AuthorityContract M} {TA : AuthorityContract T}

def packet (f : Translation SA TA) (p : Packet SA) : Packet TA :=
  ⟨f.mapKind p.1, f.mapClaim p.1 p.2.1, f.translate p.1 p.2.1 p.2.2⟩

def identity (authority : AuthorityContract S) : Translation authority authority where
  toTheoryTranslation := TheoryTranslation.identity S
  translate _ _ certificate := certificate
  preserves _ _ _ accepted := accepted

def comp (f : Translation SA MA) (g : Translation MA TA) : Translation SA TA where
  toTheoryTranslation := f.toTheoryTranslation.comp g.toTheoryTranslation
  translate kind claim certificate := g.translate (f.mapKind kind)
    (f.mapClaim kind claim) (f.translate kind claim certificate)
  preserves kind claim certificate accepted := g.preserves _ _ _
    (f.preserves kind claim certificate accepted)

@[simp] theorem identity_packet (p : Packet SA) : (identity SA).packet p = p := rfl

@[simp] theorem comp_packet (f : Translation SA MA) (g : Translation MA TA)
    (p : Packet SA) : (f.comp g).packet p = g.packet (f.packet p) := rfl

/-- Both acceptance and rejection commute on every translated input. -/
def Exact (f : Translation SA TA) : Prop :=
  ∀ p, checkPacket TA (f.packet p) = checkPacket SA p

theorem exact_identity : (identity SA).Exact := fun _ => rfl

theorem Exact.comp {f : Translation SA MA} {g : Translation MA TA}
    (hf : f.Exact) (hg : g.Exact) : (f.comp g).Exact := by
  intro p
  rw [comp_packet, hg, hf]

/-- Adapter for the existing exact authority translation interface. -/
def ofCertified (f : CertifiedTranslation SA TA) : Translation SA TA where
  toTheoryTranslation := f.toTheoryTranslation
  translate kind _ certificate := f.mapCertificate kind certificate
  preserves kind claim certificate accepted := by
    exact (f.check_commutes kind claim certificate).trans accepted

theorem ofCertified_exact (f : CertifiedTranslation SA TA) : (ofCertified f).Exact := by
  intro p
  exact f.check_commutes p.1 p.2.1 p.2.2

/-- Global scope reflection applies even to proofs outside the compiler image. -/
theorem reflects_accepted (f : Translation SA TA)
    (reflects : f.toTheoryTranslation.ScopeReflecting)
    (kind : SK) (claim : S.Claim kind)
    (certificate : TA.Certificate (f.mapKind kind))
    (accepted : (TA.checker (f.mapKind kind)).check
      (f.mapClaim kind claim) certificate = true) : S.Scope kind claim :=
  reflects kind claim ((TA.scopeAuthority _).sound _ _ accepted)

/-- An authored reverse algorithm is stronger than propositional reflection.
It must handle every accepted target certificate for a translated claim.
No runtime bound is implicit in this data. -/
structure Extractor (f : Translation SA TA) where
  extract : ∀ kind, S.Claim kind → TA.Certificate (f.mapKind kind) → SA.Certificate kind
  accepted : ∀ kind claim certificate,
    (TA.checker (f.mapKind kind)).check (f.mapClaim kind claim) certificate = true →
    (SA.checker kind).check claim (extract kind claim certificate) = true

theorem Extractor.reflects {f : Translation SA TA} (e : f.Extractor) :
    f.toTheoryTranslation.ScopeReflecting := by
  intro kind claim h
  obtain ⟨certificate, accepted⟩ := (TA.scopeAuthority _).complete _ h
  exact (SA.scopeAuthority _).sound _ _ (e.accepted _ _ _ accepted)

def Extractor.comp {f : Translation SA MA} {g : Translation MA TA}
    (first : f.Extractor) (second : g.Extractor) : (f.comp g).Extractor where
  extract kind claim certificate := first.extract kind claim
    (second.extract (f.mapKind kind) (f.mapClaim kind claim) certificate)
  accepted _kind _claim _certificate accepted := first.accepted _ _ _
    (second.accepted _ _ _ accepted)

end Translation

/-- A uniform polynomial translation of whole packets, realized by a finite
stack machine on every encoded packet, including rejected certificates. -/
structure OperationalTranslation {SK TK Γ Δ : Type} [Fintype Γ] [Fintype Δ]
    {S : TheoryFamily SK} {T : TheoryFamily TK}
    (SA : AuthorityContract S) (TA : AuthorityContract T)
    (sourceEncoding : Computability.Encoding (Packet SA) Γ)
    (targetEncoding : Computability.Encoding (Packet TA) Δ)
    extends Translation SA TA where
  outputBound : PolyBoundedBy (fun p => (targetEncoding.encode (toTranslation.packet p)).length)
    (fun p => (sourceEncoding.encode p).length)
  realization : TM2ComputableInPolyTime sourceEncoding.encode targetEncoding.encode toTranslation.packet
  /-- FinTM2 itself requires finiteness only of the input alphabet. This
  stronger interface rules out an unbounded object hidden in an internal cell. -/
  finiteAlphabet : ∀ key, Finite (realization.tm.Γ key)

namespace OperationalTranslation

variable {SK MK TK Γ Δ Ε : Type} [Fintype Γ] [Fintype Δ] [Fintype Ε]
    {S : TheoryFamily SK} {M : TheoryFamily MK} {T : TheoryFamily TK}
    {SA : AuthorityContract S} {MA : AuthorityContract M} {TA : AuthorityContract T}
    {se : Computability.Encoding (Packet SA) Γ}
    {me : Computability.Encoding (Packet MA) Δ}
    {te : Computability.Encoding (Packet TA) Ε}

/-- The composed clock includes both machines and the physical intermediate
copy, charged as `2 * intermediate.length + 2` by the composition theorem. -/
noncomputable def comp [Inhabited Δ]
    (f : OperationalTranslation SA MA se me)
    (g : OperationalTranslation MA TA me te) : OperationalTranslation SA TA se te where
  toTranslation := f.toTranslation.comp g.toTranslation
  outputBound := (g.outputBound.comp f.packet).trans f.outputBound
  realization := ExecutedComposition.realization f.realization g.realization
    f.outputBound.choose f.outputBound.choose_spec
  finiteAlphabet := by
    intro key
    change Finite (Mettapedia.Computability.StackMachineComposition.Alphabet
      f.realization.tm g.realization.tm key)
    cases key with
    | none => exact f.finiteAlphabet _
    | some key =>
      cases key with
      | inl key => exact f.finiteAlphabet key
      | inr key => exact g.finiteAlphabet key

set_option backward.isDefEq.respectTransparency false in
/-- Even identity transport is implemented and charged, rather than supplied
with a freely declared zero clock. -/
noncomputable def identity [Inhabited Γ] (authority : AuthorityContract S)
    (encoding : Computability.Encoding (Packet authority) Γ) :
    OperationalTranslation authority authority encoding encoding where
  toTranslation := Translation.identity authority
  outputBound := PolyBoundedBy.refl _
  realization :=
    { tm := SymbolMapMachine.machine (id : Γ → Γ)
      inputAlphabet := Equiv.refl Γ
      outputAlphabet := Equiv.refl Γ
      time := C 2 * X + C 2
      outputsFun p := by
        simpa [SymbolMapMachine.machine, Translation.identity, Translation.packet] using
          SymbolMapMachine.outputs (id : Γ → Γ) (encoding.encode p) }
  finiteAlphabet _ := (inferInstance : Finite Γ)

def execution (f : OperationalTranslation SA TA se te) (p : Packet SA) :
    TM2OutputsInTime f.realization.tm
      ((se.encode p).map f.realization.inputAlphabet.symm)
      (some ((te.encode (f.packet p)).map f.realization.outputAlphabet.symm))
      (f.realization.time.eval (se.encode p).length) := f.realization.outputsFun p

theorem clock_positive (f : OperationalTranslation SA TA se te) (p : Packet SA) :
    0 < f.realization.time.eval (se.encode p).length :=
  OperationalPSimulation.outputs_positive (f.execution p)

theorem comp_exact [Inhabited Δ]
    (f : OperationalTranslation SA MA se me) (g : OperationalTranslation MA TA me te)
    (hf : f.toTranslation.Exact) (hg : g.toTranslation.Exact) :
    (f.comp g).toTranslation.Exact := hf.comp hg

end OperationalTranslation

namespace Controls

/-- Two independently specified scopes, the second adding just judgment one. -/
def zeroTheory : TheoryFamily Unit where
  Signature := Unit
  signatureOf _ := ()
  Claim _ := Nat
  Scope _ n := n = 0
  Meaning _ n := n ≤ 1
  scope_sound _ _ h := by omega

def twoTheory : TheoryFamily Unit where
  Signature := Unit
  signatureOf _ := ()
  Claim _ := Nat
  Scope _ n := n = 0 ∨ n = 1
  Meaning _ n := n ≤ 1
  scope_sound _ _ h := by rcases h with h | h <;> omega

def zeroAuthority : AuthorityContract zeroTheory where
  Certificate _ := Unit
  checker _ := ⟨fun (n : Nat) (_ : Unit) => decide (n = 0)⟩
  scopeAuthority _ :=
    { sound := by intro n _ h; simpa [zeroTheory] using h
      complete := by intro n h; exact ⟨(), by simpa [zeroTheory] using h⟩ }

def twoAuthority : AuthorityContract twoTheory where
  Certificate _ := Bool
  checker _ := ⟨fun (n : Nat) (tag : Bool) => if tag then decide (n = 1) else decide (n = 0)⟩
  scopeAuthority _ :=
    { sound := by
        intro n tag h
        cases tag
        · exact Or.inl (by simpa using h)
        · exact Or.inr (by simpa using h)
      complete := by
        intro n h
        rcases h with h | h
        · exact ⟨false, by simpa using h⟩
        · exact ⟨true, by simpa using h⟩ }

/-- The compiler selects the original rule, while the host has an extra rule. -/
def inclusion : Translation zeroAuthority twoAuthority where
  mapKind := id
  mapSignature := id
  signature_commutes _ := rfl
  mapClaim _ := id
  scope_preserved _ _ h := Or.inl h
  meaning_preserved _ _ h := h
  translate _ _ _ := false
  preserves _ _ _ h := h

theorem inclusion_exact : inclusion.Exact := fun _ => rfl

theorem original_accepted : checkPacket twoAuthority
    (inclusion.packet ⟨(), (0 : Nat), ()⟩) = true := by decide

theorem wrong_claim_refused : checkPacket twoAuthority
    (inclusion.packet ⟨(), (2 : Nat), ()⟩) = false := by decide

/-- Exact replay on the compiler image does not reflect arbitrary host proofs. -/
theorem exact_not_reflecting : ¬ inclusion.toTheoryTranslation.ScopeReflecting := by
  intro reflection
  have impossible := reflection () (1 : Nat) (Or.inr rfl)
  change 1 = 0 at impossible
  omega

/-- Nor does exact replay alone supply an algorithm extracting every host proof. -/
theorem no_extractor : IsEmpty inclusion.Extractor :=
  ⟨fun extractor => exact_not_reflecting extractor.reflects⟩

end Controls

end Mettapedia.GSLT.LanguageDef.ResourceTranslation
