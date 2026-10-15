import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MetabolicReadout
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.MetabolicSignatureCodec
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.MetabolicFundingReadout

/-!
# Complete source stacks in the rho metabolic protocol

The conversion preserves each ordered source signature. The closed signature
codec uses an explicit countable ground-atom representation. A designated
protocol session carries one located source stack; source location and receipt
remain separate from the session's declared target channel. This is not a
translation of arbitrary cost terms or contexts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Metabolic.StackInternalization

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

universe u

abbrev TargetStack (Ground : Type u) := RhoCalculus.Metabolic.Stack (CostSig Ground)

def stack {Ground : Type u} : CostStack Ground → TargetStack Ground
  | .empty => .empty
  | .cons head tail => .cell head (stack tail)

def source {Ground : Type u} : TargetStack Ground → CostStack Ground
  | .empty => .empty
  | .cell head tail => .cons head (source tail)

@[simp]
theorem source_stack {Ground : Type u} (original : CostStack Ground) : source (stack original) = original := by
  cases original with
  | empty => rfl
  | cons head tail => simp [stack, source, source_stack tail]

@[simp]
theorem stack_source {Ground : Type u} (original : TargetStack Ground) : stack (source original) = original := by
  induction original with
  | empty => rfl
  | cell head tail ih => simp [stack, source, ih]

theorem stack_injective {Ground : Type u} : Function.Injective (stack (Ground := Ground)) := by
  intro first second equality
  simpa using congrArg source equality

@[simp]
theorem ordered_heads {Ground : Type u} (original : CostStack Ground) :
    (stack original).heads = original.toList := by
  cases original with
  | empty => rfl
  | cons head tail => simp [stack, RhoCalculus.Metabolic.Stack.heads, CostStack.toList, ordered_heads tail]

theorem exact_cells {Ground : Type u} (original : CostStack Ground) :
    (stack original).size = original.cellCount := by
  rw [RhoCalculus.Metabolic.Stack.size_eq_length, ordered_heads, CostStack.cellCount_eq_length]

theorem exact_signatures {Ground : Type u} (original : CostStack Ground) :
    (stack original).heads.sum = original.storedSignatures := by
  rw [ordered_heads, ← CostStack.storedSignatures_eq_sum]

/-- The actual codec laws are constructed for the protocol, rather than supplied
as an unproved representation contract. -/
noncomputable def signatureEncoding {Ground : Type u} [Encodable Ground] :
    RhoCalculus.Metabolic.Encoding (CostSig Ground) where
  code := SignatureCodec.signatureCode
  typed := fun signature => SignatureCodec.signature_typed signature []
  safe := SignatureCodec.signature_safe
  normalize := SignatureCodec.signature_normal
  substitution := SignatureCodec.signature_subst
  canonical := SignatureCodec.signature_canonical

noncomputable def payload {Ground : Type u} [Encodable Ground] (original : CostStack Ground) : Pattern :=
  RhoCalculus.Metabolic.payload signatureEncoding (stack original)

noncomputable def message {Ground : Type u} [Encodable Ground] (original : CostStack Ground) :
    LanguageDefGSLT.RhoProcess :=
  RhoCalculus.Metabolic.messageProcess signatureEncoding (stack original)

/-- Complete source cells are recovered from the protocol's independently defined
structural readout. The order of cells is preserved. -/
theorem payload_readout {Ground : Type u} [Encodable Ground] (original : CostStack Ground)
    (codes : List Pattern) (read : RhoCalculus.Metabolic.PayloadReadout (payload original) codes) :
    codes.map (SignatureCodec.signatureRead (Ground := Ground)) = original.toList := by
  have exact := (RhoCalculus.Metabolic.payload_complete_readout signatureEncoding (stack original) codes).mp read
  rw [exact, ordered_heads, List.map_map]
  have decoded : SignatureCodec.signatureRead (Ground := Ground) ∘ signatureEncoding.code = id := by
    funext signature
    exact SignatureCodec.signature_roundtrip signature
  rw [decoded, List.map_id]

/-- Canonical rho equations preserve the complete ordered signatures, not only
the raw encoding or its scalar depth. -/
theorem canonical_payload_readout {Ground : Type u} [Encodable Ground]
    (original : CostStack Ground) (codes : List Pattern)
    (read : RhoCalculus.Metabolic.CanonicalPayloadReadout (Canonical.canonicalize (payload original)) codes) :
    codes.map (SignatureCodec.signatureRead (Ground := Ground)) = original.toList := by
  have exact := (RhoCalculus.Metabolic.canonical_payload_complete_readout
    signatureEncoding (stack original) codes).mp read
  rw [exact, ordered_heads, List.map_map]
  have decoded : SignatureCodec.signatureRead (Ground := Ground) ∘ signatureEncoding.code = id := by
    funext signature
    exact SignatureCodec.signature_roundtrip signature
  rw [decoded, List.map_id]

theorem semantic_stack_injective {Ground : Type u} [Encodable Ground]
    {first second : CostStack Ground}
    (same : Canonical.canonicalize (payload first) = Canonical.canonicalize (payload second)) :
    first = second := by
  apply stack_injective
  exact RhoCalculus.Metabolic.canonical_stack_readout_injective signatureEncoding
    SignatureCodec.signatureCode_injective same

theorem selected_head_and_tail {Ground : Type u} (choice : SelectedPurseHead Ground) :
    stack (.cons choice.head choice.tail) = .cell choice.head (stack choice.tail) := rfl

theorem selected_tail_order {Ground : Type u} (choice : SelectedPurseHead Ground) :
    (stack choice.tail).heads = choice.tail.toList := ordered_heads _

theorem selected_tail_inventory {Ground : Type u} (choice : SelectedPurseHead Ground) :
    (stack (.cons choice.head choice.tail)).heads.sum =
      (stack choice.tail).heads.sum + choice.head := by
  simp [stack, RhoCalculus.Metabolic.Stack.heads, add_comm]

theorem selected_positive_burn {Ground : Type u} (choice : SelectedPurseHead Ground) :
    0 < choice.head.card := Multiset.card_pos.mpr choice.head_valid

namespace Controls

def firstStack : CostStack Nat := .cons {0} (.cons {1} .empty)
def secondStack : CostStack Nat := .cons {1} (.cons {0} .empty)

theorem equal_inventory : firstStack.storedSignatures = secondStack.storedSignatures := by
  simp [firstStack, secondStack, CostStack.storedSignatures, add_comm]

theorem ordered_stacks_remain_distinct : stack firstStack ≠ stack secondStack := by
  intro equality
  have sourceEqual := stack_injective equality
  have different : firstStack ≠ secondStack := by decide +kernel
  exact different sourceEqual

theorem equal_price_does_not_identify_signatures :
    ({0} : CostSig Nat).card = ({1} : CostSig Nat).card ∧
      SignatureCodec.signatureCode ({0} : CostSig Nat) ≠ SignatureCodec.signatureCode ({1} : CostSig Nat) := by
  constructor
  · rfl
  · intro equality
    have same := SignatureCodec.signatureCode_injective equality
    have different : ({0} : CostSig Nat) ≠ {1} := by decide +kernel
    exact different same

end Controls

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Metabolic.StackInternalization
