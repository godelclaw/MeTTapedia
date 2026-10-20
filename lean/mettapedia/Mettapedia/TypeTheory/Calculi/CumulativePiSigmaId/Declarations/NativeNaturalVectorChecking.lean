import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorFamilies
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedFamilyChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationConversionCode
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerChecking

/-!
# Finite checking for the declared natural/vector computation

The four existing Nat/Vec iota schemas feed one ordered root table. The
decoder is proved sound and complete for the independently defined four-case
root evidence, then reused by declaration-aware structural conversion.

This covers finite submitted conversion and typing evidence for the original
rules. It does not prove normalization or uniform subject preservation of
the raw signature, derive its eliminators, or implement a native backend.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
namespace Checking

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.Declaration

/-- These are the original schemas, including their original typed receipts. -/
def schemas : Declaration.IndexedFamily.Checking.Schemas
    Tower.rules rawSignature proofRelevantIotaComputation :=
  [⟨3, natZeroIotaSchema⟩, ⟨4, natSuccIotaSchema⟩,
   ⟨4, vecNilIotaSchema⟩, ⟨7, vecConsIotaSchema⟩]

abbrev table := Declaration.IndexedFamily.Checking.table schemas

def enabled : Fin table.length → Bool := fun _ => true

/-- Exact replay against the independently authored four-rule root relation. -/
def iotaDecoder : StructuralConversionCode.RootDecoder iotaComputation where
  Code := SchemaTableConversionCode.Code Tower.Head
  decode := SchemaTableConversionCode.decode table enabled
  sound := by
    intro n code left right accepted
    obtain ⟨evidence⟩ := SchemaTableConversionCode.decode_sound table enabled code accepted
    exact ⟨Declaration.IndexedFamily.Checking.realizeEvidence schemas evidence⟩
  complete := by
    intro n left right step
    obtain ⟨evidence⟩ := step
    cases evidence with
    | natZero motive zeroCase succCase =>
        exact ⟨⟨0, [succCase, right, motive]⟩, rfl⟩
    | natSucc motive zeroCase succCase number =>
        exact ⟨⟨1, [number, succCase, zeroCase, motive]⟩, rfl⟩
    | vecNil element motive nilCase consCase =>
        exact ⟨⟨2, [consCase, right, motive, element]⟩, rfl⟩
    | vecCons element motive nilCase consCase length head tail =>
        exact ⟨⟨3, [tail, head, length, consCase, nilCase, motive, element]⟩, rfl⟩

/-- Inherited roots, delta lookup and the four declared iota cases share the
existing declaration decoder. No extra root rule is assumed. -/
def decoder : StructuralConversionCode.RootDecoder rules.computation :=
  DeclarationConversionCode.rootDecoder (base := Tower.rules) (signature := rawSignature)
    (.ofEmpty _ rfl) iotaDecoder

local instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel rules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

abbrev ConversionCode (n : Nat) := StructuralConversionCode.Code Tower.Head decoder.Code n

def conversionCheck {n : Nat} (code : ConversionCode n) (left right : Tower.Tm n) : Bool :=
  code.check rules.headEq decoder.decode left right

theorem conversionCheck_sound {n : Nat} {code : ConversionCode n} {left right : Tower.Tm n}
    (accepted : conversionCheck code left right = true) :
    Conv rules.headEq left right rules.computation :=
  StructuralConversionCode.Code.check_sound decoder accepted

/-- Exactness means existence of finite evidence, not termination of search. -/
theorem conversion_iff_checked {n : Nat} {left right : Tower.Tm n} :
    Conv rules.headEq left right rules.computation ↔
      ∃ code : ConversionCode n, conversionCheck code left right = true :=
  StructuralConversionCode.Code.conversion_iff_checked decoder

abbrev Request (claim : FormationSensitiveRuleSignature.Judgment Tower.Head) :=
  FormationSensitiveChecking.Request decoder claim

def check {claim : FormationSensitiveRuleSignature.Judgment Tower.Head}
    (request : Request claim) : Bool := request.check decoder

/-- The same decoder joins the existing common checking interface for the
full formation-sensitive declaration judgment. -/
theorem coverage (claim : FormationSensitiveRuleSignature.Judgment Tower.Head) :
    FormationSensitive.Judgment rules claim.context claim.subject claim.type ↔
      ∃ request : Request claim, check request = true := by
  constructor
  · intro derived
    obtain ⟨context, nodes, root, accepted⟩ :=
      (FormationSensitiveChecking.judgment_iff_checked decoder claim).mp derived
    exact ⟨⟨context, nodes, root⟩, accepted⟩
  · rintro ⟨request, accepted⟩
    exact request.sound decoder accepted

end Checking
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
