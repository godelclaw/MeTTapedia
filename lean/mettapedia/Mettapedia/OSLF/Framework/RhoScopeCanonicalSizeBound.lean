import Mettapedia.OSLF.Framework.RhoScopeBoundedDecision
import Mettapedia.OSLF.Syntax.RhoRecursiveComponentDescent

/-!
# Finite depth bounds for arbitrary atomic scopes on actual rho names

Every finite scope certificate has a witness whose depth is bounded by the
canonical size of its readout. A recursive component that reads back to the
same name already supplies a witness for that name; all other components
strictly decrease canonical size. This proves termination without assuming
unique parallel splits or ruling out the source name equation's self-loops.
The bound concerns an available witness, not every retained derivation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeCanonicalSizeBound

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoSchema.IntrinsicEncoding
open MeTTaIL.PatternTreeSize
open RhoRecursiveComponentDescent
open RhoEquationGeneratedScope RhoGeneratedScopeStrata

def canonicalSize {context : Ctx sig} (name : Name context) : Nat :=
  nodes (encodeEquationClass name)

theorem certificate_has_size_bounded_witness {context : Ctx sig}
    {left right : Process context → Prop} {name : Name context}
    (certificate : Certificate left right name) :
    Bounded left right (canonicalSize name) name := by
  induction certificate with
  | atoms first second firstAtom secondAtom =>
    exact ⟨.atoms first second firstAtom secondAtom, Nat.zero_le _⟩
  | left child childCertificate second secondAtom ih =>
    rcases left_recursive_self_or_smaller child second with same | smaller
    · exact same ▸ ih
    · obtain ⟨witness, small⟩ := ih
      exact ⟨.left child witness second secondAtom,
        (Nat.add_le_add_right small 1).trans (Nat.succ_le_of_lt smaller)⟩
  | right first firstAtom child childCertificate ih =>
    rcases right_recursive_self_or_smaller first child with same | smaller
    · exact same ▸ ih
    · obtain ⟨witness, small⟩ := ih
      exact ⟨.right first firstAtom child witness,
        (Nat.add_le_add_right small 1).trans (Nat.succ_le_of_lt smaller)⟩
  | both first second firstCertificate secondCertificate firstIH secondIH =>
    rcases left_recursive_self_or_smaller first (drop second) with firstSame | firstSmaller
    · exact firstSame ▸ firstIH
    · rcases right_recursive_self_or_smaller (drop first) second with secondSame | secondSmaller
      · exact secondSame ▸ secondIH
      · obtain ⟨firstWitness, firstSmall⟩ := firstIH
        obtain ⟨secondWitness, secondSmall⟩ := secondIH
        refine ⟨.both first second firstWitness secondWitness, ?_⟩
        have firstBound := (Nat.add_le_add_right firstSmall 1).trans
          (Nat.succ_le_of_lt firstSmaller)
        have secondBound := (Nat.add_le_add_right secondSmall 1).trans
          (Nat.succ_le_of_lt secondSmaller)
        change max firstWitness.depth secondWitness.depth + 1 ≤ _
        dsimp only [canonicalSize]
        omega

theorem generated_iff_size_bounded {context : Ctx sig} (left right : Process context → Prop)
    (name : Name context) :
    generated left right name ↔ Bounded left right (canonicalSize name) name := by
  constructor
  · intro member
    obtain ⟨certificate⟩ := (generated_iff_certificate left right name).mp member
    exact certificate_has_size_bounded_witness certificate
  · rintro ⟨certificate, _⟩
    exact certificate_sound certificate

theorem bounded_stabilizes_at_canonical_size {context : Ctx sig}
    (left right : Process context → Prop) (name : Name context) {limit : Nat}
    (enough : canonicalSize name ≤ limit) :
    Bounded left right limit name ↔ generated left right name := by
  constructor
  · rintro ⟨certificate, _⟩
    exact certificate_sound certificate
  · intro member
    exact bounded_mono enough ((generated_iff_size_bounded left right name).mp member)

theorem stratum_le_canonical_size {context : Ctx sig} {left right : Process context → Prop}
    {name : Name context} (member : generated left right name) :
    stratum member ≤ canonicalSize name :=
  stratum_le member ((generated_iff_size_bounded left right name).mp member)

end Mettapedia.OSLF.Framework.RhoScopeCanonicalSizeBound
