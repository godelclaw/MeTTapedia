import Mettapedia.OSLF.Framework.RhoScopeCanonicalSizeBound
import Mettapedia.OSLF.Framework.RhoGeneratedScopeSubstitution

/-!
# Retained scope receipts can exceed the membership decision cutoff

A supplied certificate can be extended through the actual parallel-unit and
name equations without changing its readout. Its extra unfolding and premise
occurrences are retained. The canonical-size theorem supplies a shorter
available witness; it does not erase this history or bound every receipt.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeReceiptLoops

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres
open RhoEquationGeneratedScope RhoGeneratedScopeSubstitution RhoScopeCanonicalSizeBound

def extend {context : Ctx sig} {left right : Process context → Prop}
    (zeroAdmitted : left (zero context)) {name : Name context}
    (certificate : Certificate left right name) : Certificate left right name :=
  ((congrArg quote (join_zero_left (drop name))).trans (quote_drop name)) ▸
    Certificate.right (zero context) zeroAdmitted name certificate

theorem extend_depth {context : Ctx sig} {left right : Process context → Prop}
    (zeroAdmitted : left (zero context)) {name : Name context}
    (certificate : Certificate left right name) :
    (extend zeroAdmitted certificate).depth = certificate.depth + 1 := by
  simp only [extend, depth_cast, Certificate.depth]

theorem extend_atomic_origins {context : Ctx sig} {left right : Process context → Prop}
    (zeroAdmitted : left (zero context)) {name : Name context}
    (certificate : Certificate left right name) :
    (extend zeroAdmitted certificate).atomicOrigins = Sum.inl (zero context) :: certificate.atomicOrigins := by
  simp only [extend, Certificate.atomicOrigins_cast, Certificate.atomicOrigins]

def tower {context : Ctx sig} {left right : Process context → Prop}
    (zeroAdmitted : left (zero context)) {name : Name context}
    (certificate : Certificate left right name) : Nat → Certificate left right name
  | 0 => certificate
  | height + 1 => extend zeroAdmitted (tower zeroAdmitted certificate height)

theorem tower_depth {context : Ctx sig} {left right : Process context → Prop}
    (zeroAdmitted : left (zero context)) {name : Name context}
    (certificate : Certificate left right name) (height : Nat) :
    (tower zeroAdmitted certificate height).depth = certificate.depth + height := by
  induction height with
  | zero => simp only [tower, Nat.add_zero]
  | succ height ih => rw [tower, extend_depth, ih, Nat.add_assoc]

theorem receipt_depths_exceed_every_cutoff {context : Ctx sig} {left right : Process context → Prop}
    (zeroAdmitted : left (zero context)) {name : Name context}
    (certificate : Certificate left right name) (cutoff : Nat) :
    ∃ receipt : Certificate left right name, cutoff < receipt.depth := by
  refine ⟨tower zeroAdmitted certificate (cutoff + 1), ?_⟩
  rw [tower_depth]
  omega

theorem unbounded_receipts_with_a_bounded_membership_witness {context : Ctx sig}
    {left right : Process context → Prop} (zeroAdmitted : left (zero context))
    {name : Name context} (certificate : Certificate left right name) :
    RhoGeneratedScopeStrata.Bounded left right (canonicalSize name) name ∧
      ∀ cutoff, ∃ receipt : Certificate left right name, cutoff < receipt.depth :=
  ⟨certificate_has_size_bounded_witness certificate, receipt_depths_exceed_every_cutoff zeroAdmitted certificate⟩

end Mettapedia.OSLF.Framework.RhoScopeReceiptLoops
