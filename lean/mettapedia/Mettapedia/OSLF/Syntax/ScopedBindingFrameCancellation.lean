import Mettapedia.OSLF.Syntax.ScopedBindingContextSubstitution

/-!
# Complete frame cancellation and retained outer slots

At a fixed selected slot, equality of filled constructor terms determines
both the entire hole value and every stored sibling. Complete binder paths
are consequently injective on their hole values, even though different
selected positions can have identical ground fillings. Slot codes retain
the operator and selected position independently of variable contexts;
capture-avoiding substitution preserves the actual outer slot code.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

variable {S : Binding.Signature}

local instance bindingCancellationQuiver : Quiver (Scope S) := bindingFrameQuiver S

theorem assembleArguments_injective (context : Binding.Ctx S)
    (declarations : List (List S.Srt × S.Srt)) :
    Function.Injective (assembleArguments (S := S) context declarations) := by
  intro first second same
  have encoded := congrArg (encodeArguments (S := S)) same
  rw [encodeArguments_assemble, encodeArguments_assemble] at encoded
  funext position
  exact encode_injective (congrFun encoded position)

theorem BindingFrame.slot_fill_readback {context : Binding.Ctx S} {sort : S.Srt}
    (operator : S.Op sort) (position : Fin (S.arity operator).length)
    (firstSiblings secondSiblings : (other : Fin (S.arity operator).length) → other ≠ position →
      Binding.Term S (((S.arity operator).get other).1 ++ context)
        ((S.arity operator).get other).2)
    (first second : Binding.Term S (((S.arity operator).get position).1 ++ context)
      ((S.arity operator).get position).2)
    (same : (BindingFrame.slot context sort operator position firstSiblings).fill first =
      (BindingFrame.slot context sort operator position secondSiblings).fill second) :
    first = second ∧ firstSiblings = secondSiblings := by
  change Binding.Term.op operator (assembleArguments context (S.arity operator)
      (fun other => if equal : other = position then equal.symm ▸ first else firstSiblings other equal)) =
    Binding.Term.op operator (assembleArguments context (S.arity operator)
      (fun other => if equal : other = position then equal.symm ▸ second else secondSiblings other equal)) at same
  have arguments : assembleArguments context (S.arity operator)
      (fun other => if equal : other = position then equal.symm ▸ first else firstSiblings other equal) =
    assembleArguments context (S.arity operator)
      (fun other => if equal : other = position then equal.symm ▸ second else secondSiblings other equal) := by
    simpa only [Binding.Term.op.injEq, heq_eq_eq, eq_self, true_and] using same
  have readings := assembleArguments_injective context (S.arity operator) arguments
  refine ⟨?_, ?_⟩
  · simpa only [dite_true] using congrFun readings position
  · funext other absent
    simpa only [dif_neg absent] using congrFun readings other

theorem BindingFrame.fill_injective {source target : Scope S}
    (frame : BindingFrame S source target) : Function.Injective frame.fill := by
  cases frame with
  | slot context sort operator position siblings =>
    intro first second same
    exact (BindingFrame.slot_fill_readback operator position siblings siblings first second same).1

theorem fillContext_injective {source target : Scope S} (context : BindingContext S source target) :
    Function.Injective (fillContext context) := by
  induction context with
  | nil => exact fun _ _ same => same
  | cons previous frame inductionHypothesis =>
    intro first second same
    exact inductionHypothesis (frame.fill_injective same)

inductive BindingSlotCode (S : Binding.Signature) where
  | mk (sort : S.Srt) (operator : S.Op sort) (position : Fin (S.arity operator).length)

def BindingFrame.slotCode {source target : Scope S}
    (frame : BindingFrame S source target) : BindingSlotCode S :=
  match frame with
  | .slot _ sort operator position _ => .mk sort operator position

def lastSlot {source target : Scope S} (context : BindingContext S source target) :
    Option (BindingSlotCode S) :=
  match context with
  | .nil => none
  | .cons _ frame => some frame.slotCode

theorem lastSlot_substitution {source target : Scope S} (context : BindingContext S source target)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination) :
    lastSlot (substituteContext context destination sigma).path = lastSlot context := by
  cases context with
  | nil => rfl
  | cons previous frame =>
    cases frame
    rfl

theorem BindingFrame.same_slot_cancel {first second target : Scope S}
    (left : BindingFrame S first target) (right : BindingFrame S second target)
    (sameSlot : left.slotCode = right.slotCode)
    (firstValue : Binding.Term S first.1 first.2) (secondValue : Binding.Term S second.1 second.2)
    (same : left.fill firstValue = right.fill secondValue) :
    first = second ∧ HEq left right ∧ HEq firstValue secondValue := by
  cases left with
  | slot context sort operator position siblings =>
    cases right with
    | slot _ _ otherOperator otherPosition otherSiblings =>
      change BindingSlotCode.mk sort operator position =
        BindingSlotCode.mk sort otherOperator otherPosition at sameSlot
      cases sameSlot
      obtain ⟨sameValue, sameSiblings⟩ := BindingFrame.slot_fill_readback
        operator position siblings otherSiblings firstValue secondValue same
      subst secondValue otherSiblings
      exact ⟨rfl, HEq.rfl, HEq.rfl⟩

end Mettapedia.OSLF.Binding.ScopedEncoding
