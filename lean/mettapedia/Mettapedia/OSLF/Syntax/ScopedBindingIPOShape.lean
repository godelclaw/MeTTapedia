import Mettapedia.OSLF.Syntax.ScopedBindingFrameCancellation
import Mettapedia.CategoryTheory.GroundPathRelativePushout

/-!
# Minimal binding bounds from actual outer slots

A commuting bound shares a removable outer frame exactly when both paths
have the same final operator and selected position. Equality of the full
filled terms then reconstructs all siblings and the inner hole values.
Every competing candidate with nonempty descent exposes such a shared slot.
The resulting characterization earns IPO preservation and reflection under
arbitrary capture-avoiding variable substitution, without assuming the
substitution injective or cancelling distinct ground context actions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout

variable {S : Binding.Signature}
local instance bindingIPOShapeQuiver : Quiver (Scope S) := bindingFrameQuiver S

def SharedOuterSlot {first second target : Scope S}
    (left : BindingContext S first target) (right : BindingContext S second target) : Prop :=
  ∃ code, lastSlot left = some code ∧ lastSlot right = some code

theorem binding_ipo_of_no_shared_outer_slot {first second target : Scope S}
    (firstValue : Binding.Term S first.1 first.2) (secondValue : Binding.Term S second.1 second.2)
    (left : BindingContext S first target) (right : BindingContext S second target)
    (square : bindingTermArrow firstValue ≫ bindingContextArrow left =
      bindingTermArrow secondValue ≫ bindingContextArrow right)
    (separated : ¬SharedOuterSlot left right) :
    IsIdemPushout (bindingTermArrow firstValue) (bindingTermArrow secondValue)
      (bindingContextArrow left) (bindingContextArrow right) square := by
  let candidate : PathCandidate (bindingAction S) (first := first) (second := second)
      (target := target) firstValue secondValue left right := PathCandidate.self (Arrow.value.inj square)
  apply PathCandidate.categorical_isRelativePushout candidate
  intro other
  rcases other with ⟨apex, inl, inr, down, comm, recoversLeft, recoversRight⟩
  cases down with
  | nil => exact Nat.le_refl _
  | cons previous frame =>
    have leftSlot := congrArg lastSlot recoversLeft
    have rightSlot := congrArg lastSlot recoversRight
    change some frame.slotCode = lastSlot left at leftSlot
    change some frame.slotCode = lastSlot right at rightSlot
    exact False.elim (separated ⟨frame.slotCode, leftSlot.symm, rightSlot.symm⟩)

theorem binding_ipo_excludes_shared_outer_slot {first second target : Scope S}
    (firstValue : Binding.Term S first.1 first.2) (secondValue : Binding.Term S second.1 second.2)
    (left : BindingContext S first target) (right : BindingContext S second target)
    (square : bindingTermArrow firstValue ≫ bindingContextArrow left =
      bindingTermArrow secondValue ≫ bindingContextArrow right)
    (minimal : IsIdemPushout (bindingTermArrow firstValue) (bindingTermArrow secondValue)
      (bindingContextArrow left) (bindingContextArrow right) square) :
    ¬SharedOuterSlot left right := by
  rintro ⟨code, leftSlot, rightSlot⟩
  cases left with
  | nil => cases leftSlot
  | cons leftPrevious leftFrame =>
    cases right with
    | nil => cases rightSlot
    | cons rightPrevious rightFrame =>
      have sameSlot : leftFrame.slotCode = rightFrame.slotCode :=
        (Option.some.inj leftSlot).trans (Option.some.inj rightSlot).symm
      have same : leftFrame.fill (fillContext leftPrevious firstValue) =
          rightFrame.fill (fillContext rightPrevious secondValue) := Arrow.value.inj square
      obtain ⟨sameInterface, sameFrame, sameValue⟩ :=
        BindingFrame.same_slot_cancel leftFrame rightFrame sameSlot
          (fillContext leftPrevious firstValue) (fillContext rightPrevious secondValue) same
      cases sameInterface
      have equalFrames : leftFrame = rightFrame := eq_of_heq sameFrame
      subst rightFrame
      let candidate : PathCandidate (bindingAction S) (first := first) (second := second)
          (target := target) firstValue secondValue
          (leftPrevious.cons leftFrame) (rightPrevious.cons leftFrame) := {
        apex := _, inl := leftPrevious, inr := rightPrevious,
        down := (.nil : BindingContext S _ _).cons leftFrame,
        comm := eq_of_heq sameValue, fac_left := rfl, fac_right := rfl }
      have counted := ipo_no_context_descent (bindingAction S) firstValue secondValue
        (leftPrevious.cons leftFrame) (rightPrevious.cons leftFrame) square minimal candidate
      change 1 = 0 at counted
      omega

theorem binding_ipo_iff_no_shared_outer_slot {first second target : Scope S}
    (firstValue : Binding.Term S first.1 first.2) (secondValue : Binding.Term S second.1 second.2)
    (left : BindingContext S first target) (right : BindingContext S second target)
    (square : bindingTermArrow firstValue ≫ bindingContextArrow left =
      bindingTermArrow secondValue ≫ bindingContextArrow right) :
    IsIdemPushout (bindingTermArrow firstValue) (bindingTermArrow secondValue)
        (bindingContextArrow left) (bindingContextArrow right) square ↔
      ¬SharedOuterSlot left right :=
  ⟨binding_ipo_excludes_shared_outer_slot firstValue secondValue left right square,
    binding_ipo_of_no_shared_outer_slot firstValue secondValue left right square⟩

theorem substituted_bound_square {first second target : Scope S}
    (firstValue : Binding.Term S first.1 first.2) (secondValue : Binding.Term S second.1 second.2)
    (left : BindingContext S first target) (right : BindingContext S second target)
    (square : bindingTermArrow firstValue ≫ bindingContextArrow left =
      bindingTermArrow secondValue ≫ bindingContextArrow right)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination) :
    bindingTermArrow (S := S)
        (scope := ((substituteContext left destination sigma).holeContext, first.2))
        (Binding.bind (substituteContext left destination sigma).holeVariables firstValue) ≫
        bindingContextArrow (substituteContext left destination sigma).path =
      bindingTermArrow (S := S)
        (scope := ((substituteContext right destination sigma).holeContext, second.2))
        (Binding.bind (substituteContext right destination sigma).holeVariables secondValue) ≫
        bindingContextArrow (substituteContext right destination sigma).path := by
  have original : fillContext left firstValue = fillContext right secondValue := Arrow.value.inj square
  exact congrArg (bindingTermArrow (S := S) (scope := (destination, target.2)))
    ((substituteContext_fill left destination sigma firstValue).symm.trans
      ((congrArg (Binding.bind sigma) original).trans
        (substituteContext_fill right destination sigma secondValue)))

theorem binding_ipo_substitution_iff {first second target : Scope S}
    (firstValue : Binding.Term S first.1 first.2) (secondValue : Binding.Term S second.1 second.2)
    (left : BindingContext S first target) (right : BindingContext S second target)
    (square : bindingTermArrow firstValue ≫ bindingContextArrow left =
      bindingTermArrow secondValue ≫ bindingContextArrow right)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination) :
    IsIdemPushout
        (bindingTermArrow (S := S)
          (scope := ((substituteContext left destination sigma).holeContext, first.2))
          (Binding.bind (substituteContext left destination sigma).holeVariables firstValue))
        (bindingTermArrow (S := S)
          (scope := ((substituteContext right destination sigma).holeContext, second.2))
          (Binding.bind (substituteContext right destination sigma).holeVariables secondValue))
        (bindingContextArrow (substituteContext left destination sigma).path)
        (bindingContextArrow (substituteContext right destination sigma).path)
        (substituted_bound_square firstValue secondValue left right square destination sigma) ↔
      IsIdemPushout (bindingTermArrow firstValue) (bindingTermArrow secondValue)
        (bindingContextArrow left) (bindingContextArrow right) square := by
  rw [binding_ipo_iff_no_shared_outer_slot, binding_ipo_iff_no_shared_outer_slot]
  simp only [SharedOuterSlot, lastSlot_substitution]

end Mettapedia.OSLF.Binding.ScopedEncoding
