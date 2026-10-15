import Mettapedia.OSLF.Syntax.ScopedBindingContextPermission
import Mettapedia.OSLF.Syntax.ScopedBindingSubstitutionCoherence
import Mettapedia.CategoryTheory.GroundPathFramePermissionReadout

/-!+# Slot permissions through actual capture-avoiding substitution

A position permission selects a declared operator slot independently of the
ambient variable context. Substitution retains that operator and position,
substitutes every sibling under its own binder prefix, and computes the
complete inherited hole-variable map. Induction earns permission preservation
and reflection for the whole path, together with its unchanged frame count.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath

variable (S : Binding.Signature)

abbrev PositionPermission := (sort : S.Srt) → (operator : S.Op sort) →
  Fin (S.arity operator).length → Prop

def uniformSlotPermission (permission : PositionPermission S) : SlotPermission S :=
  fun _ sort operator position => permission sort operator position

variable {S}

local instance : Quiver (Scope S) := bindingFrameQuiver S

theorem substituteFrameSlot_permission_iff (permission : PositionPermission S)
    {context destination : Binding.Ctx S} {sort : S.Srt}
    (operator : S.Op sort) (position : Fin (S.arity operator).length)
    (siblings : (other : Fin (S.arity operator).length) → other ≠ position →
      Binding.Term S (((S.arity operator).get other).1 ++ context)
        ((S.arity operator).get other).2)
    (sigma : Binding.Sub S context destination) :
    framePermission S (uniformSlotPermission S permission)
        (substituteFrameSlot operator position siblings sigma) ↔
      framePermission S (uniformSlotPermission S permission)
        (BindingFrame.slot context sort operator position siblings) := Iff.rfl

theorem substituteContext_permission_iff (permission : PositionPermission S)
    {source target : Scope S} (context : BindingContext S source target) :
    ∀ (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination),
      FramePermission.PermittedPath (framePermission S (uniformSlotPermission S permission))
          (substituteContext context destination sigma).path ↔
        FramePermission.PermittedPath (framePermission S (uniformSlotPermission S permission))
          context := by
  induction context with
  | nil =>
    intro destination sigma
    exact ⟨fun _ => .nil _, fun _ => .nil _⟩
  | cons previous frame inductionHypothesis =>
    intro destination sigma
    cases frame with
    | slot original sort operator position siblings =>
      change FramePermission.PermittedPath _
          ((substituteContext previous (((S.arity operator).get position).1 ++ destination)
            (Binding.liftSub sigma ((S.arity operator).get position).1)).path.cons
              (substituteFrameSlot operator position siblings sigma)) ↔
        FramePermission.PermittedPath _
          (previous.cons (BindingFrame.slot original sort operator position siblings))
      rw [FramePermission.permittedPath_cons_iff, FramePermission.permittedPath_cons_iff,
        inductionHypothesis]
      rfl

theorem substituteContext_frame_count {source target : Scope S}
    (context : BindingContext S source target) :
    ∀ (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination),
      (substituteContext context destination sigma).path.length = context.length := by
  induction context with
  | nil => intro destination sigma; rfl
  | cons previous frame inductionHypothesis =>
    intro destination sigma
    cases frame with
    | slot original sort operator position siblings =>
      change (substituteContext previous (((S.arity operator).get position).1 ++ destination)
        (Binding.liftSub sigma ((S.arity operator).get position).1)).path.length + 1 =
          previous.length + 1
      exact congrArg (fun count => count + 1) (inductionHypothesis _ _)

def permittedSubstitutionContext (permission : PositionPermission S)
    {source target : Scope S} (context : BindingContext S source target)
    (allowed : FramePermission.PermittedPath
      (framePermission S (uniformSlotPermission S permission)) context)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination) :
    permittedInterface S (uniformSlotPermission S permission)
        ((substituteContext context destination sigma).holeContext, source.2) ⟶
      permittedInterface S (uniformSlotPermission S permission) (destination, target.2) :=
  permittedContextArrow (substituteContext context destination sigma).path
    ((substituteContext_permission_iff permission context destination sigma).mpr allowed)

theorem permittedSubstitutionContext_fill (permission : PositionPermission S)
    {source target : Scope S} (context : BindingContext S source target)
    (allowed : FramePermission.PermittedPath
      (framePermission S (uniformSlotPermission S permission)) context)
    (destination : Binding.Ctx S) (sigma : Binding.Sub S target.1 destination)
    (supplied : Binding.Term S source.1 source.2) :
    permittedTermArrow (S := S)
        (scope := ((substituteContext context destination sigma).holeContext, source.2))
        (Binding.bind (substituteContext context destination sigma).holeVariables supplied) ≫
        permittedSubstitutionContext permission context allowed destination sigma =
      permittedTermArrow (S := S) (scope := (destination, target.2))
        (permission := uniformSlotPermission S permission)
        (Binding.bind sigma (fillContext context supplied)) :=
  Subtype.ext (congrArg (bindingTermArrow (S := S) (scope := (destination, target.2)))
    (substituteContext_fill context destination sigma supplied).symm)

end Mettapedia.OSLF.Binding.ScopedEncoding
