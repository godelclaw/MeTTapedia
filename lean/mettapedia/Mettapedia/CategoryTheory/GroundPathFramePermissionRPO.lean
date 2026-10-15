import Mettapedia.CategoryTheory.GroundPathFramePermission
import Mettapedia.GSLT.Logic.RelativePushoutFunctor

/-!
# Complete relative pushouts for permitted frames

Every ambient competitor below permitted interface bounds reconstructs its
apex, incoming paths and descent. Every compatible mediator reconstructs as
well. The ambient RPO comparison and existence follow from these actual
factor equations, without fullness of the permission inclusion.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.GroundPath.FramePermission

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout

universe u v w

variable {V : Type u} [Quiver.{v} V]
variable (permission : Permission V) (action : Action.{u,v,w} V)
variable {first second : V} {target : Object permission action}
variable {before : action.Value first} {redex : action.Value second}
variable {left : interface permission action first ⟶ target}
  {right : interface permission action second ⟶ target}

def liftCandidate (candidate : Candidate ((inclusion permission action).map (value permission action before))
    ((inclusion permission action).map (value permission action redex))
    ((inclusion permission action).map left) ((inclusion permission action).map right)) :
    Candidate (value permission action before) (value permission action redex) left right where
  apex := ⟨candidate.apex⟩
  inl := ⟨candidate.inl, (factors_permitted permission action candidate.inl candidate.down
    (candidate.fac_left.symm ▸ left.property)).1⟩
  inr := ⟨candidate.inr, (factors_permitted permission action candidate.inr candidate.down
    (candidate.fac_right.symm ▸ right.property)).1⟩
  down := ⟨candidate.down, (factors_permitted permission action candidate.inl candidate.down
    (candidate.fac_left.symm ▸ left.property)).2⟩
  comm := Subtype.ext candidate.comm
  fac_left := Subtype.ext candidate.fac_left
  fac_right := Subtype.ext candidate.fac_right

theorem liftCandidate_readout (candidate : Candidate
    ((inclusion permission action).map (value permission action before))
    ((inclusion permission action).map (value permission action redex))
    ((inclusion permission action).map left) ((inclusion permission action).map right)) :
    mapCandidate (inclusion permission action) (liftCandidate permission action candidate) = candidate := by
  cases candidate
  rfl

theorem map_mediates {candidate other : Candidate (value permission action before)
    (value permission action redex) left right} (mediator : candidate.apex ⟶ other.apex)
    (equations : Candidate.Mediates candidate other mediator) :
    Candidate.Mediates (mapCandidate (inclusion permission action) candidate)
      (mapCandidate (inclusion permission action) other) mediator.val :=
  ⟨congrArg Subtype.val equations.1, congrArg Subtype.val equations.2.1,
    congrArg Subtype.val equations.2.2⟩

theorem reflects_mediates {candidate other : Candidate (value permission action before)
    (value permission action redex) left right} (mediator : candidate.apex ⟶ other.apex)
    (equations : Candidate.Mediates (mapCandidate (inclusion permission action) candidate)
      (mapCandidate (inclusion permission action) other) mediator.val) :
    Candidate.Mediates candidate other mediator :=
  ⟨Subtype.ext equations.1, Subtype.ext equations.2.1, Subtype.ext equations.2.2⟩

def liftMediator {candidate other : Candidate (value permission action before)
    (value permission action redex) left right}
    (mediator : (inclusion permission action).obj candidate.apex ⟶
      (inclusion permission action).obj other.apex)
    (equations : Candidate.Mediates (mapCandidate (inclusion permission action) candidate)
      (mapCandidate (inclusion permission action) other) mediator) : candidate.apex ⟶ other.apex :=
  ⟨mediator, (factors_permitted permission action candidate.inl.val mediator
    (equations.1.symm ▸ other.inl.property)).2⟩

theorem relativePushout_iff (candidate : Candidate (value permission action before)
    (value permission action redex) left right) :
    IsRelativePushout candidate ↔
      IsRelativePushout (mapCandidate (inclusion permission action) candidate) := by
  constructor
  · intro universal other
    let original := liftCandidate permission action other
    obtain ⟨mediator, equations, unique⟩ := universal original
    refine ⟨mediator.val, map_mediates permission action mediator equations, ?_⟩
    intro alternative laws
    let lifted := liftMediator permission action (other := original) alternative laws
    exact congrArg Subtype.val (unique lifted (reflects_mediates permission action lifted laws))
  · intro universal other
    obtain ⟨mediator, equations, unique⟩ := universal (mapCandidate (inclusion permission action) other)
    let lifted := liftMediator permission action mediator equations
    refine ⟨lifted, reflects_mediates permission action lifted equations, ?_⟩
    intro alternative laws
    exact Subtype.ext (unique alternative.val (map_mediates permission action alternative laws))

theorem idemPushout_iff (square : value permission action before ≫ left =
    value permission action redex ≫ right) :
    IsIdemPushout (value permission action before) (value permission action redex) left right square ↔
      IsIdemPushout (valueArrow action before) (valueArrow action redex) left.val right.val
        (congrArg Subtype.val square) := by
  exact relativePushout_iff permission action
    (Candidate.self (value permission action before) (value permission action redex) left right square)

theorem redex_relativePushouts (supplied : action.Value first) (redex : action.Value second) :
    HasRelativePushouts (value permission action supplied) (value permission action redex) := by
  intro target left right square
  obtain ⟨ambient, universal⟩ := ground_hasRelativePushouts action supplied redex
    target.base left.val right.val (congrArg Subtype.val square)
  refine ⟨liftCandidate permission action ambient, (relativePushout_iff permission action _).mpr ?_⟩
  have read := liftCandidate_readout permission action (before := supplied) (redex := redex)
    (left := left) (right := right) ambient
  exact read.symm ▸ universal

end Mettapedia.CategoryTheory.GroundPath.FramePermission
