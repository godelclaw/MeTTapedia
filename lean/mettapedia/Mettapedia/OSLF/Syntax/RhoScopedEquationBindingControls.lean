import Mettapedia.OSLF.Syntax.RhoScopedEquationEventControls

/-!+# Binding transport with independently declared reaction permission

A communication occurrence beneath an input opens an actual new hole
context. Its continuation refers to the enclosing caller's name. Closing
that caller transports the full root assignment and path without capturing
the input-bound name. This occurrence belongs to the explicitly all-position
test profile and is excluded by the parallel-only reaction profile.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoScopedEquationBindingControls

open _root_.CategoryTheory RhoSchema ScopedEncoding ScopedEquationContexts ScopedEquationEvents
open Mettapedia.CategoryTheory.GroundPath
open RhoScopedEquationContextControls RhoScopedEquationEventControls

local instance : Quiver (Scope sig) := bindingFrameQuiver sig

def inputBodyFrame (context : Ctx sig) (channel : Term sig context Srt.nm) :
    BindingFrame sig (Srt.nm :: context, Srt.pr) (context, Srt.pr) :=
  .slot context Srt.pr Op.inp 1 (Fin.cases (fun _ => channel)
    (fun previous absent => by
      have only : previous = 0 := @Subsingleton.elim (Fin 1) inferInstance previous 0
      subst previous
      exact False.elim (absent rfl)))

def inputBodyContext : BindingContext sig ([Srt.nm, Srt.nm], Srt.pr) ([Srt.nm], Srt.pr) :=
  single (inputBodyFrame [Srt.nm] (.var .zero))

/-- The dependency variable and input-bound name precede the caller's name. -/
def enclosingContinuation : ContextualAssignment sig metas [Srt.nm, Srt.nm]
  | ⟨0, _⟩ => .op Op.drp (.cons (.var (.succ (.succ .zero))) .nil)

def closeUnderInput : Sub sig G [Srt.nm, Srt.nm]
  | _, .zero => .var .zero
  | _, .succ .zero => .op Op.nil .nil

def openRoot : ContextualRootEvents.Instance comm.unpositioned [Srt.nm, Srt.nm] where
  body := enclosingContinuation
  close := closeUnderInput

def underInput : Event rules allPositions ([Srt.nm], Srt.pr) where
  index := 0
  holeContext := [Srt.nm, Srt.nm]
  root := openRoot
  context := inputBodyContext
  permitted := .cons (.nil _) (by trivial)

def closeCaller : Sub sig [Srt.nm] []
  | _, .zero => chan

def expectedOpenTarget : Term sig [Srt.nm] Srt.pr :=
  .op Op.inp (.cons (.var .zero)
    (.cons (.op Op.drp (.cons (.var (.succ .zero)) .nil)) .nil))

def capturedOpenTarget : Term sig [Srt.nm] Srt.pr :=
  .op Op.inp (.cons (.var .zero)
    (.cons (.op Op.drp (.cons (.var .zero) .nil)) .nil))

def expectedClosedTarget : Term sig [] Srt.pr :=
  .op Op.inp (.cons chan (.cons (.op Op.drp (.cons (weaken chan) .nil)) .nil))

def capturedClosedTarget : Term sig [] Srt.pr :=
  .op Op.inp (.cons chan (.cons (.op Op.drp (.cons (.var .zero) .nil)) .nil))

theorem actual_open_target : underInput.target = expectedOpenTarget := rfl

theorem actual_closed_target : (underInput.map [] closeCaller).target = expectedClosedTarget := rfl

theorem open_capture_changes_readout : underInput.target ≠ capturedOpenTarget := by
  rw [actual_open_target]
  intro same
  cases same

theorem closed_capture_changes_readout :
    (underInput.map [] closeCaller).target ≠ capturedClosedTarget := by
  rw [actual_closed_target]
  intro same
  cases same

theorem opened_hole_context : (underInput.map [] closeCaller).holeContext = [Srt.nm] := rfl

theorem input_fresh_name_retained :
    (substituteContext underInput.context [] closeCaller).holeVariables Srt.nm .zero =
      .var .zero := rfl

theorem caller_name_closed :
    (substituteContext underInput.context [] closeCaller).holeVariables Srt.nm (.succ .zero) =
      weaken chan := rfl

theorem closed_source_square :
    (underInput.map [] closeCaller).sourceClass rhoSourceE =
      bindQ closeCaller (underInput.sourceClass rhoSourceE) :=
  Event.sourceClass_map rhoSourceE [] closeCaller underInput

theorem closed_target_square :
    (underInput.map [] closeCaller).targetClass rhoSourceE =
      bindQ closeCaller (underInput.targetClass rhoSourceE) :=
  Event.targetClass_map rhoSourceE [] closeCaller underInput

theorem complete_identity :
    underInput.map [Srt.nm] (fun _ position => .var position) = underInput :=
  Event.map_id underInput

theorem complete_composition (first : Sub sig [Srt.nm] [Srt.nm, Srt.nm])
    (second : Sub sig [Srt.nm, Srt.nm] []) :
    (underInput.map [Srt.nm, Srt.nm] first).map [] second =
      underInput.map [] (fun sort position => bind second (first sort position)) :=
  Event.map_comp _ _ first second underInput

/-- Actual substitution also preserves the reaction origin and frame count. -/
theorem retained_full_origin_and_length :
    (underInput.map [] closeCaller).index = underInput.index ∧
      (underInput.map [] closeCaller).context.length = underInput.context.length :=
  ⟨Event.complete_origin_map [] closeCaller underInput,
    Event.reaction_length_map [] closeCaller underInput⟩

/-- The inactive input body is not granted a parallel-only reaction. -/
theorem input_body_not_parallel_permitted :
    ¬ FramePermission.PermittedPath
      (framePermission sig (uniformSlotPermission sig parallelPermission)) inputBodyContext := by
  intro permitted
  cases permitted with
  | cons _ last => exact last

/-- Consequently this exact authored path cannot supply a parallel-profile
event, even though its all-position counterpart has checked binding laws. -/
theorem no_parallel_event_at_this_path :
    ¬ ∃ event : Event rules parallelPermission ([Srt.nm], Srt.pr),
      event.holeContext = [Srt.nm, Srt.nm] ∧ HEq event.context inputBodyContext := by
  rintro ⟨event, contextEq, pathEq⟩
  rcases event with ⟨index, holeContext, root, context, permitted⟩
  dsimp at contextEq pathEq
  subst holeContext
  have paths : context = inputBodyContext := eq_of_heq pathEq
  subst context
  exact input_body_not_parallel_permitted permitted

end Mettapedia.OSLF.Binding.RhoScopedEquationBindingControls
