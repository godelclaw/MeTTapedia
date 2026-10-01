import Mettapedia.GraphTheory.FourColor.DualTruncateFacePhaseKempe
import Mettapedia.GSLT.Core.Ultrainfinite
import Mettapedia.GSLT.Core.ProofRelevantPresentation

/-!
# Authored physical face-phase repair routes

States are actual target Tait witnesses sharing one compatible source
choice. Each event retains the chosen colour pair and the exact physical
update. The three-stage route normalizes the witness; every authored route
preserves the joint cross field. No independent choices are made at seams.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateFacePhaseGSLT

open DualTruncateColoring DualTruncateFacePhaseKempe
open GoertzelV24HexagonPairingTargetAwareBoundary
open Mettapedia.GSLT Mettapedia.GSLT.Ultrainfinite Mettapedia.GSLT.ProofRelevantPresentation

noncomputable section
universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem.{u,u,u} V E) (w : ThreeVertexColoring RS)

/-- Retain the pair label, including when the selected region is empty. -/
abbrev Event (source target : State RS w) : Type u :=
  ULift.{u} {pair : TaitColorPair // target = step RS w source pair}

def theory : GSLT.{u} where
  Term := State RS w
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => Nonempty (Event RS w source target)
  rewrites_resp_left := by
    intro source source' target equal event
    subst source'
    exact ⟨target,event,rfl⟩
  rewrites_resp_right := by
    intro source target target' event equal
    subst target'
    exact event

def presentation : StepPresentation (theory RS w) where
  Evidence := Event RS w
  erases_iff := fun _ _ => Iff.rfl

theorem event_physical {source target : State RS w} (event : Event RS w source target) :
    RotationPatchKempe.Region (rotation RS) (fun _ => True) source.colouring
        event.down.val (mask RS w source event.down.val) ∧
      (target.colouring : Edge RS → Color) = RotationPatchKempe.switched source.colouring
        event.down.val (mask RS w source event.down.val) := by
  refine ⟨physical_region RS w source _, ?_⟩
  exact (congrArg (fun s : State RS w => (s.colouring : Edge RS → Color))
    event.down.property).trans (exact_effect RS w source _)

theorem event_cross_preserved {source target : State RS w}
    (event : Event RS w source target) (e : E) :
    target.colouring (.inl e) = source.colouring (.inl e) := by
  rw [event.down.property]
  exact step_cross_preserved RS w source _ e

def PhysicalEvent {source target : State RS w} (event : Event RS w source target) : Prop :=
  RotationPatchKempe.Region (rotation RS) (fun _ => True) source.colouring
    event.down.val (mask RS w source event.down.val) ∧
  (target.colouring : Edge RS → Color) = RotationPatchKempe.switched source.colouring
    event.down.val (mask RS w source event.down.val)

/-- Each intermediate field is the genuine switched field of its predecessor. -/
def PhysicalHistory : {source target : State RS w} → Route (Event RS w) source target → Prop
  | _, _, .refl _ => True
  | _, _, .cons event rest => PhysicalEvent RS w event ∧ PhysicalHistory rest

theorem physical_history {source target : State RS w}
    (history : Route (Event RS w) source target) : PhysicalHistory RS w history := by
  induction history with
  | refl => trivial
  | cons event rest ih => exact ⟨event_physical RS w event, ih⟩

/-- Conservation composes over arbitrary authored histories. -/
theorem route_cross_preserved {source target : State RS w}
    (history : Route (Event RS w) source target) (e : E) :
    target.colouring (.inl e) = source.colouring (.inl e) := by
  exact (Route.observe_eq_of_route (fun s : State RS w => s.colouring (.inl e))
    (fun event => (event_cross_preserved RS w event e).symm) history).symm

def repair (source : State RS w) :
    Route (Event RS w) source (normalize RS w source) :=
  .cons ⟨⟨.redBlue,rfl⟩⟩
    (.cons ⟨⟨.redPurple,rfl⟩⟩ (.cons ⟨⟨.bluePurple,rfl⟩⟩ (.refl _)))

theorem repair_length (source : State RS w) : (repair RS w source).length = 3 := rfl

theorem repair_terminal (source : State RS w) :
    (normalize RS w source).colouring = DualTruncateColoring.colouring RS w :=
  normalize_exact RS w source

end
end Mettapedia.GraphTheory.FourColor.DualTruncateFacePhaseGSLT
