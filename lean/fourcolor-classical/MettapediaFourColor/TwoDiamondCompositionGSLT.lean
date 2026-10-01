import MettapediaFourColor.TwoDiamondConfigurations
import Mettapedia.GSLT.Core.RelationalRouteSemantics
import Mettapedia.GSLT.Core.ProofRelevantPresentation

/-!
# Joint diamond choices compose into actual reference colourings

The first operation reconstructs the complete graph from a boundary colouring
and two summaries agreeing at their shared tip. The second transports that
witness to the original configuration hypermap. Every reference colouring
admits such a compatible history, with arbitrary final observations retained.
This construction supplies neither an initial compatible choice nor coverage.
-/

namespace FourColor.TwoDiamondCompositionGSLT

open TwoDiamondConfigurations
open Mettapedia.GSLT Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.RelationalRouteSemantics Mettapedia.GSLT.ProofRelevantPresentation
open Mettapedia.GSLT.LooseRelationEquipment

inductive Member where | three | six
inductive Interface where | pieces | assembled | reference

def State : Member → Interface → Type
  | .three, .pieces => Plan003 Color
  | .three, .assembled => graph003.Coloring Color
  | .three, .reference => {k : (cfmap cf003).Dart → Color // (cfmap cf003).map.Coloring k}
  | .six, .pieces => Plan006 Color
  | .six, .assembled => graph006.Coloring Color
  | .six, .reference => {k : (cfmap cf006).Dart → Color // (cfmap cf006).map.Coloring k}

inductive Event : Interface → Interface → Type where
  | assemble : Event .pieces .assembled
  | represent : Event .assembled .reference

def theory : GSLT where
  Term := Interface
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := Nonempty (Event source target)
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def presentation : StepPresentation theory where
  Evidence := Event
  erases_iff := fun _ _ => Iff.rfl

noncomputable def execute (m : Member) :
    {a b : Interface} → Event a b → State m a ≃ State m b
  | _, _, .assemble => match m with
    | .three => (planEquiv003 Color).symm
    | .six => (planEquiv006 Color).symm
  | _, _, .represent => match m with
    | .three => faces003.coloringEquiv.trans realization003.coloringEquiv.symm
    | .six => faces006.coloringEquiv.trans realization006.coloringEquiv.symm

noncomputable def semantics (m : Member) : Semantics Event where
  State := State m
  step event x y := EqWitness (execute m event x) y

def route : Route Event .pieces .reference :=
  .cons .assemble (.cons .represent (.refl _))

noncomputable def assembled (m : Member) : State m .pieces ≃ State m .reference :=
  (execute m .assemble).trans (execute m .represent)

noncomputable def witness (m : Member) (x : State m .pieces) :
    (semantics m).Witness route x (assembled m x) :=
  ⟨execute m .assemble x, ⟨⟨rfl⟩⟩,
    execute m .represent (execute m .assemble x), ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩⟩

theorem supported_iff (m : Member) (x : State m .pieces) (y : State m .reference) :
    (semantics m).Supports route x y ↔ assembled m x = y := by
  constructor
  · rintro ⟨⟨middle, first, last, second, final⟩⟩
    exact (congrArg (execute m .represent) first.down.down).trans
      (second.down.down.trans final.down.down)
  · intro h; subst y; exact ⟨witness m x⟩

theorem every_coloring (m : Member) (y : State m .reference) :
    ∃ x, (semantics m).Supports route x y :=
  ⟨(assembled m).symm y, (supported_iff m _ _).mpr ((assembled m).apply_symm_apply y)⟩

theorem viable_iff (m : Member) (accepts : State m .reference → Prop) :
    (∃ x, (semantics m).Viable route accepts x) ↔ ∃ y, accepts y := by
  constructor
  · rintro ⟨x, y, _, hy⟩; exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := every_coloring m y
    exact ⟨x, y, hx, hy⟩

end FourColor.TwoDiamondCompositionGSLT
