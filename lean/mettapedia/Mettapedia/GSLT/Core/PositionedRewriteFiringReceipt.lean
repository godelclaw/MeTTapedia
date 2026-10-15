import Mettapedia.GSLT.Core.PositionedRewriteFrameTransport

/-!
# Indexed authored firing receipts and their actual transported events

The chosen origin, complete assignment and complete assay remain in the
receipt. A match proof earns the actual parameter instance by the frame's
pullback and hence the authored event. Transport retains this data and
recovers the entire supplied instance and event, including future inputs.
Equality of event endpoints does not identify receipt origins.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.PositionedRewriteFiringReceipt

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open ProgramReductionTheory AuthoredClosedTheory

universe u v w
variable {theory : Theory.{u,v}} {Origin : Type w}
variable (rules : Origin → Rule theory)
variable (frames : (origin : Origin) → PositionedRewriteModal.Frame (rules origin))

structure Receipt (context : theory.closed.Obj) where
  origin : Origin
  assignment : context ⟶ (frames origin).assignments
  assay : context ⟶ (frames origin).assay
  compatible : assignment ≫ (frames origin).focus = assay ≫ (frames origin).hole

namespace Receipt

variable {rules frames} {context : theory.closed.Obj}
variable (receipt : Receipt rules frames context)

def parameterInstance : context ⟶ (rules receipt.origin).parameters :=
  (frames receipt.origin).suppliedInstance receipt.assignment receipt.assay receipt.compatible

def event : context ⟶ theory.Event :=
  (frames receipt.origin).step receipt.assignment receipt.assay receipt.compatible

theorem parameterInstance_assignment : receipt.parameterInstance ≫ (frames receipt.origin).forget = receipt.assignment :=
  (frames receipt.origin).suppliedInstance_assignment _ _ _

theorem parameterInstance_assay : receipt.parameterInstance ≫ (frames receipt.origin).instantiate = receipt.assay :=
  (frames receipt.origin).suppliedInstance_assay _ _ _

theorem event_source : receipt.event ≫ theory.source = receipt.assay ≫ (frames receipt.origin).plug :=
  (frames receipt.origin).step_source _ _ _

theorem event_target : receipt.event ≫ theory.target = receipt.parameterInstance ≫ (rules receipt.origin).right :=
  (frames receipt.origin).step_target _ _ _

variable {target : Theory.{u,v}} (mapping : Map theory target)

def transport : Receipt (fun origin => (rules origin).transport mapping)
    (fun origin => (frames origin).transport mapping) (mapping.closed.functor.obj context) where
  origin := receipt.origin
  assignment := mapping.closed.functor.map receipt.assignment
  assay := mapping.closed.functor.map receipt.assay
  compatible := (frames receipt.origin).transported_match mapping _ _ receipt.compatible

theorem parameterInstance_transport : (receipt.transport mapping).parameterInstance = mapping.closed.functor.map receipt.parameterInstance :=
  (frames receipt.origin).suppliedInstance_transport mapping _ _ receipt.compatible

theorem event_transport :
    (receipt.transport mapping).event = mapping.closed.functor.map receipt.event ≫ mapping.reduction :=
  (frames receipt.origin).step_transport mapping _ _ receipt.compatible

theorem event_transport_source :
    (receipt.transport mapping).event ≫ target.source =
      mapping.closed.functor.map (receipt.event ≫ theory.source) ≫ mapping.program.hom := by
  rw [event_transport, Category.assoc, mapping.source, ← Category.assoc,
    ← mapping.closed.functor.map_comp]

theorem event_transport_target :
    (receipt.transport mapping).event ≫ target.target =
      mapping.closed.functor.map (receipt.event ≫ theory.target) ≫ mapping.program.hom := by
  rw [event_transport, Category.assoc, mapping.target, ← Category.assoc,
    ← mapping.closed.functor.map_comp]

variable {future : theory.closed.Obj} (incoming : future ⟶ context)

def precompose : Receipt rules frames future where
  origin := receipt.origin
  assignment := incoming ≫ receipt.assignment
  assay := incoming ≫ receipt.assay
  compatible := (frames receipt.origin).precomposed_match _ _ receipt.compatible incoming

theorem event_precompose : (receipt.precompose incoming).event = incoming ≫ receipt.event :=
  (frames receipt.origin).step_precompose _ _ receipt.compatible incoming

theorem event_transport_future :
    ((receipt.precompose incoming).transport mapping).event =
      mapping.closed.functor.map incoming ≫ (mapping.closed.functor.map receipt.event ≫ mapping.reduction) :=
  (frames receipt.origin).step_transport_future mapping _ _ receipt.compatible incoming

theorem origins_separate {second : Receipt rules frames context}
    (different : receipt.origin ≠ second.origin) : receipt ≠ second := by
  intro same
  exact different (congrArg Receipt.origin same)

theorem transported_origins_separate {second : Receipt rules frames context}
    (different : receipt.origin ≠ second.origin) : receipt.transport mapping ≠ second.transport mapping := by
  apply origins_separate
  exact different

end Receipt

end Mettapedia.GSLT.Core.PositionedRewriteFiringReceipt
