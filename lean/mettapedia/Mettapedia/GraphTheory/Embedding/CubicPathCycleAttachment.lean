import Mettapedia.GraphTheory.CubicPathCycleAttachment
import Mettapedia.GraphTheory.Embedding.FaceCutCycleVertexSide
import Mettapedia.GraphTheory.Embedding.SimpleGraphRotation
import Mettapedia.GraphTheory.FourColor.CubicPathRotation

/-!
# Face sides of cubic-path attachments

For a path arc on a simple embedded cycle, a third edge that leaves the
cycle enters a definite face side.  At a cubic vertex that side is read
directly from the local rotation turn: one turn reads the forward path dart,
and the other reads the backward path dart.

The statement is generic embedding theory.  It does not mention colourings
or the four-colour compositional route.
-/

namespace Mettapedia.GraphTheory.Embedding

open Mettapedia.GraphTheory.CubicPathAttachment
open Mettapedia.GraphTheory.FourColor
open Mettapedia.GraphTheory.FourColor.CubicPathRotation
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence
open Mettapedia.GraphTheory.FourColor.SimpleGraphDartRotation
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {start finish : V}

/-- For the `backwardToAttachment` turn, the off-cycle endpoint lies on the
filled side selected by the forward path-dart face exactly when that face has
the selected label. -/
theorem filledCycleSide_attachmentNeighbor_iff_forwardDart_of_backwardTurn
    (data : Data G)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {path : G.Walk start finish} (closure : PathCycleClosure path)
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈
        (path.append closure.complement).edges) F2)
    (selected : F2)
    (hexterior : IsCycleExteriorAttachment closure hpath hregular position)
    (hturn : attachmentTurn data hpath hregular position =
      .backwardToAttachment) :
    cut.filledCycleSide data (path.append closure.complement) selected
        (attachmentNeighbor hpath hregular position) ↔
      cut.label (dartOrbitFace data.toRotationSystem
        (forwardDart position)) = selected := by
  let attachment := attachmentDart hpath hregular position
  have hneighbor : data.toRotationSystem.vertOf
      (data.toRotationSystem.alpha attachment) =
        attachmentNeighbor hpath hregular position := by
    change attachment.snd = attachmentNeighbor hpath hregular position
    exact attachmentDart_snd hpath hregular position
  have hoff : data.toRotationSystem.vertOf
      (data.toRotationSystem.alpha attachment) ∉
      (path.append closure.complement).support := by
    rw [hneighbor]
    exact hexterior
  rw [← hneighbor]
  rw [cut.filledCycleSide_iff_label_of_not_mem_support
    data hrotation (path.append closure.complement) selected
      (data.toRotationSystem.alpha attachment) hoff]
  have hlocal : data.IsVertexwiseCyclic :=
    (vertexRotationCyclic_iff_isVertexwiseCyclic data).mp hrotation
  have hcycle := rotationCycle_of_attachmentTurn_eq_backwardToAttachment
    data hlocal hpath hregular position hturn
  have hface : dartOrbitFace data.toRotationSystem
        (data.toRotationSystem.alpha attachment) =
      dartOrbitFace data.toRotationSystem (forwardDart position) := by
    calc
      dartOrbitFace data.toRotationSystem
          (data.toRotationSystem.alpha attachment) =
          dartOrbitFace data.toRotationSystem
            (data.toRotationSystem.rho attachment) :=
        dartOrbitFace_alpha_eq_dartOrbitFace_rho
          data.toRotationSystem attachment
      _ = dartOrbitFace data.toRotationSystem (forwardDart position) := by
        rw [Data.toRotationSystem_rho, hcycle.2.1]
  rw [hface]

/-- For the `forwardToAttachment` turn, the off-cycle endpoint lies on the
filled side selected by the backward path-dart face exactly when that face
has the selected label. -/
theorem filledCycleSide_attachmentNeighbor_iff_backwardDart_of_forwardTurn
    (data : Data G)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    {path : G.Walk start finish} (closure : PathCycleClosure path)
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (cut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet => edge.1 ∈
        (path.append closure.complement).edges) F2)
    (selected : F2)
    (hexterior : IsCycleExteriorAttachment closure hpath hregular position)
    (hturn : attachmentTurn data hpath hregular position =
      .forwardToAttachment) :
    cut.filledCycleSide data (path.append closure.complement) selected
        (attachmentNeighbor hpath hregular position) ↔
      cut.label (dartOrbitFace data.toRotationSystem
        (backwardDart position)) = selected := by
  let attachment := attachmentDart hpath hregular position
  have hneighbor : data.toRotationSystem.vertOf
      (data.toRotationSystem.alpha attachment) =
        attachmentNeighbor hpath hregular position := by
    change attachment.snd = attachmentNeighbor hpath hregular position
    exact attachmentDart_snd hpath hregular position
  have hoff : data.toRotationSystem.vertOf
      (data.toRotationSystem.alpha attachment) ∉
      (path.append closure.complement).support := by
    rw [hneighbor]
    exact hexterior
  rw [← hneighbor]
  rw [cut.filledCycleSide_iff_label_of_not_mem_support
    data hrotation (path.append closure.complement) selected
      (data.toRotationSystem.alpha attachment) hoff]
  have hlocal : data.IsVertexwiseCyclic :=
    (vertexRotationCyclic_iff_isVertexwiseCyclic data).mp hrotation
  have hcycle := rotationCycle_of_attachmentTurn_eq_forwardToAttachment
    data hlocal hpath hregular position hturn
  have hface : dartOrbitFace data.toRotationSystem
        (data.toRotationSystem.alpha attachment) =
      dartOrbitFace data.toRotationSystem (backwardDart position) := by
    calc
      dartOrbitFace data.toRotationSystem
          (data.toRotationSystem.alpha attachment) =
          dartOrbitFace data.toRotationSystem
            (data.toRotationSystem.rho attachment) :=
        dartOrbitFace_alpha_eq_dartOrbitFace_rho
          data.toRotationSystem attachment
      _ = dartOrbitFace data.toRotationSystem (backwardDart position) := by
        rw [Data.toRotationSystem_rho, hcycle.2.2]
  rw [hface]

end

end Mettapedia.GraphTheory.Embedding
