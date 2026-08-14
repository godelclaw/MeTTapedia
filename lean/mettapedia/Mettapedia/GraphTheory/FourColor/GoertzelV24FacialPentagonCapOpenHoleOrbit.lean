import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapDeletedBoundaryCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionBoundaryOrbit
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondBoundaryOrder

/-!
# The opened hole orbit of a facial pentagon cap

This module completes the local-to-open part of formation rung C-2.  The
facial cap calculation already places all five spoke darts in one cycle of
the capped deleted-side face permutation.  Here the literal cap cycle first
proves that the deleted induced side is connected.  The planar-bond boundary
order then transfers the computed cycle to the retained first-return order,
and the open-region rotation realizes that order as one actual face orbit.

The remaining source-facing hypothesis is connectedness of the retained
complement of the cap.  It is stated explicitly: this file does not infer it
from the picture of a facial pentagon, and it does not postulate any global
two-sidedness property for the opened rotation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCapOpenHoleOrbit

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapDeletedBoundaryCycle
open GoertzelV24FacialPentagonCapOpenBoundary
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenRegionBoundaryOrbit
open GoertzelV24OpenRegionRotation
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PentagonCapOpening
open GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24RetainedRegionBoundaryOrder

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-! Keep the literal subtype instances used by the cap boundary carrier. -/
attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexFintype
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

namespace OrientedFacialPentagonCap

variable {data : Data G}

/-- Consecutive named vertices of an oriented facial cap are adjacent in the
ambient graph. -/
theorem adjacent_next (cap : OrientedFacialPentagonCap data) (step : Fin 5) :
    G.Adj
      (cap.toFacialPentagonCap.toPentagonCap.vertex step)
      (cap.toFacialPentagonCap.toPentagonCap.vertex (step + 1)) := by
  have hedge :=
    (cap.toFacialPentagonCap.toPentagonCap.cycleEdge step).property
  rw [cap.cycleEdge_eq_vertices step] at hedge
  exact (SimpleGraph.mem_edgeSet G).mp hedge

/-- The five cap vertices form a connected induced side.  This discharges the
deleted-side connectedness premise of the planar-bond boundary-order theorem
from the literal cap cycle rather than carrying it as formation data. -/
theorem induce_vertexSupport_connected
    (cap : OrientedFacialPentagonCap data) :
    (G.induce
      (↑cap.toFacialPentagonCap.toPentagonCap.vertexSupport : Set V)).Connected := by
  let support := cap.toFacialPentagonCap.toPentagonCap.vertexSupport
  have hmem (step : Fin 5) :
      cap.toFacialPentagonCap.toPentagonCap.vertex step ∈ support :=
    (cap.toFacialPentagonCap.toPentagonCap.mem_vertexSupport_iff _).mpr
      ⟨step, rfl⟩
  let capVertex (step : Fin 5) :
      {vertex // vertex ∈ support} :=
    ⟨cap.toFacialPentagonCap.toPentagonCap.vertex step, hmem step⟩
  have hadj (step : Fin 5) :
      (G.induce (↑support : Set V)).Adj
        (capVertex step) (capVertex (step + 1)) := by
    exact adjacent_next cap step
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨capVertex 0, ?_⟩
  intro vertex
  rcases vertex with ⟨vertex, hvertex⟩
  rcases (cap.toFacialPentagonCap.toPentagonCap.mem_vertexSupport_iff vertex).mp
      hvertex with ⟨step, rfl⟩
  have htarget :
      (⟨cap.toFacialPentagonCap.toPentagonCap.vertex step, hvertex⟩ :
        {vertex // vertex ∈ support}) = capVertex step :=
    Subtype.ext (by rfl)
  change (G.induce (↑support : Set V)).Reachable (capVertex 0)
    ⟨cap.toFacialPentagonCap.toPentagonCap.vertex step, hvertex⟩
  rw [htarget]
  fin_cases step
  · exact .rfl
  · exact (hadj 0).reachable
  · exact (hadj 0).reachable.trans (hadj 1).reachable
  · exact ((hadj 0).reachable.trans (hadj 1).reachable).trans
      (hadj 2).reachable
  · exact (((hadj 0).reachable.trans (hadj 1).reachable).trans
      (hadj 2).reachable).trans (hadj 3).reachable

end OrientedFacialPentagonCap

variable {data : Data G}

/-- Planar-bond transfer puts all five source-ordered cap spokes in one cycle
of the retained first-return boundary order.  The deleted-side connectedness
premise is supplied internally by the literal pentagon cycle; only the
retained complement remains a source-formation obligation. -/
theorem retainedBoundarySuccessor_openBoundary_sameCycle
    (walk : FacialPentagonCapBoundaryWalk data)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex |
        deletedRegionKeep
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport
          vertex}).Connected)
    (first second : Fin 5) :
    (retainedRegionBoundarySuccessor data.toRotationSystem
      (deletedRegionKeep
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport)).SameCycle
      (PentagonCap.openBoundaryDart data
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap first)
      (PentagonCap.openBoundaryDart data
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap second) := by
  let cap := walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
  have hdeletedConnected :
      (G.induce {vertex | Not (deletedRegionKeep cap.vertexSupport vertex)}).Connected := by
    have hdeletedSet :
        {vertex | Not (deletedRegionKeep cap.vertexSupport vertex)} =
          (cap.vertexSupport : Set V) := by
      ext vertex
      simp [deletedRegionKeep]
    rw [hdeletedSet]
    exact
      GoertzelV24FacialPentagonCapOpenHoleOrbit.OrientedFacialPentagonCap.induce_vertexSupport_connected
        walk.toOrientedFacialPentagonCap
  have horder := retained_boundarySuccessor_eq_deleted_inverse_of_planar_bond
    data cap.vertexSupport hsphere htwoSided hconnected hrotation
      hretainedConnected hdeletedConnected
  rw [horder, Equiv.Perm.sameCycle_inv]
  exact deletedRegionBoundarySuccessor_openBoundary_sameCycle
    walk hcubic hrotation first second

/-- The five fresh stubs created by opening a facial pentagon cap lie on one
literal face orbit of the opened rotation.  This is the C-2 hole-orbit
conclusion for one cap, conditional on the stated closed-map hypotheses and
connectedness of the retained complement supplied by source formation. -/
theorem openedHoleFace_stub_eq
    (walk : FacialPentagonCapBoundaryWalk data)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hretainedConnected :
      (G.induce {vertex |
        deletedRegionKeep
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport
          vertex}).Connected)
    (first second : Fin 5) :
    dartOrbitFace
        (rotationSystem data.toRotationSystem
          (PentagonCap.keep
            walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
          (Sum.inl (PentagonCap.openBoundaryDart data
            walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap 0).1))
        (Sum.inr (PentagonCap.openBoundaryDart data
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap first)) =
      dartOrbitFace
        (rotationSystem data.toRotationSystem
          (PentagonCap.keep
            walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
          (Sum.inl (PentagonCap.openBoundaryDart data
            walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap 0).1))
        (Sum.inr (PentagonCap.openBoundaryDart data
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap second)) := by
  apply dartOrbitFace_stub_eq_of_boundarySuccessor_sameCycle
  exact retainedBoundarySuccessor_openBoundary_sameCycle walk hsphere htwoSided
    hconnected hcubic hrotation hretainedConnected first second

end

end GoertzelV24FacialPentagonCapOpenHoleOrbit

end Mettapedia.GraphTheory.FourColor
