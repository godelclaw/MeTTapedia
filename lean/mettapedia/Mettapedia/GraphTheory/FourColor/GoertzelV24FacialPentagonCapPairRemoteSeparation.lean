import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceVertexSeparation
import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapDeletedBoundaryCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapPairBoundaryFaces

/-!
# Dual-distance criterion for remote facial pentagon caps

Formation rung C-4 must obtain the simultaneous-opening separation condition
from the source corridor, rather than assume it at the annular-cellulation
constructor.  This file isolates the exact local bridge.

Every retained-side spoke face is adjacent in the full facial dual to the
named pentagonal cap face.  Consequently, if the two cap faces have no common
dual neighbour, no ambient face can meet both cap interfaces.  The remaining
source task is therefore quantitative selection of cap faces at dual distance
greater than two; it is not a new surface-surgery premise.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCapPairRemoteSeparation

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24CubicFaceVertexSeparation
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapDeletedBoundaryCycle
open GoertzelV24FacialPentagonCapOpenBoundary
open GoertzelV24FacialPentagonCapPairBoundaryFaces
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PentagonCapOpening

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype

namespace FacialPentagonCapBoundaryWalk

variable {data : Data G}

/-- Every recorded boundary dart belongs to the named facial orbit. -/
theorem dartOrbitFace_boundaryDart_eq_faceDart
    (walk : FacialPentagonCapBoundaryWalk data) (step : Fin 5) :
    dartOrbitFace data.toRotationSystem (walk.boundaryDart step) =
      dartOrbitFace data.toRotationSystem
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.faceDart := by
  rw [walk.faceDart_eq_boundaryDart_zero]
  have hnext (index : Fin 5) :
      dartOrbitFace data.toRotationSystem (walk.boundaryDart (index + 1)) =
        dartOrbitFace data.toRotationSystem (walk.boundaryDart index) := by
    rw [← walk.boundaryDart_phi index]
    exact dartOrbitFace_phi_eq data.toRotationSystem (walk.boundaryDart index)
  fin_cases step
  · rfl
  · exact hnext 0
  · exact (hnext 1).trans (hnext 0)
  · exact (hnext 2).trans ((hnext 1).trans (hnext 0))
  · exact (hnext 3).trans ((hnext 2).trans ((hnext 1).trans (hnext 0)))

/-- The retained-side face at a named spoke is distinct from the cap face.
The spoke belongs to the former and is excluded from the latter's exact
five-cycle edge support. -/
theorem boundaryFace_ne_capFace
    (walk : FacialPentagonCapBoundaryWalk data) (step : Fin 5) :
    dartOrbitFace data.toRotationSystem
        (PentagonCap.openBoundaryDart data
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
          step).1.1 ≠
      dartOrbitFace data.toRotationSystem
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.faceDart := by
  intro hfaces
  let cap := walk.toOrientedFacialPentagonCap.toFacialPentagonCap
  let boundary := PentagonCap.openBoundaryDart data cap.toPentagonCap step
  have hedge := edgeOf_mem_orbitFaceBoundary_dartOrbitFace
    data.toRotationSystem boundary.1.1
  rw [hfaces, orbitFaceBoundary_dartOrbitFace_eq_faceEdges] at hedge
  have hedgeEq : data.toRotationSystem.edgeOf boundary.1.1 =
      cap.toPentagonCap.spokeEdge step := by
    apply Subtype.ext
    simp [boundary, cap, PentagonCap.openBoundaryDart,
      GoertzelV24PentagonCapOpeningComparison.PentagonCap.spokeBoundaryDart,
      SimpleGraphDartRotation.Data.toRotationSystem_edgeOf,
      SimpleGraph.Dart.edge, cap.toPentagonCap.spokeEdge_eq step]
  rw [hedgeEq] at hedge
  apply cap.spokeEdge_not_mem_faceEdges step
  exact hedge

/-- A retained-side spoke face is one edge away from its named cap face in
the full facial dual.  This is the local geometric atom behind remote
two-cap separation. -/
theorem boundaryFace_adj_capFace
    (walk : FacialPentagonCapBoundaryWalk data)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (step : Fin 5) :
    (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Adj
      (orbitFaceVertex data.toRotationSystem
        (PentagonCap.openBoundaryDart data
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
          step).1.1)
      (orbitFaceVertex data.toRotationSystem
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.faceDart) := by
  let cap := walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
  let boundary := (PentagonCap.openBoundaryDart data cap step).1.1
  apply interiorDualGraph_adj_of_distinct_faces_share_vertex
    data.toRotationSystem hcubic hrotation htwoSided
      (boundaryFace_ne_capFace walk step)
      (leftDart := data.toRotationSystem.phi boundary)
      (rightDart := walk.boundaryDart step)
  · rw [mem_orbitFaceDarts_iff, dartOrbitFace_phi_eq]
  · rw [mem_orbitFaceDarts_iff]
    exact dartOrbitFace_boundaryDart_eq_faceDart walk step
  · calc
      data.toRotationSystem.vertOf (data.toRotationSystem.phi boundary) =
          data.toRotationSystem.vertOf (data.toRotationSystem.alpha boundary) :=
        data.toRotationSystem.vert_phi_eq_vert_alpha boundary
      _ = cap.vertex step := by
        simp [boundary, cap,
          GoertzelV24PentagonCapOpeningComparison.PentagonCap.spokeBoundaryDart,
          SimpleGraphDartRotation.Data.toRotationSystem_alpha]
      _ = data.toRotationSystem.vertOf (walk.boundaryDart step) := by
        simpa only [SimpleGraphDartRotation.Data.toRotationSystem_vertOf] using
          (FacialPentagonCapBoundaryWalk.boundaryDart_fst_eq_vertex
            walk step).symm

end FacialPentagonCapBoundaryWalk

/-- The cap faces have dual distance greater than two, stated without choosing
a shortest-path API: no full-dual face is adjacent to both named cap faces. -/
def CapFacesHaveNoCommonDualNeighbor
    {data : Data G} (caps : FacialPentagonCapBoundaryWalkPair data) : Prop :=
  ¬ ∃ middle : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)),
    (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Adj
        (orbitFaceVertex data.toRotationSystem
          caps.inner.toOrientedFacialPentagonCap.toFacialPentagonCap.faceDart)
        middle ∧
    (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Adj
        middle
        (orbitFaceVertex data.toRotationSystem
          caps.outer.toOrientedFacialPentagonCap.toFacialPentagonCap.faceDart)

namespace FacialPentagonCapBoundaryWalkPair

variable {data : Data G}

/-- Dual distance greater than two between the selected cap faces discharges
the exact remote-boundary premise consumed by the literal two-cap opening. -/
theorem remoteBoundaryFacesSeparated_of_noCommonDualNeighbor
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hremote : CapFacesHaveNoCommonDualNeighbor caps) :
    RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair := by
  intro innerStep outerStep hsame
  apply hremote
  let pair := caps.toPentagonCapPair
  let innerBoundary := pair.innerBoundaryDart innerStep
  let outerBoundary := pair.outerBoundaryDart outerStep
  let middle := orbitFaceVertex data.toRotationSystem innerBoundary
  have hfaces :
      dartOrbitFace data.toRotationSystem innerBoundary =
        dartOrbitFace data.toRotationSystem outerBoundary := by
    exact Quotient.sound hsame
  refine ⟨middle, ?_, ?_⟩
  · exact (FacialPentagonCapBoundaryWalk.boundaryFace_adj_capFace
      caps.inner hcubic hrotation htwoSided innerStep).symm
  · have hadj := FacialPentagonCapBoundaryWalk.boundaryFace_adj_capFace
      caps.outer hcubic hrotation htwoSided outerStep
    change (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Adj
        middle
        (orbitFaceVertex data.toRotationSystem
          caps.outer.toOrientedFacialPentagonCap.toFacialPentagonCap.faceDart)
    have hmiddle : middle = orbitFaceVertex data.toRotationSystem outerBoundary := by
      apply Subtype.ext
      exact hfaces
    rw [hmiddle]
    exact hadj

end FacialPentagonCapBoundaryWalkPair

end

end GoertzelV24FacialPentagonCapPairRemoteSeparation

end Mettapedia.GraphTheory.FourColor
