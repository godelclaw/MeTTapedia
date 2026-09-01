import Mettapedia.GraphTheory.Embedding.FaceCut
import Mettapedia.GraphTheory.PathChord

/-!
# Exact face cuts supplied by path chords

A chord together with a simple interval of the same path forms a simple
cycle.  In a connected cellular sphere embedding, that cycle therefore
determines an exact binary labeling of the faces on its two sides.

This module is the semantic bridge between graph-theoretic chord syntax and
the face-cut theory of finite combinatorial maps.  It does not assert that
two distinct chords are noncrossing.
-/

namespace Mettapedia.GraphTheory.Embedding

open Mettapedia.GraphTheory
open Mettapedia.GraphTheory.FourColor
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceBoundaryLinearAlgebra
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence
open Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCurvatureBulk
open Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceTwoSided
open Mettapedia.GraphTheory.FourColor.GoertzelV24WalkCycleParity
open Mettapedia.GraphTheory.FourColor.SimpleGraphDartRotation
open SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A same-path chord boundary in a connected cellular sphere map carries an
exact binary face cut supported precisely on its chord and intervening path
interval. -/
theorem exists_exactFaceCut_of_samePathChordBoundary
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (boundary : SamePathChordBoundary G) :
    ∃ cut : ExactFaceCut data.toRotationSystem
        (fun edge : G.edgeSet ↦ edge ∈ boundary.wall) F2,
      orbitFaceBoundaryLinearMap data.toRotationSystem cut.label =
        walkEdgeParity boundary.cycleWalk := by
  rcases exists_exactFaceCut_of_closedTrail data htwoSided hdual hconnected
      hsphere boundary.cycleWalk boundary.cycleWalk_isCycle.isTrail with
    ⟨cycleCut, hboundary⟩
  let wallCut : ExactFaceCut data.toRotationSystem
      (fun edge : G.edgeSet ↦ edge ∈ boundary.wall) F2 :=
    { label := cycleCut.label
      separates := by
        intro dart
        rw [cycleCut.separates]
        exact (boundary.mem_wall_iff_mem_cycleWalk_edges
          (data.toRotationSystem.edgeOf dart)).symm }
  exact ⟨wallCut, hboundary⟩

end

end Mettapedia.GraphTheory.Embedding
