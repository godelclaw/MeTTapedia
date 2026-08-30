import Mettapedia.GraphTheory.FourColor.GoertzelV24KauffmanFacePotential
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSidePrimalKempeTrail
import Mettapedia.GraphTheory.FourColor.GoertzelV24WalkCycleParity

/-!
# Exact face-side certificates for graph-backed physical Kempe cycles

A boundary-free physical bichromatic component in a literal graph shore
contracts to an ambient simple cycle.  On a connected spherical map, the
binary edge vector of that cycle is an exact sum of orbit-face boundaries.
This file packages the resulting face-side certificate without asserting
connectedness of either face class or constructing a geometric noose.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24VertexSidePrimalKempeFaceSeparator

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexagonPairingTargetAwareBoundary
open GoertzelV24KauffmanFacePotential
open GoertzelV24OpenTangleComposition
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PortTangleCommonKempeWeb
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleKempeEndpoints
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24VertexSidePrimalKempeTrail
open GoertzelV24WalkCycleParity

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A simple closed walk in a connected spherical map is exactly the binary
boundary of a face set: an edge occurs in the walk precisely when its two
incident orbit faces lie on opposite sides of that set. -/
theorem exists_faceSet_separates_iff_mem_walk_of_isCycle
    (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {vertex : V} (walk : G.Walk vertex vertex) (hcycle : walk.IsCycle) :
    ∃ faces : Finset (OrbitFace data.toRotationSystem),
      ∀ dart : data.toRotationSystem.D,
        (data.toRotationSystem.edgeOf dart).1 ∈ walk.edges ↔
          ((dartOrbitFace data.toRotationSystem dart ∈ faces ∧
              dartOrbitFace data.toRotationSystem
                (data.toRotationSystem.alpha dart) ∉ faces) ∨
            (dartOrbitFace data.toRotationSystem dart ∉ faces ∧
              dartOrbitFace data.toRotationSystem
                (data.toRotationSystem.alpha dart) ∈ faces)) := by
  have hchain := walkEdgeParity_mem_f2CycleSpace_of_closed walk
  rcases exists_faceSet_separates_iff_eq_one_of_mem_f2CycleSpace
      data hclass htwoSided hchain with ⟨faces, hfaces⟩
  refine ⟨faces, fun dart => ?_⟩
  calc
    (data.toRotationSystem.edgeOf dart).1 ∈ walk.edges ↔
        walkEdgeParity walk (data.toRotationSystem.edgeOf dart) = 1 :=
      (walkEdgeParity_apply_eq_one_iff_mem_edges_of_isTrail
        hcycle.isTrail (data.toRotationSystem.edgeOf dart)).symm
    _ ↔
        ((dartOrbitFace data.toRotationSystem dart ∈ faces ∧
            dartOrbitFace data.toRotationSystem
              (data.toRotationSystem.alpha dart) ∉ faces) ∨
          (dartOrbitFace data.toRotationSystem dart ∉ faces ∧
            dartOrbitFace data.toRotationSystem
              (data.toRotationSystem.alpha dart) ∈ faces)) :=
      hfaces dart

/-- The ambient cycle obtained from a boundary-free physical component comes
with the exact spherical face-side certificate of its edge support. -/
theorem exists_ambientPrimalKempeCycle_faceSetSeparator_of_boundaryFree
    (graphData : Data G)
    (hclass : BridgelessSphericalCubicMapData
      graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (keep : V → Prop)
    (outer : RetainedDart graphData.toRotationSystem keep)
    (coloring : Coloring (vertexSidePortTangle graphData keep outer))
    (hproper : IsProper coloring) (pair : TaitColorPair)
    (root : ActiveDart
      (vertexSidePortTangle graphData keep outer) coloring pair)
    (hboundaryFree : componentPortDarts
      (vertexSidePortTangle graphData keep outer) coloring pair root = ∅) :
    ∃ walk : G.Walk
        ((vertexSidePortTangle graphData keep outer).vert root.1).1
        ((vertexSidePortTangle graphData keep outer).vert root.1).1,
      walk.IsCycle ∧
        ∃ faces : Finset (OrbitFace graphData.toRotationSystem),
          ∀ dart : graphData.toRotationSystem.D,
            (graphData.toRotationSystem.edgeOf dart).1 ∈ walk.edges ↔
              ((dartOrbitFace graphData.toRotationSystem dart ∈ faces ∧
                  dartOrbitFace graphData.toRotationSystem
                    (graphData.toRotationSystem.alpha dart) ∉ faces) ∨
                (dartOrbitFace graphData.toRotationSystem dart ∉ faces ∧
                  dartOrbitFace graphData.toRotationSystem
                    (graphData.toRotationSystem.alpha dart) ∈ faces)) := by
  rcases exists_ambientPrimalKempeCycle_of_boundaryFree
      graphData keep outer hclass.spherical.cubic coloring hproper pair root
      hboundaryFree with ⟨walk, hcycle⟩
  rcases exists_faceSet_separates_iff_mem_walk_of_isCycle
      graphData hclass htwoSided walk hcycle with ⟨faces, hfaces⟩
  exact ⟨walk, hcycle, faces, hfaces⟩

end

end GoertzelV24VertexSidePrimalKempeFaceSeparator

end Mettapedia.GraphTheory.FourColor
