import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebChordBoundarySupportExclusion
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebChordHoleSideCutWitness
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebFaceComponentCycleTransport

/-!
# Hole-free chord sides exclude their named boundary faces

The hole-free certificate says that the selected facial component cannot reach
the named inner or outer hole.  At the corresponding boundary dart every
incident edge avoids the chord wall, because the boundary stub is outside the
cycle.  The generic cubic rotation argument therefore turns the facial
non-reachability into a primal vertex-side exclusion.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebChordHoleBoundaryComponentExclusion

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebChordBoundarySupportExclusion
open GoertzelV24ClosedWebFaceComponentCycleTransport
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebHoleBoundaryOrder
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SimpleGraphFaceDualConnectedness

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

local instance chordHoleBoundaryComponentExclusionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

theorem innerStub_not_faceComponentSide_of_holeFreeChordSide
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (htwoSided : OrbitFacesTwoSided embedded.RS)
    (side : Bool)
    (hholeFree : HoleFreeChordSide embedded.cellulation
      (chord.boundary htriple) side) :
    ¬ faceComponentSide embedded.RS
        (chord.boundary htriple).wall
        (fullFace embedded.cellulation
          (chordSideFace embedded.cellulation
            (chord.boundary htriple) side))
        (data.innerStub radial.inner) := by
  let seed : AmbientFace (Finset.univ : Finset (OrbitFace embedded.RS)) :=
    fullFace embedded.cellulation
      (chordSideFace embedded.cellulation (chord.boundary htriple) side)
  let hole : AmbientFace (Finset.univ : Finset (OrbitFace embedded.RS)) :=
    fullFace embedded.cellulation embedded.cellulation.innerHole
  let dart := innerBoundaryDart data hdata radial.inner
  have hrotation : VertexRotationCyclic embedded.RS :=
    hasCyclicVertexRotations_implies_vertexRotationCyclic
      G embedded.cellulation.rotation
        embedded.cellulation.vertexRotation_cyclic
  have hface : orbitFaceVertex embedded.RS dart = hole := by
    apply Subtype.ext
    exact innerBoundaryDart_on_innerHole embedded hdata radial.inner
  have hfree :
      ¬ (faceAdjacencyAvoiding
        (orbitFaceBoundary embedded.RS)
        (Finset.univ : Finset (OrbitFace embedded.RS))
        (chord.boundary htriple).wall).Reachable seed hole := by
    change ¬ (faceAdjacencyAvoiding
      (orbitFaceBoundary embedded.RS)
      (Finset.univ : Finset (OrbitFace embedded.RS))
      (chord.boundary htriple).wall).Reachable
      (fullFace embedded.cellulation
        (chordSideFace embedded.cellulation
          (chord.boundary htriple) side))
      (fullFace embedded.cellulation embedded.cellulation.innerHole)
    exact (holeFreeChordSide_iff
      embedded.cellulation (chord.boundary htriple) side).1 hholeFree |>.1
  have havoid : ∀ incident : embedded.RS.D,
      embedded.RS.vertOf incident = embedded.RS.vertOf dart →
      embedded.RS.edgeOf incident ∉ (chord.boundary htriple).wall := by
    intro incident hincident hwall
    have hvertex : embedded.RS.vertOf incident =
        data.innerStub radial.inner := by
      simpa [dart, innerBoundaryDart_fst] using hincident
    have hnotCycle :=
      chord.toRotationSystem_edge_not_mem_cycleWalk_of_vertex_not_mem_support
        embedded.cellulation.rotation
        (innerStub_not_mem_cycleWalk_support hdata chord htriple)
        incident hvertex
    apply hnotCycle
    exact (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple
      (embedded.RS.edgeOf incident)).1 hwall
  have hnot := not_faceComponentSide_of_holeFree_incident_dart
    embedded.RS htwoSided hrotation (chord.boundary htriple).wall
      seed hole dart hface havoid hfree
  simpa [seed, dart, innerBoundaryDart_fst] using hnot

theorem outerStub_not_faceComponentSide_of_holeFreeChordSide
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (htwoSided : OrbitFacesTwoSided embedded.RS)
    (side : Bool)
    (hholeFree : HoleFreeChordSide embedded.cellulation
      (chord.boundary htriple) side) :
    ¬ faceComponentSide embedded.RS
        (chord.boundary htriple).wall
        (fullFace embedded.cellulation
          (chordSideFace embedded.cellulation
            (chord.boundary htriple) side))
        (data.outerStub radial.outer) := by
  let seed : AmbientFace (Finset.univ : Finset (OrbitFace embedded.RS)) :=
    fullFace embedded.cellulation
      (chordSideFace embedded.cellulation (chord.boundary htriple) side)
  let hole : AmbientFace (Finset.univ : Finset (OrbitFace embedded.RS)) :=
    fullFace embedded.cellulation embedded.cellulation.outerHole
  let dart := outerBoundaryDart data hdata radial.outer
  have hrotation : VertexRotationCyclic embedded.RS :=
    hasCyclicVertexRotations_implies_vertexRotationCyclic
      G embedded.cellulation.rotation
        embedded.cellulation.vertexRotation_cyclic
  have hface : orbitFaceVertex embedded.RS dart = hole := by
    apply Subtype.ext
    exact outerBoundaryDart_on_outerHole embedded hdata radial.outer
  have hfree :
      ¬ (faceAdjacencyAvoiding
        (orbitFaceBoundary embedded.RS)
        (Finset.univ : Finset (OrbitFace embedded.RS))
        (chord.boundary htriple).wall).Reachable seed hole := by
    change ¬ (faceAdjacencyAvoiding
      (orbitFaceBoundary embedded.RS)
      (Finset.univ : Finset (OrbitFace embedded.RS))
      (chord.boundary htriple).wall).Reachable
      (fullFace embedded.cellulation
        (chordSideFace embedded.cellulation
          (chord.boundary htriple) side))
      (fullFace embedded.cellulation embedded.cellulation.outerHole)
    exact (holeFreeChordSide_iff
      embedded.cellulation (chord.boundary htriple) side).1 hholeFree |>.2
  have havoid : ∀ incident : embedded.RS.D,
      embedded.RS.vertOf incident = embedded.RS.vertOf dart →
      embedded.RS.edgeOf incident ∉ (chord.boundary htriple).wall := by
    intro incident hincident hwall
    have hvertex : embedded.RS.vertOf incident =
        data.outerStub radial.outer := by
      simpa [dart, outerBoundaryDart_fst] using hincident
    have hnotCycle :=
      chord.toRotationSystem_edge_not_mem_cycleWalk_of_vertex_not_mem_support
        embedded.cellulation.rotation
        (outerStub_not_mem_cycleWalk_support hdata chord htriple)
        incident hvertex
    apply hnotCycle
    exact (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple
      (embedded.RS.edgeOf incident)).1 hwall
  have hnot := not_faceComponentSide_of_holeFree_incident_dart
    embedded.RS htwoSided hrotation (chord.boundary htriple).wall
      seed hole dart hface havoid hfree
  simpa [seed, dart, outerBoundaryDart_fst] using hnot

/-! The radial-component support census upgrades the two endpoint exclusions
above to the whole annular interface.  These are still face-component
exclusions, not a Jordan theorem: they only say that a hole-free selected
component cannot contain any boundary stub. -/

theorem any_innerStub_not_faceComponentSide_of_holeFreeChordSide
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (hpair : ValidColorPair first second)
    (htwoSided : OrbitFacesTwoSided embedded.RS)
    (side : Bool)
    (hholeFree : HoleFreeChordSide embedded.cellulation
      (chord.boundary htriple) side)
    (inner : Fin 5) :
    ¬ faceComponentSide embedded.RS
        (chord.boundary htriple).wall
        (fullFace embedded.cellulation
          (chordSideFace embedded.cellulation
            (chord.boundary htriple) side))
        (data.innerStub inner) := by
  let seed : AmbientFace (Finset.univ : Finset (OrbitFace embedded.RS)) :=
    fullFace embedded.cellulation
      (chordSideFace embedded.cellulation (chord.boundary htriple) side)
  let hole : AmbientFace (Finset.univ : Finset (OrbitFace embedded.RS)) :=
    fullFace embedded.cellulation embedded.cellulation.innerHole
  let dart := innerBoundaryDart data hdata inner
  have hrotation : VertexRotationCyclic embedded.RS :=
    hasCyclicVertexRotations_implies_vertexRotationCyclic
      G embedded.cellulation.rotation
        embedded.cellulation.vertexRotation_cyclic
  have hface : orbitFaceVertex embedded.RS dart = hole := by
    apply Subtype.ext
    exact innerBoundaryDart_on_innerHole embedded hdata inner
  have hfree :
      ¬ (faceAdjacencyAvoiding
        (orbitFaceBoundary embedded.RS)
        (Finset.univ : Finset (OrbitFace embedded.RS))
        (chord.boundary htriple).wall).Reachable seed hole := by
    change ¬ (faceAdjacencyAvoiding
      (orbitFaceBoundary embedded.RS)
      (Finset.univ : Finset (OrbitFace embedded.RS))
      (chord.boundary htriple).wall).Reachable
      (fullFace embedded.cellulation
        (chordSideFace embedded.cellulation
          (chord.boundary htriple) side))
      (fullFace embedded.cellulation embedded.cellulation.innerHole)
    exact (holeFreeChordSide_iff
      embedded.cellulation (chord.boundary htriple) side).1 hholeFree |>.1
  have havoid : ∀ incident : embedded.RS.D,
      embedded.RS.vertOf incident = embedded.RS.vertOf dart →
      embedded.RS.edgeOf incident ∉ (chord.boundary htriple).wall := by
    intro incident hincident hwall
    have hvertex : embedded.RS.vertOf incident = data.innerStub inner := by
      simpa [dart, innerBoundaryDart_fst] using hincident
    have hnotCycle := chord.toRotationSystem_edge_not_mem_cycleWalk_of_vertex_not_mem_support
      embedded.cellulation.rotation
      (GoertzelV24ClosedWebChordBoundarySupportExclusion.any_innerStub_not_mem_cycleWalk_support
        hdata C hC chord htriple hpair inner)
      incident hvertex
    apply hnotCycle
    exact (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple
      (embedded.RS.edgeOf incident)).1 hwall
  have hnot := not_faceComponentSide_of_holeFree_incident_dart
    embedded.RS htwoSided hrotation (chord.boundary htriple).wall
      seed hole dart hface havoid hfree
  simpa [seed, dart, innerBoundaryDart_fst] using hnot

theorem any_outerStub_not_faceComponentSide_of_holeFreeChordSide
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (hpair : ValidColorPair first second)
    (htwoSided : OrbitFacesTwoSided embedded.RS)
    (side : Bool)
    (hholeFree : HoleFreeChordSide embedded.cellulation
      (chord.boundary htriple) side)
    (outer : Fin outerCount) :
    ¬ faceComponentSide embedded.RS
        (chord.boundary htriple).wall
        (fullFace embedded.cellulation
          (chordSideFace embedded.cellulation
            (chord.boundary htriple) side))
        (data.outerStub outer) := by
  let seed : AmbientFace (Finset.univ : Finset (OrbitFace embedded.RS)) :=
    fullFace embedded.cellulation
      (chordSideFace embedded.cellulation (chord.boundary htriple) side)
  let hole : AmbientFace (Finset.univ : Finset (OrbitFace embedded.RS)) :=
    fullFace embedded.cellulation embedded.cellulation.outerHole
  let dart := outerBoundaryDart data hdata outer
  have hrotation : VertexRotationCyclic embedded.RS :=
    hasCyclicVertexRotations_implies_vertexRotationCyclic
      G embedded.cellulation.rotation
        embedded.cellulation.vertexRotation_cyclic
  have hface : orbitFaceVertex embedded.RS dart = hole := by
    apply Subtype.ext
    exact outerBoundaryDart_on_outerHole embedded hdata outer
  have hfree :
      ¬ (faceAdjacencyAvoiding
        (orbitFaceBoundary embedded.RS)
        (Finset.univ : Finset (OrbitFace embedded.RS))
        (chord.boundary htriple).wall).Reachable seed hole := by
    change ¬ (faceAdjacencyAvoiding
      (orbitFaceBoundary embedded.RS)
      (Finset.univ : Finset (OrbitFace embedded.RS))
      (chord.boundary htriple).wall).Reachable
      (fullFace embedded.cellulation
        (chordSideFace embedded.cellulation
          (chord.boundary htriple) side))
      (fullFace embedded.cellulation embedded.cellulation.outerHole)
    exact (holeFreeChordSide_iff
      embedded.cellulation (chord.boundary htriple) side).1 hholeFree |>.2
  have havoid : ∀ incident : embedded.RS.D,
      embedded.RS.vertOf incident = embedded.RS.vertOf dart →
      embedded.RS.edgeOf incident ∉ (chord.boundary htriple).wall := by
    intro incident hincident hwall
    have hvertex : embedded.RS.vertOf incident = data.outerStub outer := by
      simpa [dart, outerBoundaryDart_fst] using hincident
    have hnotCycle := chord.toRotationSystem_edge_not_mem_cycleWalk_of_vertex_not_mem_support
      embedded.cellulation.rotation
      (GoertzelV24ClosedWebChordBoundarySupportExclusion.any_outerStub_not_mem_cycleWalk_support
        hdata C hC chord htriple hpair outer)
      incident hvertex
    apply hnotCycle
    exact (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple
      (embedded.RS.edgeOf incident)).1 hwall
  have hnot := not_faceComponentSide_of_holeFree_incident_dart
    embedded.RS htwoSided hrotation (chord.boundary htriple).wall
      seed hole dart hface havoid hfree
  simpa [seed, dart, outerBoundaryDart_fst] using hnot

end

end GoertzelV24ClosedWebChordHoleBoundaryComponentExclusion

end Mettapedia.GraphTheory.FourColor
