import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutDeletionComponent
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationBoundaryFaceCutProfile

/-!
# Boundary profiles from paired annular transversals

Two repeated source transversals form a closed loop in the facial dual.  The
annular-crosscut layer already constructs a deletion component whose exact
primal boundary is the loop's crossed-edge support.  This file turns that
component into the finite vertex-side carrier used by the profile engine.

The point is architectural as well as technical: a profile is computed from
the actual retained side of the paired source interfaces, not from a free
side predicate or from a chord wall.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteEdgeDeletion
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/- The finite separator in the preceding layer was elaborated with this
instance.  Reusing it here keeps its edge carrier definitionally stable. -/
attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The finite vertex carrier of a concrete deletion component. -/
noncomputable def componentSide
    {data : Data G}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (component : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent) :
    Finset V := by
  classical
  exact Finset.univ.filter fun vertex => vertex ∈ component.supp

@[simp]
theorem mem_componentSide_iff
    {data : Data G}
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (component : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent)
    (vertex : V) :
    vertex ∈ pair.componentSide component ↔ vertex ∈ component.supp := by
  classical
  simp [componentSide]

/-- The finite edge support of the dual loop has exactly the two interface
widths.  This turns the source's geometric width into the profile engine's
actual finite carrier size. -/
theorem primalCutEdges_card_eq_interfaceWidths
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) :
    (pair.primalCutEdges data).card =
      pair.left.walk.length + pair.right.walk.length := by
  have hwidth := pair.primalCut_ncard_eq_interfaceWidths data
  rw [pair.primalCut_eq_edgeFinsetValueSet_primalCutEdges data,
    ncard_edgeFinsetValueSet] at hwidth
  exact hwidth

/-- Once the constructed component has the exact separator boundary, its
finite vertex-side crossing set is exactly the crossed-edge support of the
two source transversals. -/
theorem vertexSetCrossingEdges_componentSide_eq_primalCutEdges
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (component : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent)
    (hboundary : componentCrossingEdges (pair.primalCutEdges data) component =
      pair.primalCutEdges data) :
    vertexSetCrossingEdges data.toRotationSystem
      (pair.componentSide component) = pair.primalCutEdges data := by
  ext edge
  calc
    edge ∈ vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide component) ↔
        EdgeCrossesVertexSide G
          (fun vertex => vertex ∈ pair.componentSide component) edge := by
          exact mem_simpleGraph_vertexSetCrossingEdges_iff
            data (pair.componentSide component) edge
    _ ↔ EdgeCrossesVertexSide G
          (fun vertex => vertex ∈ component.supp) edge := by
          simp only [mem_componentSide_iff]
    _ ↔ edge ∈ componentCrossingEdges (pair.primalCutEdges data) component := by
          exact (mem_componentCrossingEdges_iff
            (pair.primalCutEdges data) component edge).symm
    _ ↔ edge ∈ pair.primalCutEdges data := by rw [hboundary]

/-- The profile engine sees precisely the expected number of actual crossing
ports on a component whose boundary is the paired transversal loop. -/
theorem componentSide_crossingCard_eq_interfaceWidths
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (component : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent)
    (hboundary : componentCrossingEdges (pair.primalCutEdges data) component =
      pair.primalCutEdges data) :
    Fintype.card (VertexSetCrossingEdge data.toRotationSystem
      (pair.componentSide component)) =
        pair.left.walk.length + pair.right.walk.length := by
  rw [card_vertexSetCrossingEdge]
  rw [pair.vertexSetCrossingEdges_componentSide_eq_primalCutEdges
    data component hboundary,
    pair.primalCutEdges_card_eq_interfaceWidths data]

/-- The raw finite profile data of a paired transversal is computed from the
actual deletion component and its open face fragments.  No profile field is
postulated: the region, ports, and fragments are all derived from that side. -/
noncomputable def componentBoundaryProfileData
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (component : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent) :=
  vertexSetBoundaryGraphCutData data.toRotationSystem
    (pair.componentSide component)

/-- Every port of the constructed profile lies in the component-side region;
this is inherited from the concrete vertex-side construction, not assumed by
the annular interface. -/
theorem componentBoundaryProfileData_portsInRegion
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (component : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent) :
    (pair.componentBoundaryProfileData data component).PortsInRegion :=
  vertexSetBoundaryGraphCutData_portsInRegion data.toRotationSystem
    (pair.componentSide component)

/-- Every constructed face fragment is genuinely on its named face and in
the retained component-side region. -/
theorem componentBoundaryProfileData_fragmentsOnFaceInRegion
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (component : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent) :
    (pair.componentBoundaryProfileData data component).FragmentsOnFaceInRegion :=
  vertexSetBoundaryGraphCutData_fragmentsOnFaceInRegion data.toRotationSystem
    (pair.componentSide component)

/-- The finite color/connectivity/face state attached to a paired source
interface is computed from its actual component-side data. -/
noncomputable def componentBoundaryProfile
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (component : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent)
    (coloring : data.toRotationSystem.EdgeColoring Color)
    (hcoloring : data.toRotationSystem.IsTaitEdgeColoring coloring) :=
  (pair.componentBoundaryProfileData data component).profile coloring hcoloring

/-- The graph-derived profile data constructed above has the separator's
actual crossed edges as its port carrier whenever the component boundary is
exact. -/
theorem componentBoundaryProfileData_crossingCard_eq_interfaceWidths
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (component : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent)
    (hboundary : componentCrossingEdges (pair.primalCutEdges data) component =
      pair.primalCutEdges data) :
    Fintype.card (VertexSetCrossingEdge data.toRotationSystem
      (pair.componentSide component)) =
        pair.left.walk.length + pair.right.walk.length :=
  pair.componentSide_crossingCard_eq_interfaceWidths data component hboundary

/-- A paired source interface supplies an exact profile side without any
caller-provided vertex predicate.  This is the direct construction used at
the geometric entrance to the profile/splice layer. -/
theorem exists_componentBoundaryProfileData
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) :
    ∃ component : (G.deleteEdges
        (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent,
      vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide component) = pair.primalCutEdges data := by
  rcases pair.exists_primalCutComponent_exactBoundary data htwoSided hdual
      hconnected hsphere with ⟨component, hboundary⟩
  exact ⟨component,
    pair.vertexSetCrossingEdges_componentSide_eq_primalCutEdges
      data component hboundary⟩

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
