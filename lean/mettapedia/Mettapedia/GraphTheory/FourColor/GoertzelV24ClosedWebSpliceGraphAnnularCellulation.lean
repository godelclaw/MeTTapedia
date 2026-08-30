import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceGraphHoleTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSplicePrimalGraph
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceEuler

/-!
# Annular cellulation on the graph-backed splice output

Addendum XXVII shortens a source annulus by deleting the region between two
aligned cuts and sewing the ordered cut ports.  This module assembles the
literal graph-backed output cellulation from the receipts already exposed by
the splice calculus:

* both named source holes are wholly retained;
* the retained primal carrier is connected;
* the new seam endpoints pass the exact simplicity test; and
* the deleted vertices, removed edges, changed faces, and seam edges satisfy
  the local Euler balance.

The result proves cyclic vertex rotations, transports two distinct hole face
orbits, and proves the sphere Euler equation on the output graph.  It does not
yet package a `ClosedWebAnnularEmbedding`: that stronger structure additionally
requires the three per-dart statements identifying the output root and the two
ordered boundary interfaces with these transported holes.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebSpliceGraphAnnularCellulation

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RetainedSpliceAmbientFaceCount
open GoertzelV24RetainedSpliceEdgeCount
open GoertzelV24RetainedSpliceEuler
open GoertzelV24RetainedSpliceFaceCount
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSystemPrimalEdgePresentation
open GoertzelV24RotationSystemPrimalFaceTransport
open GoertzelV24RotationSystemPrimalGraphBacking
open GoertzelV24RotationSystemPrimalGraphBacking.OrderedCutSpliceData
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24SpliceUnification

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

local instance rotationPrimalGraphAdjDecidable (RS : RotationSystem V E) :
    DecidableRel (rotationPrimalGraph RS).Adj :=
  Classical.decRel _

local instance rotationPrimalGraphEdgeDecidableEq
    (RS : RotationSystem V E) :
    DecidableEq (rotationPrimalGraph RS).edgeSet :=
  Subtype.instDecidableEq

/-- Ordered deletion and sewing retains the complete cyclic order at each
surviving vertex. -/
theorem output_vertexRotationCyclic
    {RS : RotationSystem V E}
    {n terminalCount faceFragmentCount : Nat}
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (hcyclic : VertexRotationCyclic RS) :
    VertexRotationCyclic data.output := by
  intro left right hvertex
  let parts := retainedDartEquivMatchedParts RS data.keep
    (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
    data.cover data.disjoint
  have hunderlyingVertex :
      RS.vertOf (parts.symm left).1 = RS.vertOf (parts.symm right).1 := by
    rw [← matchedPartUnderlyingDart_eq_equiv_symm_val RS data.keep
      (orderedCut data.left.crossingEdge)
      (orderedCut data.right.crossingEdge)
      data.cover data.disjoint left]
    rw [← matchedPartUnderlyingDart_eq_equiv_symm_val RS data.keep
      (orderedCut data.left.crossingEdge)
      (orderedCut data.right.crossingEdge)
      data.cover data.disjoint right]
    change (data.output.vertOf left).1 = (data.output.vertOf right).1
    exact congrArg Subtype.val hvertex
  have hambient :
      RS.rho.SameCycle (parts.symm left).1 (parts.symm right).1 :=
    hcyclic _ _ hunderlyingVertex
  have hretained :
      (retainedRho RS data.keep).SameCycle
        (parts.symm left) (parts.symm right) :=
    Equiv.Perm.SameCycle.subtypePerm hambient
  rcases hretained with ⟨power, hpower⟩
  refine ⟨power, ?_⟩
  have hrho : data.output.rho =
      matchedPartsRho RS data.keep
        (orderedCut data.left.crossingEdge)
        (orderedCut data.right.crossingEdge)
        data.cover data.disjoint := by
    rfl
  rw [hrho]
  change ((parts.permCongr (retainedRho RS data.keep)) ^ power) left = right
  have hmap :
      parts.permCongr ((retainedRho RS data.keep) ^ power) =
        (parts.permCongr (retainedRho RS data.keep)) ^ power :=
    map_zpow parts.permCongrHom (retainedRho RS data.keep) power
  rw [← hmap]
  change parts (((retainedRho RS data.keep) ^ power)
    (parts.symm left)) = right
  rw [hpower, parts.apply_symm_apply]

/-- The canonical graph backing transports cyclic vertex rotations, not just
the bare vertex-preserving permutation. -/
theorem graphData_hasCyclicVertexRotations
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (hcyclic : VertexRotationCyclic RS) :
    ∀ vertex,
      (graphData RS hinjective).vertexRotation.IsCycleOn
        {dart : (rotationPrimalGraph RS).Dart | dart.fst = vertex} := by
  intro vertex
  constructor
  · exact (graphData RS hinjective).vertexRotation.bijOn fun dart => by
      change ((graphData RS hinjective).vertexRotation dart).fst = vertex ↔
        dart.fst = vertex
      rw [(graphData RS hinjective).vertexRotation_fst]
  · intro left hleft right hright
    have hliteral := hcyclic
      ((primalDartEquiv RS hinjective).symm left)
      ((primalDartEquiv RS hinjective).symm right) (by
        rw [primalDartEquiv_symm_fst, primalDartEquiv_symm_fst]
        exact hleft.trans hright.symm)
    rcases hliteral with ⟨power, hpower⟩
    refine ⟨power, ?_⟩
    change (((primalDartEquiv RS hinjective).permCongr RS.rho) ^ power)
      left = right
    have hmap := MonoidHom.map_zpow
      (primalDartEquiv RS hinjective).permCongrHom.toMonoidHom RS.rho power
    calc
      _ = (primalDartEquiv RS hinjective).permCongr (RS.rho ^ power) left :=
        congrArg (fun permutation => permutation left) hmap.symm
      _ = primalDartEquiv RS hinjective
          ((RS.rho ^ power) ((primalDartEquiv RS hinjective).symm left)) := rfl
      _ = primalDartEquiv RS hinjective
          ((primalDartEquiv RS hinjective).symm right) :=
        congrArg (primalDartEquiv RS hinjective) hpower
      _ = right := (primalDartEquiv RS hinjective).apply_symm_apply right

/-- The local splice Euler balance transports the ambient sphere equation
without requiring the open annular carrier to be globally cubic. -/
theorem output_euler
    {RS : RotationSystem V E}
    {n terminalCount faceFragmentCount : Nat}
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (hambientEuler :
      (Fintype.card V : Int) - Fintype.card E +
        Fintype.card (OrbitFace RS) = 2)
    (hbalance : data.LocalEulerBalance) :
    (Fintype.card (RetainedVertex data.keep) : Int) -
        Fintype.card (OrderedCutSpliceData.OutputEdge data) +
        Fintype.card (OrbitFace data.output) = 2 := by
  have hvertices := card_retainedVertex_add_card_deletedVertex data.keep
  have hedges := card_retainedInternalEdge_add_card_removedEdge RS data.keep
  have hambientFaces := card_ambientRetained_add_deletedFaceOrbit RS data.keep
  have hnewEdges := card_orderedCutRetainedVertexRotationSystem_edges
    RS data.keep data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective data.rightInjective
    data.cover data.disjoint data.outer_kept data.seamEndpoints
  have hnewFaces :=
    card_orderedCutRetainedVertex_faceCycleLengths_eq_ambient_add_return
      RS data.keep data.left.crossingEdge data.right.crossingEdge
      data.leftCrosses data.rightCrosses data.leftInjective data.rightInjective
      data.cover data.disjoint data.outer_kept data.seamEndpoints
  have hambientEulerCycles :
      (Fintype.card V : Int) - Fintype.card E +
        (GoertzelV24CurvatureScope.faceCycleLengths RS).card = 2 := by
    rw [← card_orbitFace_eq_faceCycleLengths_card]
    exact hambientEuler
  have hverticesInt :
      (Fintype.card (RetainedVertex data.keep) : Int) +
          Fintype.card (DeletedVertex data.keep) = Fintype.card V := by
    exact_mod_cast hvertices
  have hedgesInt :
      (Fintype.card (RetainedInternalEdge RS data.keep) : Int) +
          Fintype.card (RemovedEdge RS data.keep) = Fintype.card E := by
    exact_mod_cast hedges
  have hambientFacesInt :
      (Fintype.card (AmbientRetainedFaceOrbit RS data.keep) : Int) +
          Fintype.card (AmbientDeletedFaceOrbit RS data.keep) =
        (GoertzelV24CurvatureScope.faceCycleLengths RS).card := by
    exact_mod_cast hambientFaces
  have hnewEdgesInt :
      (Fintype.card (OrderedCutSpliceData.OutputEdge data) : Int) =
        Fintype.card (RetainedInternalEdge RS data.keep) + n := by
    exact_mod_cast hnewEdges
  have hnewFacesInt :
      ((GoertzelV24CurvatureScope.faceCycleLengths data.output).card : Int) =
        Fintype.card (AmbientRetainedFaceOrbit RS data.keep) +
          (actualOrderedCutFaceReturnSuccessor RS data.keep
            data.left.crossingEdge data.right.crossingEdge
            data.leftCrosses data.rightCrosses data.leftInjective
            data.rightInjective data.cover data.disjoint
            data.outer_kept).partition.parts.card := by
    exact_mod_cast hnewFaces
  have hbalanceInt :
      (Fintype.card (RemovedEdge RS data.keep) : Int) +
          (actualOrderedCutFaceReturnSuccessor RS data.keep
            data.left.crossingEdge data.right.crossingEdge
            data.leftCrosses data.rightCrosses data.leftInjective
            data.rightInjective data.cover data.disjoint
            data.outer_kept).partition.parts.card =
        Fintype.card (DeletedVertex data.keep) + n +
          Fintype.card (AmbientDeletedFaceOrbit RS data.keep) := by
    exact_mod_cast hbalance
  have houtputFaceCard := card_orbitFace_eq_faceCycleLengths_card data.output
  omega

/-- Endpoint-simple graph backing preserves the Euler characteristic of the
literal rotation system. -/
theorem graphData_euler_of_literal
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (heuler :
      (Fintype.card V : Int) - Fintype.card E +
        Fintype.card (OrbitFace RS) = 2) :
    (Fintype.card V : Int) -
        Fintype.card (rotationPrimalGraph RS).edgeSet +
        Fintype.card (OrbitFace (graphData RS hinjective).toRotationSystem) =
      2 := by
  have hedges : Fintype.card E =
      Fintype.card (rotationPrimalGraph RS).edgeSet :=
    Fintype.card_congr (edgeEquiv RS hinjective)
  have hfaces : Fintype.card (OrbitFace RS) =
      Fintype.card (OrbitFace (graphData RS hinjective).toRotationSystem) :=
    Fintype.card_congr (graphFaceEquiv RS hinjective)
  omega

namespace Instance

open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RotationSystemPrimalEdgePresentation.OrderedCutSpliceData

variable {G : SimpleGraph V} [DecidableRel G.Adj]
  {boundary : AnnularBoundaryData G 5}
  {coloring : G.EdgeColoring Color}
  {n terminalCount faceFragmentCount : Nat}
  {web : GoertzelV24ClosedWebAtGoodWord.Instance boundary coloring}

attribute [-instance] GoertzelV24SeamFaceArcPartition.hitPointFintype

attribute [local instance]
  retainedVertexFintype retainedVertexDecidableEq

local instance sourceEdgeSetDecidableEqAnnularCellulation : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance outputAdjDecidable
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount) :
    DecidableRel (rotationPrimalGraph splice.output).Adj :=
  Classical.decRel _

/-- A connected retained source side remains connected on the actual
graph-backed shortened carrier. -/
theorem outputGraph_connected_of_retained
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hretained :
      (retainedAmbientPrimalGraph web.annular.RS splice.keep).Connected) :
    (rotationPrimalGraph splice.output).Connected := by
  exact rotationPrimalGraph_orderedCutRetainedVertexRotationSystem_connected_of_retained
    web.annular.RS splice.keep splice.left.crossingEdge
    splice.right.crossingEdge splice.leftCrosses splice.rightCrosses
    splice.leftInjective splice.rightInjective splice.cover splice.disjoint
    splice.outer_kept splice.seamEndpoints hretained

/-- The two transported holes, connected retained side, cyclic rotations,
and local Euler receipt assemble the graph-backed annular cellulation. -/
def outputCellulation
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses)
    (hretained :
      (retainedAmbientPrimalGraph web.annular.RS splice.keep).Connected)
    (hbalance : splice.LocalEulerBalance) :
    FramedAnnularCellulation (rotationPrimalGraph splice.output) where
  rotation := outputGraphData splice
    (GoertzelV24SimpleGraphRotationEndpointInjective.endpoints_injective
      web.annular.cellulation.rotation) hsimple
  connected := outputGraph_connected_of_retained splice hretained
  vertexRotation_cyclic := by
    apply graphData_hasCyclicVertexRotations
    apply output_vertexRotationCyclic splice
    exact web.vertexRotationCyclic
  innerHole :=
    outputGraphFaceOfHoleFaceKept splice
      web.annular.cellulation.innerHole hinner hsimple
  outerHole :=
    outputGraphFaceOfHoleFaceKept splice
      web.annular.cellulation.outerHole houter hsimple
  holes_ne := outputGraphInnerHole_ne_outputGraphOuterHole
    splice hinner houter hsimple
  euler := by
    apply graphData_euler_of_literal
    apply output_euler splice
    · exact web.annular.cellulation.euler
    · exact hbalance

end Instance

end

end GoertzelV24ClosedWebSpliceGraphAnnularCellulation

end Mettapedia.GraphTheory.FourColor
