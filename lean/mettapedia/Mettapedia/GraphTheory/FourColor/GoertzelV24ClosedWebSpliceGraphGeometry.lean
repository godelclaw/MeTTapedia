import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceGraphAnnularEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierWeightedCurvature

/-!
# Minimum-face geometry on the graph-backed shortened splice

Addendum XXVII requires the shortened annulus to retain the source's
minimum-five face bound.  The source `Instance` stores that bound only on
annular-interior faces, while the ordered splice theorem expects it on every
old facial orbit.  This module closes both representation gaps.

The two named holes contain their five injectively named boundary edges, so
their dart cycles also have length at least five.  The existing finite seam
return test then proves the bound on every literal splice face.  A canonical
equivalence of face darts transports that result to the actual simple-graph
backing.  Thus the minimum-five field of output `AnnularFrontierGeometry` is
constructed rather than assumed.

This is one L1 output-invariant receipt, not L1 closure.  The constructor at
the end still takes the two genuinely topological output facts: simplicity of
internal facial boundaries and connectedness of the internal facial dual.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebSpliceGraphGeometry

open GoertzelV24AnnularFrontierWeightedCurvature.AnnularFrontier
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebSpliceGraphAnnularCellulation.Instance
open GoertzelV24ClosedWebSpliceGraphAnnularEmbedding
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationSystemPrimalFaceTransport
open GoertzelV24RotationSystemPrimalGraphBacking
open GoertzelV24RotationSystemPrimalGraphBacking.OrderedCutSpliceData
open GoertzelV24RotationSystemPrimalEdgePresentation
open GoertzelV24RotationSystemPrimalEdgePresentation.OrderedCutSpliceData
open GoertzelV24SpliceUnification
open GoertzelV24SpliceUnification.OrderedCutSpliceData

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

attribute [-instance] GoertzelV24SeamFaceArcPartition.hitPointFintype
attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

local instance rotationPrimalGraphAdjDecidable (RS : RotationSystem V E) :
    DecidableRel (rotationPrimalGraph RS).Adj :=
  Classical.decRel _

local instance rotationPrimalGraphEdgeSetDecidableEq (RS : RotationSystem V E) :
    DecidableEq (rotationPrimalGraph RS).edgeSet :=
  Subtype.instDecidableEq

/-- The canonical graph-backing dart equivalence restricts to an equivalence
on every complete facial orbit. -/
def graphFaceDartEquiv
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (face : OrbitFace RS) :
    {dart : RS.D // dart ∈ orbitFaceDarts RS face} ≃
      {dart : (graphData RS hinjective).toRotationSystem.D //
        dart ∈ orbitFaceDarts (graphData RS hinjective).toRotationSystem
          (graphFaceEquiv RS hinjective face)} where
  toFun dart := ⟨primalDartEquiv RS hinjective dart.1, by
    rw [mem_orbitFaceDarts_iff, ← graphFaceEquiv_dartOrbitFace]
    exact congrArg (graphFaceEquiv RS hinjective)
      ((mem_orbitFaceDarts_iff RS face dart.1).1 dart.2)⟩
  invFun dart := ⟨(primalDartEquiv RS hinjective).symm dart.1, by
    rw [mem_orbitFaceDarts_iff]
    apply (graphFaceEquiv RS hinjective).injective
    rw [graphFaceEquiv_dartOrbitFace]
    have hface := (mem_orbitFaceDarts_iff
      (graphData RS hinjective).toRotationSystem
      (graphFaceEquiv RS hinjective face) dart.1).1 dart.2
    simpa using hface⟩
  left_inv dart := by
    apply Subtype.ext
    exact (primalDartEquiv RS hinjective).symm_apply_apply dart.1
  right_inv dart := by
    apply Subtype.ext
    exact (primalDartEquiv RS hinjective).apply_symm_apply dart.1

/-- Graph backing preserves the number of darts in every quotient face. -/
theorem graphFaceEquiv_orbitFaceDarts_card
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (face : OrbitFace RS) :
    (orbitFaceDarts (graphData RS hinjective).toRotationSystem
      (graphFaceEquiv RS hinjective face)).card =
      (orbitFaceDarts RS face).card := by
  have hcard := Fintype.card_congr (graphFaceDartEquiv RS hinjective face)
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  exact hcard.symm

/-- Representative-level form of facial-orbit cardinality preservation. -/
theorem graphData_faceOrbit_card_eq
    (RS : RotationSystem V E)
    (hinjective : Function.Injective RS.endpoints)
    (dart : RS.D) :
    ((graphData RS hinjective).toRotationSystem.faceOrbit
      (primalDartEquiv RS hinjective dart)).card =
      (RS.faceOrbit dart).card := by
  rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit,
    ← orbitFaceDarts_dartOrbitFace_eq_faceOrbit,
    ← graphFaceEquiv_dartOrbitFace]
  exact graphFaceEquiv_orbitFaceDarts_card RS hinjective
    (dartOrbitFace RS dart)

namespace Instance

variable {G : SimpleGraph V} [DecidableRel G.Adj]
  {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
  {n terminalCount faceFragmentCount : Nat}
  {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}

attribute [local instance]
  retainedVertexFintype retainedVertexDecidableEq

local instance sourceEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance outputAdjDecidable
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount) :
    DecidableRel (rotationPrimalGraph splice.output).Adj :=
  Classical.decRel _

private abbrev ambientEndpointsInjective :
    Function.Injective web.annular.RS.endpoints :=
  GoertzelV24SimpleGraphRotationEndpointInjective.endpoints_injective
    web.annular.cellulation.rotation

/-- Every source facial orbit has length at least five.  Interior faces use
the stored geometry; each hole uses its five injectively named boundary
edges. -/
theorem source_all_faceOrbits_minimumFive (dart : web.annular.RS.D) :
    5 ≤ (web.annular.RS.faceOrbit dart).card := by
  let face := dartOrbitFace web.annular.RS dart
  by_cases hinterior : face ∈ web.annular.cellulation.interiorFaces
  · have hminimum := web.geometry.internalMinimumFive face hinterior
    have hle := orbitFaceBoundary_card_le_orbitFaceDarts_card web.annular.RS face
    rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit] at hle
    exact hminimum.trans hle
  · have hhole : face = web.annular.cellulation.innerHole ∨
        face = web.annular.cellulation.outerHole := by
      have hother : face ≠ web.annular.cellulation.innerHole →
          face = web.annular.cellulation.outerHole := by
        simpa [FramedAnnularCellulation.interiorFaces,
          FramedAnnularCellulation.holeFaces] using hinterior
      by_cases hinner : face = web.annular.cellulation.innerHole
      · exact Or.inl hinner
      · exact Or.inr (hother hinner)
    rcases hhole with hinner | houter
    · have hsubset := web.annular.innerBoundaryEdges_subset_innerHoleBoundary
      have hcard : (innerBoundaryEdges data).card = 5 := by
        simp [innerBoundaryEdges]
      have hle := Finset.card_le_card hsubset
      have hboundary := orbitFaceBoundary_card_le_orbitFaceDarts_card
        web.annular.RS web.annular.cellulation.innerHole
      rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
      change 5 ≤ (orbitFaceDarts web.annular.RS face).card
      rw [hinner]
      omega
    · have hsubset := web.annular.outerBoundaryEdges_subset_outerHoleBoundary
      have hcard : (outerBoundaryEdges data).card = 5 := by
        simp [outerBoundaryEdges]
      have hle := Finset.card_le_card hsubset
      have hboundary := orbitFaceBoundary_card_le_orbitFaceDarts_card
        web.annular.RS web.annular.cellulation.outerHole
      rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
      change 5 ≤ (orbitFaceDarts web.annular.RS face).card
      rw [houter]
      omega

/-- The old-face minimum and finite seam-return test give the same global
minimum on the canonical simple-graph output. -/
theorem outputGraph_all_faceOrbits_minimumFive
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses)
    (hprofile : splice.SeamFacesMeetFive)
    (dart : (outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem.D) :
    5 ≤ ((outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem.faceOrbit
      dart).card := by
  let outputDartEquiv := primalDartEquiv splice.output
    (output_endpoints_injective splice ambientEndpointsInjective hsimple)
  let sourceDart := outputDartEquiv.symm dart
  have hminimum : 5 ≤ (splice.output.faceOrbit sourceDart).card :=
    output_seamFace_meets_five splice source_all_faceOrbits_minimumFive
      hprofile sourceDart
  have hcard := graphData_faceOrbit_card_eq splice.output
    (output_endpoints_injective splice ambientEndpointsInjective hsimple)
    sourceDart
  calc
    5 ≤ (splice.output.faceOrbit sourceDart).card := hminimum
    _ = ((outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem.faceOrbit
        (outputDartEquiv sourceDart)).card := hcard.symm
    _ = ((outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem.faceOrbit
        dart).card := by rw [show outputDartEquiv sourceDart = dart from
          outputDartEquiv.apply_symm_apply dart]

/-- Two topological receipts plus the computed seam return profile assemble
the output frontier geometry.  Minimum face size is derived, not assumed. -/
theorem outputGeometry
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses)
    (hretained :
      (retainedAmbientPrimalGraph web.annular.RS splice.keep).Connected)
    (hbalance : splice.LocalEulerBalance)
    (hprofile : splice.SeamFacesMeetFive)
    (hboundarySimple :
      let embedded := outputAnnularEmbedding splice hinner houter hsimple
        hretained hbalance
      ∀ face ∈ embedded.cellulation.interiorFaces,
        (orbitFaceBoundary embedded.RS face).card =
          embedded.cellulation.faceLength face)
    (hdualConnected :
      let embedded := outputAnnularEmbedding splice hinner houter hsimple
        hretained hbalance
      (interiorDualGraph (orbitFaceBoundary embedded.RS)
        embedded.cellulation.interiorFaces).Connected) :
    AnnularFrontierGeometry
      (outputAnnularEmbedding splice hinner houter hsimple hretained hbalance) := by
  let embedded := outputAnnularEmbedding splice hinner houter hsimple
    hretained hbalance
  refine {
    internalBoundarySimple := hboundarySimple
    internalMinimumFive := ?_
    internalDualConnected := hdualConnected
  }
  intro face hface
  rcases exists_dartOrbitFace_eq embedded.RS face with ⟨dart, hdart⟩
  have hminimum := outputGraph_all_faceOrbits_minimumFive splice hsimple
    hprofile dart
  have hdarts : 5 ≤ (orbitFaceDarts embedded.RS face).card := by
    rw [← hdart, orbitFaceDarts_dartOrbitFace_eq_faceOrbit]
    exact hminimum
  have hsimpleFace := hboundarySimple face hface
  rw [hsimpleFace, FramedAnnularCellulation.faceLength]
  exact hdarts

end Instance

end

end GoertzelV24ClosedWebSpliceGraphGeometry

end Mettapedia.GraphTheory.FourColor
