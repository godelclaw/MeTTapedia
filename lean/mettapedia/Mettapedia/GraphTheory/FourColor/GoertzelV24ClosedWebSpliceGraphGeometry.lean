import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceGraphAnnularEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierWeightedCurvature
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationSystemPrimalGeometryTransport

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
open GoertzelV24RotationSystemPrimalGeometryTransport
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

local instance rotationPrimalGraphAdjDecidable (RS : RotationSystem V E) :
    DecidableRel (rotationPrimalGraph RS).Adj :=
  Classical.decRel _

local instance rotationPrimalGraphEdgeSetDecidableEq (RS : RotationSystem V E) :
    DecidableEq (rotationPrimalGraph RS).edgeSet :=
  Subtype.instDecidableEq

namespace Instance

variable {G : SimpleGraph V} [DecidableRel G.Adj]
  {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
  {n terminalCount faceFragmentCount : Nat}
  {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}

attribute [local instance]
  retainedVertexFintype retainedVertexDecidableEq

local instance sourceEdgeSetDecidableEqSpliceGraphGeometry : DecidableEq G.edgeSet :=
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

/-- The two named hole faces on the literal splice rotation, before graph
backing. -/
noncomputable def outputRotationHoleFaces
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole) :
    Finset (OrbitFace splice.output) :=
  {(outputFaceOrbit_of_holeFaceKept splice
      web.annular.cellulation.innerHole hinner).1,
    (outputFaceOrbit_of_holeFaceKept splice
      web.annular.cellulation.outerHole houter).1}

/-- Literal quotient faces other than the two transported holes.  This is
the face carrier on which the splice's remaining topology should be proved. -/
noncomputable def outputRotationInteriorFaces
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole) :
    Finset (OrbitFace splice.output) :=
  Finset.univ \ outputRotationHoleFaces splice hinner houter

/-- The two literal protected holes map to the two graph-backed holes used by
the computed output cellulation. -/
theorem graphFaceFinset_outputRotationHoleFaces
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses) :
    graphFaceFinset splice.output
        (output_endpoints_injective splice ambientEndpointsInjective hsimple)
        (outputRotationHoleFaces splice hinner houter) =
      {outputGraphFaceOfHoleFaceKept splice
          web.annular.cellulation.innerHole hinner hsimple,
        outputGraphFaceOfHoleFaceKept splice
          web.annular.cellulation.outerHole houter hsimple} := by
  let hinjective : Function.Injective splice.output.endpoints :=
    output_endpoints_injective splice ambientEndpointsInjective hsimple
  let faceEquiv := graphFaceEquiv splice.output hinjective
  let innerFace : OrbitFace splice.output :=
    (outputFaceOrbit_of_holeFaceKept splice
      web.annular.cellulation.innerHole hinner).1
  let outerFace : OrbitFace splice.output :=
    (outputFaceOrbit_of_holeFaceKept splice
      web.annular.cellulation.outerHole houter).1
  change graphFaceFinset splice.output hinjective {innerFace, outerFace} =
    {faceEquiv innerFace, faceEquiv outerFace}
  unfold graphFaceFinset
  ext graphFace
  constructor
  · intro hgraphFace
    rcases Finset.mem_map.1 hgraphFace with
      ⟨sourceFace, hsourceFace, hsourceEq⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hsourceFace ⊢
    rcases hsourceFace with hinnerFace | houterFace
    · left
      simpa [hinnerFace] using hsourceEq.symm
    · right
      simpa [houterFace] using hsourceEq.symm
  · intro hgraphFace
    rw [Finset.mem_insert, Finset.mem_singleton] at hgraphFace
    apply Finset.mem_map.2
    rcases hgraphFace with hinnerFace | houterFace
    · exact ⟨innerFace, by simp, hinnerFace.symm⟩
    · exact ⟨outerFace, by simp, houterFace.symm⟩

/-- The output cellulation's graph-backed internal faces are exactly the
canonical images of the literal splice's non-hole faces. -/
theorem outputCellulation_interiorFaces_eq_graphFaceFinset
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
    (outputCellulation splice hinner houter hsimple hretained hbalance).interiorFaces =
      graphFaceFinset splice.output
        (output_endpoints_injective splice ambientEndpointsInjective hsimple)
        (outputRotationInteriorFaces splice hinner houter) := by
  unfold FramedAnnularCellulation.interiorFaces
  unfold FramedAnnularCellulation.holeFaces
  unfold outputRotationInteriorFaces
  rw [graphFaceFinset_sdiff, graphFaceFinset_univ]
  rw [graphFaceFinset_outputRotationHoleFaces splice hinner houter hsimple]
  rfl

/-- Literal simplicity of the non-hole splice faces transports to the actual
graph-backed annular cellulation. -/
theorem outputGraph_internalBoundarySimple_of_literal
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
    (hliteral : ∀ face ∈ outputRotationInteriorFaces splice hinner houter,
      (orbitFaceBoundary splice.output face).card =
        (orbitFaceDarts splice.output face).card) :
    let embedded := outputAnnularEmbedding splice hinner houter hsimple
      hretained hbalance
    ∀ face ∈ embedded.cellulation.interiorFaces,
      (orbitFaceBoundary embedded.RS face).card =
        embedded.cellulation.faceLength face := by
  dsimp only
  let hinjective :=
    output_endpoints_injective splice ambientEndpointsInjective hsimple
  let faceEquiv := graphFaceEquiv splice.output hinjective
  let literalFaces := outputRotationInteriorFaces splice hinner houter
  let embedded := outputAnnularEmbedding splice hinner houter hsimple
    hretained hbalance
  intro graphFace hgraphFace
  let literalFace := faceEquiv.symm graphFace
  have hgraphFace' : graphFace ∈ graphFaceFinset splice.output
      hinjective literalFaces := by
    rw [← outputCellulation_interiorFaces_eq_graphFaceFinset
      splice hinner houter hsimple hretained hbalance]
    exact hgraphFace
  have hliteralFace : literalFace ∈ literalFaces := by
    rcases Finset.mem_map.1 hgraphFace' with
      ⟨sourceFace, hsourceFace, hsourceEq⟩
    have hsource : sourceFace = literalFace := by
      calc
        sourceFace = faceEquiv.symm (faceEquiv sourceFace) :=
          (faceEquiv.symm_apply_apply sourceFace).symm
        _ = faceEquiv.symm graphFace := congrArg faceEquiv.symm hsourceEq
        _ = literalFace := rfl
    exact hsource ▸ hsourceFace
  have hsimpleFace := hliteral literalFace hliteralFace
  have hface : faceEquiv literalFace = graphFace :=
    faceEquiv.apply_symm_apply graphFace
  change (orbitFaceBoundary
      (graphData splice.output hinjective).toRotationSystem graphFace).card =
    (orbitFaceDarts
      (graphData splice.output hinjective).toRotationSystem graphFace).card
  calc
    (orbitFaceBoundary
        (graphData splice.output hinjective).toRotationSystem graphFace).card =
        (orbitFaceBoundary splice.output literalFace).card := by
      rw [← hface]
      exact graphFaceEquiv_orbitFaceBoundary_card splice.output
        hinjective literalFace
    _ = (orbitFaceDarts splice.output literalFace).card := hsimpleFace
    _ = (orbitFaceDarts
        (graphData splice.output hinjective).toRotationSystem graphFace).card := by
      rw [← hface]
      exact (graphFaceEquiv_orbitFaceDarts_card splice.output
        hinjective literalFace).symm

/-- Literal internal-dual connectedness transports to the actual graph-backed
annular cellulation. -/
theorem outputGraph_internalDualConnected_of_literal
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
    (hliteral : (interiorDualGraph (orbitFaceBoundary splice.output)
      (outputRotationInteriorFaces splice hinner houter)).Connected) :
    let embedded := outputAnnularEmbedding splice hinner houter hsimple
      hretained hbalance
    (interiorDualGraph (orbitFaceBoundary embedded.RS)
      embedded.cellulation.interiorFaces).Connected := by
  dsimp only
  let hinjective :=
    output_endpoints_injective splice ambientEndpointsInjective hsimple
  have hgraph := (graphInteriorDual_connected_iff splice.output hinjective
    (outputRotationInteriorFaces splice hinner houter)).2 hliteral
  rw [← outputCellulation_interiorFaces_eq_graphFaceFinset
    splice hinner houter hsimple hretained hbalance] at hgraph
  exact hgraph

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

/-- The graph-backed geometry constructor with both remaining topological
receipts stated on the literal splice rotation where the seam calculus lives. -/
theorem outputGeometryOfLiteral
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
      ∀ face ∈ outputRotationInteriorFaces splice hinner houter,
        (orbitFaceBoundary splice.output face).card =
          (orbitFaceDarts splice.output face).card)
    (hdualConnected :
      (interiorDualGraph (orbitFaceBoundary splice.output)
        (outputRotationInteriorFaces splice hinner houter)).Connected) :
    AnnularFrontierGeometry
      (outputAnnularEmbedding splice hinner houter hsimple hretained hbalance) := by
  apply outputGeometry splice hinner houter hsimple hretained hbalance hprofile
  · exact outputGraph_internalBoundarySimple_of_literal splice hinner houter
      hsimple hretained hbalance hboundarySimple
  · exact outputGraph_internalDualConnected_of_literal splice hinner houter
      hsimple hretained hbalance hdualConnected

end Instance

end

end GoertzelV24ClosedWebSpliceGraphGeometry

end Mettapedia.GraphTheory.FourColor
