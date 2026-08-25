import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceGraphAnnularCellulation
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceGraphBoundaryData
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionOutputRestriction

/-!
# The graph-backed shortened splice is an actual annular embedding

The preceding splice layer constructs the shortened simple graph, transports
the two protected hole-face quotients, and proves its annular Euler equation.
For the source-facing L1 reduction that is not enough: the distinguished root
and every dart over the ten ordered boundary edges must lie on the named hole
faces.

This module proves those incidences from the retained source darts.  The key
step is quotient-safe: it uses the bijection on an entire retained face cycle,
rather than choosing a convenient representative of a quotient orbit.  The
two graph darts over each retained boundary edge are then classified by the
rotation system's exact two-dart fiber theorem.  The result is a concrete
`ClosedWebAnnularEmbedding` on the shortened graph, not a conditional wrapper
carrying the three incidence clauses as assumptions.

This closes the annular-embedding output of the splice.  It does not by itself
construct the source crosscut pair, prove the remaining framed-annulus
geometry, or establish counterexample reflection.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebSpliceGraphAnnularEmbedding

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebSpliceGraphAnnularCellulation.Instance
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedSpliceAmbientFaceCount
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSystemPrimalFaceTransport
open GoertzelV24RotationSystemPrimalFaceTransport.OrderedCutSpliceData
open GoertzelV24RotationSystemPrimalGraphBacking
open GoertzelV24RotationSystemPrimalGraphBacking.OrderedCutSpliceData
open GoertzelV24RotationSystemPrimalEdgePresentation
open GoertzelV24RotationSystemPrimalEdgePresentation.OrderedCutSpliceData
open GoertzelV24SpliceUnification
open GoertzelV24OpenRegionOutputRestriction
open GoertzelV24OpenRegionOutputRestriction.OrderedCutSpliceData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
  {n terminalCount faceFragmentCount : Nat}
  {web : Instance data coloring}

noncomputable section

attribute [-instance] GoertzelV24SeamFaceArcPartition.hitPointFintype

attribute [local instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype

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

/-- The dart and edge graph-backing equivalences use the same underlying
unordered endpoint pair. -/
theorem graphData_edgeOf_primalDartEquiv_eq_edgeEquiv
    {X F : Type*} [Fintype X] [DecidableEq X]
    [Fintype F] [DecidableEq F]
    (RS : RotationSystem X F)
    [DecidableRel (rotationPrimalGraph RS).Adj]
    (hinjective : Function.Injective RS.endpoints)
    (dart : RS.D) :
    (graphData RS hinjective).toRotationSystem.edgeOf
        (primalDartEquiv RS hinjective dart) =
      edgeEquiv RS hinjective (RS.edgeOf dart) := by
  apply Subtype.ext
  rw [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
  change s(RS.vertOf dart, RS.vertOf (RS.alpha dart)) =
    s(RS.vertOf (chosenDart RS (RS.edgeOf dart)),
      RS.vertOf (RS.alpha (chosenDart RS (RS.edgeOf dart))))
  rcases RS.edge_fiber_two_cases
      (chosenDart_edgeOf RS (RS.edgeOf dart)) rfl with hsame | hreverse
  · exact congrArg (fun source : RS.D =>
      s(RS.vertOf source, RS.vertOf (RS.alpha source))) hsame
  · have hchosen : chosenDart RS (RS.edgeOf dart) = RS.alpha dart := by
      have halpha := congrArg RS.alpha hreverse
      simpa [RS.alpha_involutive] using halpha.symm
    rw [hchosen, RS.alpha_involutive]
    exact Sym2.eq_swap

/-- Every retained literal dart on a protected source face lies on the
canonical transported output face. -/
theorem outputFaceOrbit_of_holeFaceKept_eq_dartOrbitFace
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (face : OrbitFace web.annular.RS)
    (hkept : HoleFaceKept splice face)
    (dart : RetainedDart web.annular.RS splice.keep)
    (hdart : dartOrbitFace web.annular.RS dart.1 = face) :
    (outputFaceOrbit_of_holeFaceKept splice face hkept).1 =
      dartOrbitFace splice.output
        (retainedDartEquivMatchedParts web.annular.RS splice.keep
          (orderedCut splice.left.crossingEdge)
          (orderedCut splice.right.crossingEdge)
          splice.cover splice.disjoint dart) := by
  let retainedFace := ambientRetainedFaceOrbit_of_holeFaceKept
    splice face hkept
  let orbit := ambientRetainedFaceOrbitToSplice web.annular.RS splice.keep
    splice.left.crossingEdge splice.right.crossingEdge splice.leftCrosses
    splice.rightCrosses splice.leftInjective splice.rightInjective
    splice.cover splice.disjoint splice.outer_kept retainedFace
  let parts := retainedDartEquivMatchedParts web.annular.RS splice.keep
    (orderedCut splice.left.crossingEdge)
    (orderedCut splice.right.crossingEdge) splice.cover splice.disjoint
  let mapped := parts dart
  change orbit.1 = dartOrbitFace splice.output mapped
  have hroundtrip :
      nonHitSpliceOrbitToAmbient web.annular.RS splice.keep
        splice.left.crossingEdge splice.right.crossingEdge splice.leftCrosses
        splice.rightCrosses splice.leftInjective splice.rightInjective
        splice.cover splice.disjoint splice.outer_kept orbit = retainedFace :=
    nonHitSpliceOrbitToAmbient_ambientRetainedFaceOrbitToSplice
      web.annular.RS splice.keep splice.left.crossingEdge
      splice.right.crossingEdge splice.leftCrosses splice.rightCrosses
      splice.leftInjective splice.rightInjective splice.cover splice.disjoint
      splice.outer_kept retainedFace
  have hsourceQuotient :
      Quotient.mk (Equiv.Perm.SameCycle.setoid web.annular.RS.phi)
          (matchedPartUnderlyingDart web.annular.RS splice.keep
            (orderedCut splice.left.crossingEdge)
            (orderedCut splice.right.crossingEdge) orbit.1.out) =
        dartOrbitFace web.annular.RS dart.1 := by
    calc
      _ = (nonHitSpliceOrbitToAmbient web.annular.RS splice.keep
          splice.left.crossingEdge splice.right.crossingEdge
          splice.leftCrosses splice.rightCrosses splice.leftInjective
          splice.rightInjective splice.cover splice.disjoint
          splice.outer_kept orbit).1 := rfl
      _ = retainedFace.1 := congrArg Subtype.val hroundtrip
      _ = face := rfl
      _ = dartOrbitFace web.annular.RS dart.1 := hdart.symm
  have hsourceCycle : web.annular.RS.phi.SameCycle
      (matchedPartUnderlyingDart web.annular.RS splice.keep
        (orderedCut splice.left.crossingEdge)
        (orderedCut splice.right.crossingEdge) orbit.1.out) dart.1 :=
    Quotient.exact hsourceQuotient
  let target : {sourceDart // web.annular.RS.phi.SameCycle
      (matchedPartUnderlyingDart web.annular.RS splice.keep
        (orderedCut splice.left.crossingEdge)
        (orderedCut splice.right.crossingEdge) orbit.1.out) sourceDart} :=
    ⟨dart.1, hsourceCycle⟩
  rcases (nonHitSpliceCycleForget_bijective web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge splice.leftCrosses
      splice.rightCrosses splice.leftInjective splice.rightInjective
      splice.cover splice.disjoint splice.outer_kept orbit).2 target with
    ⟨source, hsource⟩
  have hsourceUnderlying :
      matchedPartUnderlyingDart web.annular.RS splice.keep
          (orderedCut splice.left.crossingEdge)
          (orderedCut splice.right.crossingEdge) source.1 = dart.1 :=
    congrArg Subtype.val hsource
  have hmappedUnderlying :
      matchedPartUnderlyingDart web.annular.RS splice.keep
          (orderedCut splice.left.crossingEdge)
          (orderedCut splice.right.crossingEdge) mapped = dart.1 := by
    exact matchedPartUnderlyingDart_equiv web.annular.RS splice.keep
      (orderedCut splice.left.crossingEdge)
      (orderedCut splice.right.crossingEdge) splice.cover splice.disjoint
      dart
  have hsourceMapped : source.1 = mapped :=
    matchedPartUnderlyingDart_injective web.annular.RS splice.keep
      (orderedCut splice.left.crossingEdge)
      (orderedCut splice.right.crossingEdge) splice.cover splice.disjoint
      (hsourceUnderlying.trans hmappedUnderlying.symm)
  have hcycle : splice.output.phi.SameCycle orbit.1.out mapped := by
    change (orderedCutSplicePhi web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge splice.leftCrosses
      splice.rightCrosses splice.leftInjective splice.rightInjective
      splice.cover splice.disjoint splice.outer_kept).SameCycle
        orbit.1.out mapped
    simpa only [hsourceMapped] using source.2
  exact (Quotient.out_eq orbit.1).symm.trans (Quotient.sound hcycle)

/-- The same retained-dart incidence after the canonical simple-graph
backing. -/
theorem outputGraphFaceOfHoleFaceKept_eq_dartOrbitFace
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (face : OrbitFace web.annular.RS)
    (hkept : HoleFaceKept splice face)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses)
    (dart : RetainedDart web.annular.RS splice.keep)
    (hdart : dartOrbitFace web.annular.RS dart.1 = face) :
    outputGraphFaceOfHoleFaceKept splice face hkept hsimple =
      dartOrbitFace
        (outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem
        (primalDartEquiv splice.output
          (output_endpoints_injective splice ambientEndpointsInjective hsimple)
          (retainedDartEquivMatchedParts web.annular.RS splice.keep
            (orderedCut splice.left.crossingEdge)
            (orderedCut splice.right.crossingEdge)
            splice.cover splice.disjoint dart)) := by
  unfold outputGraphFaceOfHoleFaceKept outputGraphFaceEquiv
  rw [outputFaceOrbit_of_holeFaceKept_eq_dartOrbitFace splice face hkept
    dart hdart]
  exact graphFaceEquiv_dartOrbitFace splice.output
    (output_endpoints_injective splice ambientEndpointsInjective hsimple) _

/-- The canonical output root remains on the transported outer hole. -/
theorem outputGraph_outer_dart_on_outerHole
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses) :
    dartOrbitFace
        (outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem
        (outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem.outer =
      outputGraphFaceOfHoleFaceKept splice
        web.annular.cellulation.outerHole houter hsimple := by
  exact (outputGraphFaceOfHoleFaceKept_eq_dartOrbitFace splice
    web.annular.cellulation.outerHole houter hsimple
    ⟨web.annular.RS.outer, splice.outer_kept⟩
    web.annular.outer_dart_on_outerHole).symm

/-- Every output dart over a completely retained source boundary edge lies
on the transported source hole face. -/
theorem outputGraph_boundaryEdgeDarts_on_holeFace
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (face : OrbitFace web.annular.RS)
    (hface : HoleFaceKept splice face)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses)
    (edge : G.edgeSet)
    (hkept : ∀ dart ∈ web.annular.RS.dartsOn edge,
      splice.keep (web.annular.RS.vertOf dart))
    (honFace : ∀ dart ∈ web.annular.RS.dartsOn edge,
      dartOrbitFace web.annular.RS dart = face)
    (outDart :
      (outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem.D)
    (houtDart : outDart ∈
      (outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem.dartsOn
        (outputBoundaryEdge splice hsimple edge hkept)) :
    dartOrbitFace
        (outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem
        outDart =
      outputGraphFaceOfHoleFaceKept splice face hface hsimple := by
  let internal := internalDartOfEdgeKept web.annular.RS splice.keep edge hkept
  let literal : splice.output.D := Sum.inl internal
  let hinjective := output_endpoints_injective splice ambientEndpointsInjective hsimple
  let graphDart := primalDartEquiv splice.output hinjective literal
  have hgraphEdge :
      (outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem.edgeOf
          graphDart = outputBoundaryEdge splice hsimple edge hkept := by
    have hliteralEdge : splice.output.edgeOf literal =
        retainedInternalSpliceEdge web.annular.RS splice.keep
          splice.left.crossingEdge splice.right.crossingEdge
          splice.leftCrosses splice.rightCrosses splice.leftInjective
          splice.rightInjective splice.cover splice.disjoint splice.outer_kept
          splice.seamEndpoints internal := by
      rfl
    unfold outputBoundaryEdge
    rw [← hliteralEdge]
    exact graphData_edgeOf_primalDartEquiv_eq_edgeEquiv
      splice.output hinjective literal
  have houtEdge :
      (outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem.edgeOf
          outDart = outputBoundaryEdge splice hsimple edge hkept :=
    ((outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem.mem_dartsOn).1
      houtDart
  rcases (outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem.edge_fiber_two_cases
      hgraphEdge houtEdge with hsame | hopposite
  · subst outDart
    have hfaceOut :=
      outputGraphFaceOfHoleFaceKept_eq_dartOrbitFace splice face hface hsimple
        internal.1 (honFace internal.1.1
          ((web.annular.RS.mem_dartsOn).2
            (internalDartOfEdgeKept_edgeOf web.annular.RS splice.keep edge hkept)))
    rw [retainedDartEquivMatchedParts_of_internal splice internal] at hfaceOut
    exact hfaceOut.symm
  · subst outDart
    have halphaOn : web.annular.RS.alpha internal.1.1 ∈
        web.annular.RS.dartsOn edge :=
      web.annular.RS.alpha_mem_dartsOn
        ((web.annular.RS.mem_dartsOn).2
          (internalDartOfEdgeKept_edgeOf web.annular.RS splice.keep edge hkept))
    let alphaInternal := internalAlpha web.annular.RS splice.keep internal
    have halphaFace : dartOrbitFace web.annular.RS alphaInternal.1.1 = face := by
      exact honFace alphaInternal.1.1 (by
        simpa [alphaInternal, internalAlpha_val] using halphaOn)
    have hfaceOut := outputGraphFaceOfHoleFaceKept_eq_dartOrbitFace splice face hface hsimple
        alphaInternal.1 halphaFace
    rw [retainedDartEquivMatchedParts_of_internal splice alphaInternal] at hfaceOut
    have hliteralAlpha : splice.output.alpha literal = Sum.inl alphaInternal := by
      exact orderedCutRetainedVertexRotationSystem_alpha_interior
        web.annular.RS splice.keep splice.left.crossingEdge
        splice.right.crossingEdge splice.leftCrosses splice.rightCrosses
        splice.leftInjective splice.rightInjective splice.cover splice.disjoint
        splice.outer_kept splice.seamEndpoints internal
    rw [← hliteralAlpha] at hfaceOut
    rw [primalDartEquiv_alpha splice.output hinjective literal] at hfaceOut
    exact hfaceOut.symm

/-- Every ordered inner boundary dart of the shortened graph lies on the
transported inner hole. -/
theorem outputGraph_innerBoundaryEdgeDarts_on_innerHole
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses) :
    ∀ inner : Fin 5,
      ∀ dart ∈
        (outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem.dartsOn
          ((outputBoundaryData splice hinner houter hsimple).innerBoundaryEdge inner),
        dartOrbitFace
            (outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem dart =
          outputGraphFaceOfHoleFaceKept splice
            web.annular.cellulation.innerHole hinner hsimple := by
  intro inner dart hdart
  let hkept := innerBoundaryKept_of_innerHoleFaceKept splice hinner inner
  apply outputGraph_boundaryEdgeDarts_on_holeFace splice
    web.annular.cellulation.innerHole hinner hsimple
    (data.innerBoundaryEdge inner) hkept
  · intro source hsource
    exact web.annular.innerBoundaryEdgeDarts_on_innerHole inner source hsource
  · simpa [outputBoundaryData, outputInnerBoundaryEdge, hkept] using hdart

/-- Every ordered outer boundary dart of the shortened graph lies on the
transported outer hole. -/
theorem outputGraph_outerBoundaryEdgeDarts_on_outerHole
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses) :
    ∀ outer : Fin 5,
      ∀ dart ∈
        (outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem.dartsOn
          ((outputBoundaryData splice hinner houter hsimple).outerBoundaryEdge outer),
        dartOrbitFace
            (outputGraphData splice ambientEndpointsInjective hsimple).toRotationSystem dart =
          outputGraphFaceOfHoleFaceKept splice
            web.annular.cellulation.outerHole houter hsimple := by
  intro outer dart hdart
  let hkept := outerBoundaryKept_of_outerHoleFaceKept splice houter outer
  apply outputGraph_boundaryEdgeDarts_on_holeFace splice
    web.annular.cellulation.outerHole houter hsimple
    (data.outerBoundaryEdge outer) hkept
  · intro source hsource
    exact web.annular.outerBoundaryEdgeDarts_on_outerHole outer source hsource
  · simpa [outputBoundaryData, outputOuterBoundaryEdge, hkept] using hdart

/-- The shortened graph now carries the complete source-facing annular
embedding, not merely a cellulation and two named quotient faces. -/
def outputAnnularEmbedding
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
    ClosedWebAnnularEmbedding
      (outputBoundaryData splice hinner houter hsimple) where
  cellulation := outputCellulation splice hinner houter hsimple hretained hbalance
  outer_dart_on_outerHole :=
    outputGraph_outer_dart_on_outerHole splice houter hsimple
  innerBoundaryEdgeDarts_on_innerHole :=
    outputGraph_innerBoundaryEdgeDarts_on_innerHole splice hinner houter hsimple
  outerBoundaryEdgeDarts_on_outerHole :=
    outputGraph_outerBoundaryEdgeDarts_on_outerHole splice hinner houter hsimple

end

end GoertzelV24ClosedWebSpliceGraphAnnularEmbedding

end Mettapedia.GraphTheory.FourColor
