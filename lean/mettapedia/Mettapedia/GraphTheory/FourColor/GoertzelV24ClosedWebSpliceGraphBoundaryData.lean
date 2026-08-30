import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceGraphHoleTransport

/-!
# Ordered boundary data on the graph-backed splice output

When both named hole faces lie outside the pumped region, all ten source
boundary stubs and their incident edges survive as old internal splice data.
This module transports their order and injectivity to the computed primal
simple graph and constructs its `AnnularBoundaryData`.

This is the ordered carrier datum only.  In particular, it does not yet prove
the graph-level `WellFormed` fields or package an output annular cellulation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSystemPrimalEdgePresentation
open GoertzelV24RotationSystemPrimalEdgePresentation.OrderedCutSpliceData
open GoertzelV24SimpleGraphRotationEndpointInjective
open GoertzelV24SpliceUnification

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

attribute [-instance] GoertzelV24SeamFaceArcPartition.hitPointFintype

attribute [local instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype

/-- Choose a literal internal dart over an edge whose complete dart fiber is
retained. -/
def internalDartOfEdgeKept (RS : RotationSystem V E) (keep : V → Prop)
    (edge : E)
    (hkept : ∀ dart ∈ RS.dartsOn edge, keep (RS.vertOf dart)) :
    InternalDart RS keep := by
  have hpositive : 0 < (RS.dartsOn edge).card := by
    rw [RS.dartsOn_card_two]
    omega
  let dart := Classical.choose (Finset.card_pos.mp hpositive)
  have hdart : dart ∈ RS.dartsOn edge :=
    Classical.choose_spec (Finset.card_pos.mp hpositive)
  refine ⟨⟨dart, hkept dart hdart⟩, ?_⟩
  apply hkept (RS.alpha dart)
  apply RS.mem_dartsOn.2
  rw [RS.edge_alpha]
  exact RS.mem_dartsOn.1 hdart

@[simp] theorem internalDartOfEdgeKept_edgeOf (RS : RotationSystem V E)
    (keep : V → Prop) (edge : E)
    (hkept : ∀ dart ∈ RS.dartsOn edge, keep (RS.vertOf dart)) :
    RS.edgeOf (internalDartOfEdgeKept RS keep edge hkept).1.1 = edge := by
  exact RS.mem_dartsOn.1
    (Classical.choose_spec (Finset.card_pos.mp (by
      rw [RS.dartsOn_card_two]
      omega)))

namespace Instance

variable {W : Type*} [Fintype W] [DecidableEq W]
  {G : SimpleGraph W} [DecidableRel G.Adj]
  {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
  {n terminalCount faceFragmentCount : Nat}
  {web : Instance data coloring}

local instance sourceEdgeSetDecidableEqSpliceGraphBoundaryData : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

private abbrev ambientEndpointsInjective :
    Function.Injective web.annular.RS.endpoints :=
  endpoints_injective web.annular.cellulation.rotation

private abbrev innerKept
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole) :
    ProtectedInnerInterface.InnerBoundaryKept splice :=
  innerBoundaryKept_of_innerHoleFaceKept splice hinner

private abbrev outerKept
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole) :
    ProtectedInnerInterface.OuterBoundaryKept splice :=
  outerBoundaryKept_of_outerHoleFaceKept splice houter

/-- Ordered inner source stubs, retained as vertices of the shortened graph. -/
def outputInnerStub
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole) :
    Fin 5 ↪ RetainedVertex splice.keep where
  toFun := ProtectedInnerInterface.retainedInnerStub splice
    (innerKept splice hinner)
  inj' := by
    intro first second heq
    apply data.innerStub.injective
    exact congrArg Subtype.val heq

/-- Ordered outer source stubs, retained as vertices of the shortened graph. -/
def outputOuterStub
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole) :
    Fin 5 ↪ RetainedVertex splice.keep where
  toFun := ProtectedInnerInterface.retainedOuterStub splice
    (outerKept splice houter)
  inj' := by
    intro first second heq
    apply data.outerStub.injective
    exact congrArg Subtype.val heq

/-- A completely retained old boundary edge, presented as an edge of the
computed shortened simple graph. -/
def outputBoundaryEdge
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses)
    (edge : G.edgeSet)
    (hkept : ∀ dart ∈ web.annular.RS.dartsOn edge,
      splice.keep (web.annular.RS.vertOf dart)) :
    (rotationPrimalGraph splice.output).edgeSet :=
  outputEdgeEquiv splice ambientEndpointsInjective hsimple
    (retainedInternalSpliceEdge web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses splice.leftInjective
      splice.rightInjective splice.cover splice.disjoint splice.outer_kept
      splice.seamEndpoints
      (internalDartOfEdgeKept web.annular.RS splice.keep edge hkept))

/-- Distinct retained old edges remain distinct in the computed shortened
simple graph. -/
theorem outputBoundaryEdge_injective
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses)
    {first second : G.edgeSet}
    (hfirst : ∀ dart ∈ web.annular.RS.dartsOn first,
      splice.keep (web.annular.RS.vertOf dart))
    (hsecond : ∀ dart ∈ web.annular.RS.dartsOn second,
      splice.keep (web.annular.RS.vertOf dart))
    (heq : outputBoundaryEdge splice hsimple first hfirst =
      outputBoundaryEdge splice hsimple second hsecond) :
    first = second := by
  have hold := (retainedInternalSpliceEdge_eq_iff web.annular.RS splice.keep
    splice.left.crossingEdge splice.right.crossingEdge
    splice.leftCrosses splice.rightCrosses splice.leftInjective
    splice.rightInjective splice.cover splice.disjoint splice.outer_kept
    splice.seamEndpoints
    (internalDartOfEdgeKept web.annular.RS splice.keep first hfirst)
    (internalDartOfEdgeKept web.annular.RS splice.keep second hsecond)).1
      ((outputEdgeEquiv splice ambientEndpointsInjective hsimple).injective heq)
  simpa only [internalDartOfEdgeKept_edgeOf] using hold

/-- Ordered inner source edges on the shortened primal graph. -/
def outputInnerBoundaryEdge
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses) :
    Fin 5 ↪ (rotationPrimalGraph splice.output).edgeSet where
  toFun := fun port => outputBoundaryEdge splice hsimple
    (data.innerBoundaryEdge port) (innerKept splice hinner port)
  inj' := by
    intro first second heq
    apply data.innerBoundaryEdge.injective
    exact outputBoundaryEdge_injective splice hsimple
      (innerKept splice hinner first) (innerKept splice hinner second) heq

/-- Ordered outer source edges on the shortened primal graph. -/
def outputOuterBoundaryEdge
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses) :
    Fin 5 ↪ (rotationPrimalGraph splice.output).edgeSet where
  toFun := fun port => outputBoundaryEdge splice hsimple
    (data.outerBoundaryEdge port) (outerKept splice houter port)
  inj' := by
    intro first second heq
    apply data.outerBoundaryEdge.injective
    exact outputBoundaryEdge_injective splice hsimple
      (outerKept splice houter first) (outerKept splice houter second) heq

/-- The shortened primal graph inherits both ordered five-port boundary
interfaces.  No graph-level well-formedness claim is bundled here. -/
def outputBoundaryData
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses) :
    AnnularBoundaryData (rotationPrimalGraph splice.output) 5 where
  innerStub := outputInnerStub splice hinner
  outerStub := outputOuterStub splice houter
  innerBoundaryEdge := outputInnerBoundaryEdge splice hinner hsimple
  outerBoundaryEdge := outputOuterBoundaryEdge splice houter hsimple

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
