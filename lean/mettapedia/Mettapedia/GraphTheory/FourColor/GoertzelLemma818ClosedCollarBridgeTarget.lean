import Mettapedia.GraphTheory.FourColor.GoertzelLemma814
import Mettapedia.GraphTheory.EdgeColoring
import Mettapedia.GraphTheory.Kempe

namespace Mettapedia.GraphTheory.FourColor

/-!
# Length-2/3 radial-closing-edge fiber census and manuscript S2 target

The finite encoded model below checks words of length 2 and 3 while fixing the
four edges used to close the radial cut. This is distinct from the manuscript's
S2 claim, which fixes every outer-boundary stub and ranges over collars of
arbitrary length; the graph-facing definition at the end states that property.
-/

namespace GoertzelLemma818ClosedCollarBridgeTarget

open GoertzelLemma814

/-- The length-2 and length-3 tau/mirror-tau words covered by the L1 closed-collar lab. -/
def closedCollarL1Words : List (List TauOrient) :=
  tauOrientWords2 ++ tauOrientWords3

def closedCollarL1WordCoverageAudit : Bool :=
  closedCollarL1Words.length == 12
    && closedCollarL1Words.all (fun word => word.length == 2 || word.length == 3)

theorem closedCollarL1WordCoverageAudit_ok :
    closedCollarL1WordCoverageAudit = true := by
  decide

def closedCollarIsInputStub (orients : List TauOrient) (ge : ChainEdge) : Bool :=
  (tauOrientInputOrder (tauOrientAt orients ge.occ)).contains ge.edge

def closedCollarIsOutputStub (orients : List TauOrient) (ge : ChainEdge) : Bool :=
  (tauOrientOutputOrder (tauOrientAt orients ge.occ)).contains ge.edge

/--
Representative edges for the closed collar: every input stub is represented by
the preceding output stub, including the first input stubs after cyclic
re-gluing.
-/
def closedCollarIsRepresentativeEdge
    (orients : List TauOrient) (ge : ChainEdge) : Bool :=
  !closedCollarIsInputStub orients ge

def closedCollarEdges (orients : List TauOrient) : List ChainEdge :=
  (chainLocalEdges orients).filter (closedCollarIsRepresentativeEdge orients)

def closedCollarNextOccurrence (orients : List TauOrient) (i : Nat) : Nat :=
  if i + 1 < orients.length then i + 1 else 0

def closedCollarEdgeEndpoints (orients : List TauOrient) (ge : ChainEdge) :
    ChainEndpoint × ChainEndpoint :=
  if closedCollarIsOutputStub orients ge then
    match indexOf? (tauOrientOutputOrder (tauOrientAt orients ge.occ)) ge.edge with
    | some k =>
        let nextOcc := closedCollarNextOccurrence orients ge.occ
        let nextInput := listGetD
          (tauOrientInputOrder (tauOrientAt orients nextOcc)) k TauEdge.B0
        ( ChainEndpoint.internal ge.occ (tauStubInternalEndpoint ge.edge)
        , ChainEndpoint.internal nextOcc (tauStubInternalEndpoint nextInput) )
    | none =>
        let p := edgeEndpoints ge.edge
        (tauEndpointToChainEndpoint ge.occ p.1, tauEndpointToChainEndpoint ge.occ p.2)
  else
    let p := edgeEndpoints ge.edge
    (tauEndpointToChainEndpoint ge.occ p.1, tauEndpointToChainEndpoint ge.occ p.2)

def closedCollarEdgesShareEndpoint
    (orients : List TauOrient) (e f : ChainEdge) : Bool :=
  if e == f then
    false
  else
    let ep := closedCollarEdgeEndpoints orients e
    let fp := closedCollarEdgeEndpoints orients f
    ep.1 == fp.1 || ep.1 == fp.2 || ep.2 == fp.1 || ep.2 == fp.2

def closedCollarComponentLayer (orients : List TauOrient)
    (states : List TauState) (a c : LColor) (seen : List ChainEdge) :
    List ChainEdge :=
  (closedCollarEdges orients).filter fun e =>
    chainEdgeInPair states a c e &&
      !seen.contains e &&
      seen.any (closedCollarEdgesShareEndpoint orients e)

def closeClosedCollarComponent (orients : List TauOrient)
    (states : List TauState) (a c : LColor) :
    Nat → List ChainEdge → List ChainEdge
  | 0, seen => seen
  | n + 1, seen =>
      let layer := closedCollarComponentLayer orients states a c seen
      closeClosedCollarComponent orients states a c n (appendFresh seen layer)

def closedCollarComponent (orients : List TauOrient)
    (states : List TauState) (a c : LColor) (seed : ChainEdge) :
    List ChainEdge :=
  if chainEdgeInPair states a c seed then
    closeClosedCollarComponent orients states a c (closedCollarEdges orients).length [seed]
  else
    []

def closedCollarClosingEdges (orients : List TauOrient) : List ChainEdge :=
  (chainOutputOrder orients (orients.length - 1)).map fun edge =>
    ({ occ := orients.length - 1, edge := edge } : ChainEdge)

def closedCollarComponentAvoidsClosingEdges
    (orients : List TauOrient) (component : List ChainEdge) : Bool :=
  !component.any (fun e => (closedCollarClosingEdges orients).contains e)

def closedCollarSwitchedColor (_orients : List TauOrient)
    (states : List TauState) (component : List ChainEdge)
    (a c : LColor) (ge : ChainEdge) : LColor :=
  if component.contains ge then swapColor a c (chainEdgeColor states ge)
  else chainEdgeColor states ge

def closedCollarAgreesWithSwitch (orients : List TauOrient)
    (s t : List TauState) (component : List ChainEdge) (a c : LColor) :
    Bool :=
  (closedCollarEdges orients).all fun ge =>
    colorEq (chainEdgeColor t ge)
      (closedCollarSwitchedColor orients s component a c ge)

def closedCollarSingleKempeStep
    (orients : List TauOrient) (s t : List TauState) : Bool :=
  colorPairs.any fun pair =>
    let a := pair.1
    let c := pair.2
    (closedCollarEdges orients).any fun seed =>
      let component := closedCollarComponent orients s a c seed
      !component.isEmpty &&
        closedCollarComponentAvoidsClosingEdges orients component &&
        closedCollarAgreesWithSwitch orients s t component a c

def closedCollarClosureCompatible
    (orients : List TauOrient) (states : List TauState) : Bool :=
  compatibleAdjacent
    (tauOrientAt orients (orients.length - 1))
    (tauOrientAt orients 0)
    (chainStateAt states (orients.length - 1))
    (chainStateAt states 0)

def closedCollarCompatibleStates
    (orients : List TauOrient) (states : List TauState) : Bool :=
  compatibleChainStates orients states &&
    closedCollarClosureCompatible orients states

def allClosedCollarStates (orients : List TauOrient) :
    List (List TauState) :=
  (allChainStates orients).filter (closedCollarClosureCompatible orients)

def closedCollarKey (orients : List TauOrient)
    (states : List TauState) : List LColor :=
  (closedCollarClosingEdges orients).map (chainEdgeColor states)

def closedCollarFiberFrom (orients : List TauOrient)
    (statesList : List (List TauState)) (key : List LColor) :
    List (List TauState) :=
  statesList.filter fun states => closedCollarKey orients states == key

def closedCollarFiber (orients : List TauOrient) (key : List LColor) :
    List (List TauState) :=
  closedCollarFiberFrom orients (allClosedCollarStates orients) key

def ClosedCollarFiberPoint (orients : List TauOrient) (key : List LColor) :
    Type :=
  { states : List TauState // states ∈ closedCollarFiber orients key }

def closedCollarKempeStep
    (orients : List TauOrient) (key : List LColor)
    (x y : ClosedCollarFiberPoint orients key) : Prop :=
  closedCollarSingleKempeStep orients x.1 y.1 = true

def closedCollarFiberKempeConnected
    (orients : List TauOrient) (key : List LColor) : Prop :=
  ∀ x y : ClosedCollarFiberPoint orients key,
    Relation.ReflTransGen (closedCollarKempeStep orients key) x y

/--
The closed-collar S2 target suggested by the length-2/3 lab: each fixed
closing-edge fiber is empty or connected by Kempe switches disjoint from the
closing edges.  Empty fibers are covered because the subtype has no points.
-/
def closedCollarLength23RadialClosingEdgeFiberCensusForWord
    (orients : List TauOrient) : Prop :=
  ∀ key, key ∈ colorAssignments4 → closedCollarFiberKempeConnected orients key

/-- The certified finite census: length-2/3 tau/mirror words, with the four
radial closing edges fixed. -/
def closedCollarLength23RadialClosingEdgeFiberCensus : Prop :=
  ∀ orients, orients ∈ closedCollarL1Words →
    closedCollarLength23RadialClosingEdgeFiberCensusForWord orients

def gate2FirstInputCertificate (orients : List TauOrient) : Prop :=
  chainLKRInAudit orients = true

/-! ## Manuscript-scale S2 -/

/-- Two graph edge colorings have identical colors on every designated outer
boundary stub. -/
def edgeColoringsAgreeOnOuterStubs {G : SimpleGraph V}
    (outerStubs : Finset G.edgeSet)
    (C D : G.EdgeColoring LColor) : Prop :=
  ∀ e, e ∈ outerStubs → C e = D e

/-- One genuine edge-Kempe switch whose component avoids every designated
outer boundary stub. -/
noncomputable def outerStubAvoidingEdgeKempeStep {G : SimpleGraph V}
    (outerStubs : Finset G.edgeSet)
    (C D : G.EdgeColoring LColor) : Prop :=
  ∃ colorOne colorTwo,
    ∃ K : (C.bicoloredSubgraph colorOne colorTwo).ConnectedComponent,
      (∀ e, e ∈ outerStubs →
          e ∉ C.kempeComponentSet colorOne colorTwo K) ∧
        D = C.swapOnKempeComponent colorOne colorTwo K

/-- The fiber of actual proper edge colorings with all outer stub colors fixed
to those of `base`. -/
def OuterStubFixedEdgeColoringFiber {G : SimpleGraph V}
    (outerStubs : Finset G.edgeSet) (base : G.EdgeColoring LColor) : Type :=
  { C : G.EdgeColoring LColor //
      edgeColoringsAgreeOnOuterStubs outerStubs base C }

/-- The graph-facing S2 statement for one actual collar graph. -/
noncomputable def manuscriptS2AllOuterStubsFixedForCollar
    {G : SimpleGraph V} (outerStubs : Finset G.edgeSet) : Prop :=
  ∀ base, ∀ x y : OuterStubFixedEdgeColoringFiber outerStubs base,
    Relation.ReflTransGen
      (fun C D => outerStubAvoidingEdgeKempeStep outerStubs C.1 D.1) x y

/-- Manuscript Section 9.2 S2, stated for an arbitrary indexed family of
actual collar graphs: every collar, without a length bound, has connected
all-outer-stubs-fixed fibers under outer-stub-avoiding edge-Kempe switches.

The length-2/3 encoded census above proves a different finite property. -/
noncomputable def ManuscriptSection92S2AllOuterStubsFixedArbitraryCollar
    {I : Type} (Vertex : I → Type) [∀ i, DecidableEq (Vertex i)]
    (collarGraph : ∀ i, SimpleGraph (Vertex i))
    (outerStubs : ∀ i, Finset (collarGraph i).edgeSet) : Prop :=
  ∀ i, manuscriptS2AllOuterStubsFixedForCollar (outerStubs i)

end GoertzelLemma818ClosedCollarBridgeTarget

end Mettapedia.GraphTheory.FourColor
