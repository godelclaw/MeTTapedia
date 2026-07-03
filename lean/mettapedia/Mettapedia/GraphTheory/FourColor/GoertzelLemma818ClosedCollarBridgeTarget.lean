import Mettapedia.GraphTheory.FourColor.GoertzelLemma814

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: closed-collar bridge target

This module states the finite target opened after the length-2/3 closed-collar
lab.  Existing `chainLKRInAudit` checks fixed first-input fibers.  The
section-9.2 collar step needs the cyclically re-glued fiber with the closing
edges fixed, so the target below uses a separate closed-collar edge model.

No certificate is asserted here: `closedCollarS2BridgeTarget` and
`section92S2BridgeLemmaTarget` are the next statements to prove.
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
def closedCollarS2BridgeTargetForWord (orients : List TauOrient) : Prop :=
  ∀ key, key ∈ colorAssignments4 → closedCollarFiberKempeConnected orients key

def closedCollarS2BridgeTarget : Prop :=
  ∀ orients, orients ∈ closedCollarL1Words →
    closedCollarS2BridgeTargetForWord orients

def gate2FirstInputCertificate (orients : List TauOrient) : Prop :=
  chainLKRInAudit orients = true

/--
The section-9.2 bridge target: first-input chain certificates for the same
finite words must lift to the cyclic closed-collar fibers with closing edges
fixed.
-/
def section92S2BridgeLemmaTarget : Prop :=
  (∀ orients, orients ∈ closedCollarL1Words → gate2FirstInputCertificate orients) →
    closedCollarS2BridgeTarget

theorem section92S2BridgeLemmaTarget_of_closedCollarS2BridgeTarget
    (h : closedCollarS2BridgeTarget) :
    section92S2BridgeLemmaTarget := by
  intro _hFirstInput
  exact h

end GoertzelLemma818ClosedCollarBridgeTarget

end Mettapedia.GraphTheory.FourColor
