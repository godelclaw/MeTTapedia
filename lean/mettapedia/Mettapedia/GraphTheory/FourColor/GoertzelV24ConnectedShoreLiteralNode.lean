import Mettapedia.GraphTheory.FourColor.GoertzelV24MajorityShoreStateDescent
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationBoundaryBridge

/-!
# Literal descent nodes from connected edge shores

The finite descent consumes rooted open shores with two distinct boundary
darts.  Those choices are not extra branch-decomposition data.  In a cubic,
connected, bridge-free map they follow from the two shores being nonempty:
cubicity supplies a dart at a chosen vertex on each side, while a boundary
with only one edge would make that edge a bridge.

This file packages those consequences into the literal node used by the
physical majority-shore descent.  The external decomposition supplier need
only provide connected complementary edge shores, nonempty majority sides,
and the usual middle-set bound.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ConnectedShoreLiteralNode

open GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24FaceDualConnectedness
open GoertzelV24FiniteTreeInterfacePumping
open GoertzelV24FiniteTreeInterfacePumping.DecompTree
open GoertzelV24MajorityShoreNormalizedState
open GoertzelV24MajorityShoreStateDescent
open GoertzelV24NormalizedShoreDescent
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationEdgeBridge
open GoertzelV24RotationBoundaryBridge
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V E : Type u} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-! ## A bridge-free proper vertex side has at least two boundary darts -/

/-- Boundary darts based on a finite vertex side are canonically indexed by
the rotation-system edges crossing that side. -/
noncomputable def boundaryDartEquivVertexSideEdgeBoundary
    (RS : RotationSystem V E) (side : Finset V) :
    BoundaryDart RS (fun vertex => vertex ∈ side) ≃
      {edge : E // edge ∈ RS.vertexSideEdgeBoundary side} where
  toFun dart :=
    ⟨RS.edgeOf dart.1.1,
      RS.boundaryDart_edge_mem_vertexSideEdgeBoundary side dart⟩
  invFun edge :=
    RS.boundaryDartOfCrossingEdge side edge.1 edge.2
  left_inv dart := by
    apply boundaryDart_eq_of_edgeOf_eq
    simp
  right_inv edge := by
    apply Subtype.ext
    simp

/-- Replacing a finite predicate by its filtered vertex finset does not
change its literal boundary carrier. -/
noncomputable def boundaryDartEquivFilter
    (RS : RotationSystem V E) (keep : V → Prop) [DecidablePred keep] :
    BoundaryDart RS keep ≃
      BoundaryDart RS (fun vertex => vertex ∈ Finset.univ.filter keep) := by
  classical
  exact
    { toFun := fun dart =>
        ⟨⟨dart.1.1, by simpa using dart.1.2⟩, by simpa using dart.2⟩
      invFun := fun dart =>
        ⟨⟨dart.1.1, by simpa using dart.1.2⟩, by simpa using dart.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Pointwise equivalent vertex predicates give identical literal boundary
carriers, with ambient darts unchanged. -/
def boundaryDartEquivOfIff
    (RS : RotationSystem V E) {first second : V → Prop}
    (hiff : ∀ vertex, first vertex ↔ second vertex) :
    BoundaryDart RS first ≃ BoundaryDart RS second where
  toFun dart :=
    ⟨⟨dart.1.1, (hiff _).1 dart.1.2⟩, by
      intro hsecond
      exact dart.2 ((hiff _).2 hsecond)⟩
  invFun dart :=
    ⟨⟨dart.1.1, (hiff _).2 dart.1.2⟩, by
      intro hfirst
      exact dart.2 ((hiff _).1 hfirst)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A connected graph cannot have a proper nonempty vertex side with empty
edge boundary. -/
theorem vertexSideEdgeBoundary_nonempty_of_connected
    (RS : RotationSystem V E)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (side : Finset V) (hinside : ∃ vertex, vertex ∈ side)
    (houtside : ∃ vertex, vertex ∉ side) :
    (RS.vertexSideEdgeBoundary side).Nonempty := by
  classical
  obtain ⟨inside, hinside⟩ := hinside
  obtain ⟨outside, houtside⟩ := houtside
  have hreach : (rotationPrimalGraph RS).Reachable inside outside :=
    hconnected inside outside
  by_contra hempty
  have hempty' : RS.vertexSideEdgeBoundary side = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hstay : ∀ {left right : V},
      (rotationPrimalGraph RS).Adj left right → left ∈ side → right ∈ side := by
    rintro left right ⟨dart, hleft, hright⟩ hleftSide
    by_contra hrightSide
    have hedge : RS.edgeOf dart ∈ RS.vertexSideEdgeBoundary side := by
      rw [RS.mem_vertexSideEdgeBoundary_iff]
      have hdart : dart ∈ RS.dartsOn (RS.edgeOf dart) := by simp
      rw [RS.endpoints_eq_pair_of_mem hdart, hleft, hright]
      have hinter : ({left, right} : Finset V) ∩ side = {left} := by
        ext vertex
        simp only [Finset.mem_inter, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, hmem⟩
          · rfl
          · exact False.elim (hrightSide hmem)
        · rintro rfl
          exact ⟨Or.inl rfl, hleftSide⟩
      rw [hinter, Finset.card_singleton]
    rw [hempty'] at hedge
    exact Finset.notMem_empty _ hedge
  have hstayReach : ∀ {left right : V}, left ∈ side →
      (rotationPrimalGraph RS).Reachable left right → right ∈ side := by
    intro left right hleft hleftRight
    rw [SimpleGraph.reachable_iff_reflTransGen] at hleftRight
    induction hleftRight with
    | refl => exact hleft
    | tail _ hadj ih => exact hstay hadj ih
  have houtsideMem : outside ∈ side := hstayReach hinside hreach
  exact houtside houtsideMem

/-- In a connected bridge-free rotation system, every proper nonempty vertex
side exposes at least two boundary darts. -/
theorem two_le_card_boundaryDart_of_connected_edgeBridgeFree
    (RS : RotationSystem V E)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (hfree : EdgeBridgeFree RS) (keep : V → Prop)
    (hinside : ∃ vertex, keep vertex)
    (houtside : ∃ vertex, ¬ keep vertex) :
    2 ≤ Fintype.card (BoundaryDart RS keep) := by
  classical
  let side : Finset V := Finset.univ.filter keep
  have hinsideSide : ∃ vertex, vertex ∈ side := by
    obtain ⟨vertex, hvertex⟩ := hinside
    exact ⟨vertex, by simp [side, hvertex]⟩
  have houtsideSide : ∃ vertex, vertex ∉ side := by
    obtain ⟨vertex, hvertex⟩ := houtside
    exact ⟨vertex, by simp [side, hvertex]⟩
  have hboundaryNonempty :=
    vertexSideEdgeBoundary_nonempty_of_connected RS hconnected side
      hinsideSide houtsideSide
  have hboundaryNotOne : (RS.vertexSideEdgeBoundary side).card ≠ 1 := by
    intro hcard
    obtain ⟨edge, hedge⟩ := Finset.card_eq_one.mp hcard
    exact not_boundary_singleton_of_edgeBridgeFree RS hfree side edge hedge
  have hboundaryTwo : 2 ≤ (RS.vertexSideEdgeBoundary side).card := by
    have hpositive : 0 < (RS.vertexSideEdgeBoundary side).card :=
      Finset.card_pos.mpr hboundaryNonempty
    omega
  calc
    2 ≤ (RS.vertexSideEdgeBoundary side).card := hboundaryTwo
    _ = Fintype.card
        (BoundaryDart RS (fun vertex => vertex ∈ side)) := by
      symm
      calc
        Fintype.card (BoundaryDart RS (fun vertex => vertex ∈ side)) =
            Fintype.card {edge : E //
              edge ∈ RS.vertexSideEdgeBoundary side} :=
          Fintype.card_congr
            (boundaryDartEquivVertexSideEdgeBoundary RS side)
        _ = (RS.vertexSideEdgeBoundary side).card := Fintype.card_coe _
    _ = Fintype.card (BoundaryDart RS keep) := by
      symm
      exact Fintype.card_congr (boundaryDartEquivFilter RS keep)

/-- Cubicity supplies a rooted retained dart at every named vertex of a
chosen side. -/
noncomputable def retainedDartOfVertex
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (keep : V → Prop) (vertex : V) (hvertex : keep vertex) :
    RetainedDart RS keep := by
  have hcard : (RS.dartsAt vertex).card = 3 := hcubic vertex
  have hnonempty : (RS.dartsAt vertex).Nonempty := by
    rw [← Finset.card_pos, hcard]
    omega
  exact ⟨Classical.choose hnonempty, by
    have hmem := Classical.choose_spec hnonempty
    have hvert : RS.vertOf (Classical.choose hnonempty) = vertex := by
      simpa [RotationSystem.dartsAt] using hmem
    simpa [hvert] using hvertex⟩

/-! ## Graph-backed majority shores -/

variable {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Graph darts crossing a vertex predicate are exactly the literal boundary
darts of graph-backed rotation data. -/
def boundaryDartEquivCrossingSideDart
    (rotation : SimpleGraphDartRotation.Data G) (side : V → Prop) :
    BoundaryDart rotation.toRotationSystem side ≃
      CrossingSideDart G side where
  toFun dart :=
    ⟨dart.1.1, by simpa using dart.1.2, by simpa using dart.2⟩
  invFun dart :=
    ⟨⟨dart.1, by simpa using dart.2.1⟩, by simpa using dart.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [G.LocallyFinite] in
/-- The literal majority-shore width is the graph-theoretic number of
outgoing darts charged to the branch-decomposition middle set. -/
theorem boundaryWidth_eq_card_crossingSideDart
    (rotation : SimpleGraphDartRotation.Data G)
    (shore : Finset G.edgeSet) :
    boundaryWidth rotation shore =
      Fintype.card (CrossingSideDart G (majorityVertexSide G shore)) := by
  rw [boundaryWidth]
  exact Fintype.card_congr
    ((boundaryDartEquivOfIff rotation.toRotationSystem
        (fun vertex => majorityRetainedKeep_iff shore vertex)).trans
      (boundaryDartEquivCrossingSideDart rotation
        (majorityVertexSide G shore)))

namespace LiteralShoreNode

/-- Connected complementary edge shores produce the complete
literal node consumed by finite physical descent.  Roots and two distinct
exterior boundary darts are derived rather than supplied. -/
noncomputable def ofConnectedShore
    (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (shore : Finset G.edgeSet)
    (hshoreConnected : EdgeShoreConnected G shore)
    (hcomplementConnected :
      EdgeShoreConnected G (Finset.univ \ shore))
    (hmajorityNonempty : ∃ vertex, majorityVertexSide G shore vertex)
    (hcomplementNonempty :
      ∃ vertex, ¬ majorityVertexSide G shore vertex)
    (k w : Nat)
    (hwidthMiddle : (edgeShoreMiddleVertices G shore).card ≤ k)
    (hmiddle : (edgeShoreMiddleVertices G shore).card ≤ w) :
    LiteralShoreNode rotation k w := by
  classical
  let RS := rotation.toRotationSystem
  let innerVertex := Classical.choose hmajorityNonempty
  have hinnerVertex : majorityVertexSide G shore innerVertex :=
    Classical.choose_spec hmajorityNonempty
  let outsideVertex := Classical.choose hcomplementNonempty
  have houtsideVertex : ¬ majorityVertexSide G shore outsideVertex :=
    Classical.choose_spec hcomplementNonempty
  let innerOuter : RetainedDart RS (majorityRetainedKeep G shore) :=
    retainedDartOfVertex RS minimal.spherical.cubic
      (majorityRetainedKeep G shore) innerVertex
      ((majorityRetainedKeep_iff shore innerVertex).2 hinnerVertex)
  let outsideOuter : RetainedDart RS (majorityDeletedKeep G shore) :=
    retainedDartOfVertex RS minimal.spherical.cubic
      (majorityDeletedKeep G shore) outsideVertex
      ((majorityDeletedKeep_iff shore outsideVertex).2 houtsideVertex)
  have htwo : 2 ≤ Fintype.card
      (BoundaryDart RS (majorityDeletedKeep G shore)) :=
    two_le_card_boundaryDart_of_connected_edgeBridgeFree RS
      minimal.primalConnected minimal.edgeBridgeFree
      (majorityDeletedKeep G shore)
      ⟨outsideVertex,
        (majorityDeletedKeep_iff shore outsideVertex).2 houtsideVertex⟩
      ⟨innerVertex, by
        simpa [majorityDeletedKeep_iff shore innerVertex] using hinnerVertex⟩
  have hpair : ∃ first second :
      BoundaryDart RS (majorityDeletedKeep G shore), first ≠ second :=
    Fintype.exists_pair_of_one_lt_card (lt_of_lt_of_le Nat.one_lt_two htwo)
  let first := Classical.choose hpair
  let second := Classical.choose (Classical.choose_spec hpair)
  have hne : first ≠ second :=
    Classical.choose_spec (Classical.choose_spec hpair)
  have hcubicEdges :
      ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      rotation minimal.spherical.cubic
  have hwidth : boundaryWidth rotation shore ≤ k := by
    rw [boundaryWidth_eq_card_crossingSideDart rotation shore]
    exact (card_crossingSideDart_majority_le_middle hcubicEdges shore).trans
      hwidthMiddle
  exact
    { shore := shore
      shoreConnected := hshoreConnected
      complementConnected := hcomplementConnected
      majorityNonempty := ⟨innerVertex, hinnerVertex⟩
      complementNonempty := ⟨outsideVertex, houtsideVertex⟩
      outsideOuter := outsideOuter
      innerOuter := innerOuter
      widthBound := hwidth
      middleBound := hmiddle
      first := first
      second := second
      first_ne_second := hne }

end LiteralShoreNode

/-! ## A connected-shore tree consumed directly -/

/-- The nodewise data supplied by a bounded-width connected edge
decomposition.  It contains no roots, boundary coordinates, or chosen ports;
the completion below derives those from the minimal map. -/
structure ConnectedShoreNode (k w : Nat) where
  shore : Finset G.edgeSet
  shoreConnected : EdgeShoreConnected G shore
  complementConnected : EdgeShoreConnected G (Finset.univ \ shore)
  majorityNonempty : ∃ vertex, majorityVertexSide G shore vertex
  complementNonempty : ∃ vertex, ¬ majorityVertexSide G shore vertex
  widthMiddle : (edgeShoreMiddleVertices G shore).card ≤ k
  middleBound : (edgeShoreMiddleVertices G shore).card ≤ w

namespace ConnectedShoreNode

/-- Complete a connected-shore node to the literal node used by the physical
replacement theorem. -/
noncomputable def toLiteral
    (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {k w : Nat} (node : ConnectedShoreNode (G := G) k w) :
    LiteralShoreNode rotation k w :=
  LiteralShoreNode.ofConnectedShore rotation minimal node.shore
    node.shoreConnected node.complementConnected node.majorityNonempty
    node.complementNonempty k w node.widthMiddle node.middleBound

@[simp]
theorem toLiteral_shore
    (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {k w : Nat} (node : ConnectedShoreNode (G := G) k w) :
    (node.toLiteral rotation minimal).shore = node.shore :=
  rfl

/-- The exact finite state computed after completing the node. -/
noncomputable def cardPhasedState
    (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {k w : Nat} (node : ConnectedShoreNode (G := G) k w) :
    Fin (6 * w + 1) × StateAtBound.{u} k :=
  (node.toLiteral rotation minimal).cardPhasedState

end ConnectedShoreNode

/-- Proper nesting stated solely on the connected edge shores supplied by the
decomposition. -/
def StrictConnectedShoreTree {k w : Nat}
    (tree : DecompTree (ConnectedShoreNode (G := G) k w)) : Prop :=
  ∀ p : List (ConnectedShoreNode (G := G) k w), OnPath tree p →
    ∀ i j : Fin p.length, i < j → (p.get j).shore ⊂ (p.get i).shore

/-- **Bounded-width descent from connected shores.**  Once a reduced binary
tree supplies connected complementary edge shores, nonempty majority sides,
and middle-set bounds, all literal roots, ports, widths and exact states are
derived internally. -/
theorem vertexCount_le_of_connectedShoreTree
    (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (k w : Nat)
    (tree : DecompTree (ConnectedShoreNode (G := G) k w))
    (hstrict : StrictConnectedShoreTree tree)
    (hvertices : Fintype.card V ≤ 2 * nodeCount tree) :
    Fintype.card V ≤
      2 * (2 ^ ((6 * w + 1) *
        (∑ j : Fin (k + 1),
          Nat.factorial (j : Nat) * 2 ^ (3 ^ (j : Nat)))) - 1) := by
  have hnorepeat : NoRepeatedStateOnDescents
      (fun node : ConnectedShoreNode (G := G) k w =>
        node.cardPhasedState rotation minimal) tree := by
    apply noRepeatedStateOnDescents_of_get
    intro p hpath i j hij heq
    have hproper : (p.get j).shore ⊂ (p.get i).shore :=
      hstrict p hpath i j hij
    exact cardPhasedState_ne_of_ssubset rotation minimal
      ((p.get i).toLiteral rotation minimal)
      ((p.get j).toLiteral rotation minimal)
      (by simpa using hproper) heq
  have hbound := vertexCount_le hnorepeat 2 (Fintype.card V) hvertices
  rw [Fintype.card_prod, Fintype.card_fin,
    card_stateAtBound.{u} k] at hbound
  exact hbound

end

end GoertzelV24ConnectedShoreLiteralNode

end Mettapedia.GraphTheory.FourColor
