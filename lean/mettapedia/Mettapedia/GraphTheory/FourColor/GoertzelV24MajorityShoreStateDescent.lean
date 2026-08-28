import Mettapedia.GraphTheory.FourColor.GoertzelV24MajorityShorePhysicalReplacement
import Mettapedia.GraphTheory.FourColor.GoertzelV24NormalizedShoreDescent

/-!
# Literal majority-shore states consumed by physical descent

The finite descent stores shores of varying boundary width in one sigma type.
This module connects equality in that sigma type to the physical replacement
theorem.  In particular, the dependent equality of the state fields is
unpacked rather than hidden behind a caller-supplied cast.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MajorityShoreStateDescent

open GoertzelV24MajorityShoreNormalizedState
open GoertzelV24MajorityShorePhysicalReplacement
open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24FiniteTreeInterfacePumping
open GoertzelV24FiniteTreeInterfacePumping.DecompTree
open GoertzelV24NormalizedShoreDescent
open GoertzelV24RotationVertexCutProfile
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24ShoreStateDescent
open GoertzelV24SphereCutMaterial
open GoertzelV24TwoEdgeCutMinimality

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The exact normalized state of a literal majority shore, embedded in the
single finite carrier of all widths at most `k`. -/
noncomputable def boundedNormalizedState
    (rotation : SimpleGraphDartRotation.Data G)
    (shore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem
      (GoertzelV24ConnectedEdgeShoreStructuralData.majorityRetainedKeep G shore))
    (k : Nat) (hbound : boundaryWidth rotation shore ≤ k) :
    StateAtBound.{u} k :=
  ⟨⟨boundaryWidth rotation shore, by omega⟩,
    normalizedState rotation shore outer (boundaryWidth rotation shore) rfl⟩

/-- Transporting the width index of a normalized shore state is the same as
supplying the transported width proof to its definition. -/
theorem normalizedState_ndrec
    (rotation : SimpleGraphDartRotation.Data G)
    (shore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem
      (GoertzelV24ConnectedEdgeShoreStructuralData.majorityRetainedKeep G shore))
    (width : Nat) (hwidth : boundaryWidth rotation shore = width) :
    Eq.ndrec
        (normalizedState rotation shore outer
          (boundaryWidth rotation shore) rfl)
        hwidth =
      normalizedState rotation shore outer width hwidth := by
  cases hwidth
  rfl

set_option maxHeartbeats 1000000 in
/-- Equality of varying-width literal states exposes one common literal width
and the ordinary equality of normalized states required by physical
replacement. -/
theorem boundedNormalizedState_eq_elim
    (rotation : SimpleGraphDartRotation.Data G)
    (oldShore newShore : Finset G.edgeSet)
    (oldOuter : RetainedDart rotation.toRotationSystem
      (GoertzelV24ConnectedEdgeShoreStructuralData.majorityRetainedKeep G oldShore))
    (newOuter : RetainedDart rotation.toRotationSystem
      (GoertzelV24ConnectedEdgeShoreStructuralData.majorityRetainedKeep G newShore))
    (k : Nat)
    (oldBound : boundaryWidth rotation oldShore ≤ k)
    (newBound : boundaryWidth rotation newShore ≤ k)
    (hstate : boundedNormalizedState rotation oldShore oldOuter k oldBound =
      boundedNormalizedState rotation newShore newOuter k newBound) :
    ∃ width : Nat,
      ∃ oldWidth : boundaryWidth rotation oldShore = width,
      ∃ newWidth : boundaryWidth rotation newShore = width,
        normalizedState rotation oldShore oldOuter width oldWidth =
          normalizedState rotation newShore newOuter width newWidth := by
  rcases Sigma.ext_iff.mp hstate with ⟨hindex, hvalue⟩
  have hwidth : boundaryWidth rotation oldShore =
      boundaryWidth rotation newShore := congrArg Fin.val hindex
  refine ⟨boundaryWidth rotation newShore, hwidth, rfl, ?_⟩
  let oldState := normalizedState rotation oldShore oldOuter
    (boundaryWidth rotation oldShore) rfl
  let newState := normalizedState rotation newShore newOuter
    (boundaryWidth rotation newShore) rfl
  have hvalue' : oldState ≍ newState := hvalue
  have hrec : Eq.ndrec oldState hwidth ≍ oldState :=
    eqRec_heq hwidth oldState
  have htransported : Eq.ndrec oldState hwidth = newState :=
    eq_of_heq (hrec.trans hvalue')
  exact (normalizedState_ndrec rotation oldShore oldOuter _ hwidth).symm.trans
    htransported

/-- The physical descent theorem in the single varying-width state carrier
used by finite pumping.  Equality of sigma states supplies the common width
and its dependent state equality internally. -/
theorem no_nested_equal_boundedNormalizedState_of_strict_material
    (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (oldShore newShore : Finset G.edgeSet)
    (hsubset : newShore ⊆ oldShore)
    (hOldConnected : GoertzelV24ConnectedEdgeShoreMajority.EdgeShoreConnected
      G oldShore)
    (hOldComplementConnected :
      GoertzelV24ConnectedEdgeShoreMajority.EdgeShoreConnected G
        (Finset.univ \ oldShore))
    (hOldMajorityNonempty :
      ∃ vertex, GoertzelV24ConnectedEdgeShoreMajority.majorityVertexSide
        G oldShore vertex)
    (hOldComplementNonempty :
      ∃ vertex, ¬ GoertzelV24ConnectedEdgeShoreMajority.majorityVertexSide
        G oldShore vertex)
    (hNewConnected : GoertzelV24ConnectedEdgeShoreMajority.EdgeShoreConnected
      G newShore)
    (hNewComplementConnected :
      GoertzelV24ConnectedEdgeShoreMajority.EdgeShoreConnected G
        (Finset.univ \ newShore))
    (hNewMajorityNonempty :
      ∃ vertex, GoertzelV24ConnectedEdgeShoreMajority.majorityVertexSide
        G newShore vertex)
    (hNewComplementNonempty :
      ∃ vertex, ¬ GoertzelV24ConnectedEdgeShoreMajority.majorityVertexSide
        G newShore vertex)
    (outsideOuter : RetainedDart rotation.toRotationSystem
      (GoertzelV24ConnectedEdgeShoreStructuralData.majorityDeletedKeep
        G oldShore))
    (oldInnerOuter : RetainedDart rotation.toRotationSystem
      (GoertzelV24ConnectedEdgeShoreStructuralData.majorityRetainedKeep
        G oldShore))
    (newInnerOuter : RetainedDart rotation.toRotationSystem
      (GoertzelV24ConnectedEdgeShoreStructuralData.majorityRetainedKeep
        G newShore))
    (k : Nat)
    (oldBound : boundaryWidth rotation oldShore ≤ k)
    (newBound : boundaryWidth rotation newShore ≤ k)
    (hstate : boundedNormalizedState rotation oldShore oldInnerOuter k oldBound =
      boundedNormalizedState rotation newShore newInnerOuter k newBound)
    (first second : BoundaryDart rotation.toRotationSystem
      (GoertzelV24ConnectedEdgeShoreStructuralData.majorityDeletedKeep
        G oldShore))
    (hne : first ≠ second)
    (strictVertex : V)
    (hall : ∀ edge ∈ incidentEdgeFinset G strictVertex,
        edge ∈ oldShore \ newShore) : False := by
  obtain ⟨width, oldWidth, newWidth, heq⟩ :=
    boundedNormalizedState_eq_elim rotation oldShore newShore
      oldInnerOuter newInnerOuter k oldBound newBound hstate
  exact no_nested_equal_normalizedState_of_strict_material
    rotation minimal oldShore newShore hsubset
    hOldConnected hOldComplementConnected
    hOldMajorityNonempty hOldComplementNonempty
    hNewConnected hNewComplementConnected
    hNewMajorityNonempty hNewComplementNonempty
    outsideOuter oldInnerOuter newInnerOuter
    width oldWidth newWidth heq first second hne strictVertex hall

/-! ## A literal connected-shore decomposition -/

/-- One decomposition node with every literal datum consumed by the physical
replacement theorem.  No abstract replacement function is stored here: the
state is computed from the displayed shore and roots. -/
structure LiteralShoreNode
    (rotation : SimpleGraphDartRotation.Data G) (k w : Nat) where
  shore : Finset G.edgeSet
  shoreConnected : EdgeShoreConnected G shore
  complementConnected : EdgeShoreConnected G (Finset.univ \ shore)
  majorityNonempty : ∃ vertex, majorityVertexSide G shore vertex
  complementNonempty : ∃ vertex, ¬ majorityVertexSide G shore vertex
  outsideOuter : RetainedDart rotation.toRotationSystem
    (majorityDeletedKeep G shore)
  innerOuter : RetainedDart rotation.toRotationSystem
    (majorityRetainedKeep G shore)
  widthBound : boundaryWidth rotation shore ≤ k
  middleBound : (edgeShoreMiddleVertices G shore).card ≤ w
  first : BoundaryDart rotation.toRotationSystem
    (majorityDeletedKeep G shore)
  second : BoundaryDart rotation.toRotationSystem
    (majorityDeletedKeep G shore)
  first_ne_second : first ≠ second

namespace LiteralShoreNode

/-- The actual varying-width seam-and-support state read from a certified
literal shore. -/
noncomputable def state
    {rotation : SimpleGraphDartRotation.Data G} {k w : Nat}
    (node : LiteralShoreNode rotation k w) : StateAtBound.{u} k :=
  boundedNormalizedState rotation node.shore node.innerOuter k node.widthBound

/-- The finite pumping state, augmented by shore cardinality modulo the
period that forces a strict cubic star between repeated states. -/
noncomputable def cardPhasedState
    {rotation : SimpleGraphDartRotation.Data G} {k w : Nat}
    (node : LiteralShoreNode rotation k w) :
    Fin (6 * w + 1) × StateAtBound.{u} k :=
  (shoreCardPhase w node.shore, node.state)

end LiteralShoreNode

/-- Along every decomposition descent, later literal shores are proper
subsets of earlier shores.  This is the exact laminar/reduced-tree condition
the connected decomposition adapter must establish. -/
def StrictLiteralShoreTree
    {rotation : SimpleGraphDartRotation.Data G} {k w : Nat}
    (tree : DecompTree (LiteralShoreNode rotation k w)) : Prop :=
  ∀ p : List (LiteralShoreNode rotation k w), OnPath tree p →
    ∀ i j : Fin p.length, i < j → (p.get j).shore ⊂ (p.get i).shore

/-- Every graph edge has an endpoint, in the incidence relation used by the
strict-slab counting theorem. -/
theorem exists_incident_vertex (edge : G.edgeSet) :
    ∃ vertex : V, vertex ∈ (edge : Sym2 V) := by
  induction edge.1 using Sym2.inductionOn with
  | _ left right => exact ⟨left, Sym2.mem_mk_left left right⟩

/-- Two strictly nested certified shores cannot carry the same phased exact
state in a graph-backed vertex-minimal Tait counterexample.  This is the
pairwise pumping atom shared by the linear-corridor and decomposition-tree
consumers below. -/
theorem cardPhasedState_ne_of_ssubset
    (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {k w : Nat}
    (oldNode newNode : LiteralShoreNode rotation k w)
    (hproper : newNode.shore ⊂ oldNode.shore) :
    oldNode.cardPhasedState ≠ newNode.cardPhasedState := by
  intro heq
  let incident : V → G.edgeSet → Prop :=
    fun vertex edge => vertex ∈ (edge : Sym2 V)
  have hcubicEdges :
      ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      rotation minimal.spherical.cubic
  have hphase : shoreCardPhase w oldNode.shore =
      shoreCardPhase w newNode.shore :=
    congrArg Prod.fst heq
  have hstate : oldNode.state = newNode.state :=
    congrArg Prod.snd heq
  obtain ⟨strictVertex, -, hall⟩ :=
    exists_strict_slab_vertex_of_cardPhaseRepeat incident w hproper
      (exists_incident_vertex (G := G)) (fun vertex => by
        simpa only [incident, incidentEdgeFinset] using
          (Nat.le_of_eq (hcubicEdges vertex))) newNode.middleBound
      oldNode.middleBound hphase.symm
  exact no_nested_equal_boundedNormalizedState_of_strict_material
    rotation minimal oldNode.shore newNode.shore hproper.1
    oldNode.shoreConnected oldNode.complementConnected
    oldNode.majorityNonempty oldNode.complementNonempty
    newNode.shoreConnected newNode.complementConnected
    newNode.majorityNonempty newNode.complementNonempty
    oldNode.outsideOuter oldNode.innerOuter newNode.innerOuter
    k oldNode.widthBound newNode.widthBound hstate
    oldNode.first oldNode.second oldNode.first_ne_second
    strictVertex (by
      intro edge hedge
      exact hall edge (by
        simpa only [incident, incidentEdgeFinset,
          Finset.mem_filter, Finset.mem_univ, true_and] using hedge))

/-- **Linear source-corridor pumping.**  A strictly nested sequence of
literal certified shores in a graph-backed least Tait counterexample has at
most the exact number of phased normalized states.  Unlike the older transfer
formulation, this conclusion needs neither a self-loop premise nor a
caller-supplied replacement operation: a repeated cumulative state is fed
directly to the physical splice. -/
theorem length_le_of_literalShoreChain
    (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (k w length : Nat)
    (nodes : Fin length → LiteralShoreNode rotation k w)
    (hstrict : ∀ i j : Fin length, i < j →
      (nodes j).shore ⊂ (nodes i).shore) :
    length ≤
      (6 * w + 1) *
        (∑ j : Fin (k + 1),
          Nat.factorial (j : Nat) * 2 ^ (3 ^ (j : Nat))) := by
  let state : Fin length → Fin (6 * w + 1) × StateAtBound.{u} k :=
    fun i => (nodes i).cardPhasedState
  have hinjective : Function.Injective state := by
    intro i j heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact cardPhasedState_ne_of_ssubset rotation minimal
        (nodes i) (nodes j) (hstrict i j hij) (by
          simpa only [state] using heq)
    · exact cardPhasedState_ne_of_ssubset rotation minimal
        (nodes j) (nodes i) (hstrict j i hji) (by
          simpa only [state] using heq.symm)
  have hcard := Fintype.card_le_of_injective state hinjective
  simpa only [Fintype.card_fin, Fintype.card_prod,
    card_stateAtBound.{u}] using hcard

/-- **The bounded-width literal-shore descent.**  A graph-backed least Tait
counterexample carrying a reduced binary tree of the certified literal shores
above is bounded by the exact normalized state count.  The abstract
replacement premise has disappeared: a repeated state is contradicted by the
physical majority-shore splice. -/
theorem vertexCount_le_of_literalShoreTree
    (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (k w : Nat)
    (tree : DecompTree (LiteralShoreNode rotation k w))
    (hstrict : StrictLiteralShoreTree tree)
    (hvertices : Fintype.card V ≤ 2 * nodeCount tree) :
    Fintype.card V ≤
      2 * (2 ^ ((6 * w + 1) *
        (∑ j : Fin (k + 1),
          Nat.factorial (j : Nat) * 2 ^ (3 ^ (j : Nat)))) - 1) := by
  have hnorepeat : NoRepeatedStateOnDescents
      (fun node : LiteralShoreNode rotation k w => node.cardPhasedState) tree := by
    apply noRepeatedStateOnDescents_of_get
    intro p hpath i j hij heq
    have hproper : (p.get j).shore ⊂ (p.get i).shore :=
      hstrict p hpath i j hij
    exact cardPhasedState_ne_of_ssubset rotation minimal
      (p.get i) (p.get j) hproper heq
  have hbound := vertexCount_le hnorepeat 2 (Fintype.card V) hvertices
  rw [Fintype.card_prod, Fintype.card_fin,
    card_stateAtBound.{u} k] at hbound
  exact hbound

end

end GoertzelV24MajorityShoreStateDescent

end Mettapedia.GraphTheory.FourColor
