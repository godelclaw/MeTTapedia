import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileAlignedChain

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- An aligned localized profile has at least two shared ranks. -/
theorem LocalizedAlignedSharedEdgeProfile.two_le_order_length
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face) :
    2 ≤ pair.prefixSharedEdgeOrder.length := by
  rw [pair.prefixSharedEdgeOrder_length_eq_sharedEdges_card]
  exact profile.two_le_card

/-- The first shared rank of a nontrivial aligned profile. -/
def LocalizedAlignedSharedEdgeProfile.firstRank
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face) :
    Fin pair.prefixSharedEdgeOrder.length :=
  ⟨0, by
    have htwo := profile.two_le_order_length
    omega⟩

/-- The last shared rank of a nontrivial aligned profile. -/
def LocalizedAlignedSharedEdgeProfile.lastRank
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face) :
    Fin pair.prefixSharedEdgeOrder.length :=
  ⟨pair.prefixSharedEdgeOrder.length - 1, by
    have htwo := profile.two_le_order_length
    omega⟩

@[simp] theorem LocalizedAlignedSharedEdgeProfile.firstRank_val
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face) :
    profile.firstRank.val = 0 :=
  rfl

@[simp] theorem LocalizedAlignedSharedEdgeProfile.lastRank_val
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face) :
    profile.lastRank.val = pair.prefixSharedEdgeOrder.length - 1 :=
  rfl

/-- Every shared rank in a common-run chain occurs at its rank offset from
the first raw prefix-trail position. Thus the whole shared word is one
contiguous affine block, not merely pairwise consecutive. -/
theorem LocalizedAlignedCommonRunChain.prefix_positions_affine
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (chain : LocalizedAlignedCommonRunChain profile)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    (pair.prefixSharedEdgePositionEmbedding position).val =
      (pair.prefixSharedEdgePositionEmbedding profile.firstRank).val +
        position.val := by
  have hstep : ∀ (n : Nat)
      (hn : n + 1 < pair.prefixSharedEdgeOrder.length),
      (pair.prefixSharedEdgePositionEmbedding
          (⟨n + 1, hn⟩ : Fin pair.prefixSharedEdgeOrder.length)).val =
        (pair.prefixSharedEdgePositionEmbedding
          (⟨n, by omega⟩ : Fin pair.prefixSharedEdgeOrder.length)).val + 1 := by
    intro n hn
    let rank : Fin (pair.prefixSharedEdgeOrder.length - 1) :=
      ⟨n, by omega⟩
    simpa only [rank, RetainedIntersectionExactFaceCutPair.alignedLinkFirst,
      RetainedIntersectionExactFaceCutPair.alignedLinkSecond] using
        chain.prefix_positions_consecutive rank
  have hind : ∀ (n : Nat)
      (hn : n < pair.prefixSharedEdgeOrder.length),
      (pair.prefixSharedEdgePositionEmbedding
          (⟨n, hn⟩ : Fin pair.prefixSharedEdgeOrder.length)).val =
        (pair.prefixSharedEdgePositionEmbedding profile.firstRank).val + n := by
    intro n
    induction n with
    | zero =>
        intro hn
        rfl
    | succ n inductionHypothesis =>
        intro hn
        rw [hstep n hn, inductionHypothesis (by omega)]
        omega
  exact hind position.val position.isLt

/-- The suffix occurrences form the same affine contiguous block in the
same rank order. -/
theorem LocalizedAlignedCommonRunChain.suffix_positions_affine
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (chain : LocalizedAlignedCommonRunChain profile)
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv position)).val =
      (pair.suffixSharedEdgePositionEmbedding
        (pair.sharedEdgeOrderEquiv profile.firstRank)).val + position.val := by
  have hstep : ∀ (n : Nat)
      (hn : n + 1 < pair.prefixSharedEdgeOrder.length),
      (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv
            (⟨n + 1, hn⟩ : Fin pair.prefixSharedEdgeOrder.length))).val =
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv
            (⟨n, by omega⟩ : Fin pair.prefixSharedEdgeOrder.length))).val + 1 := by
    intro n hn
    let rank : Fin (pair.prefixSharedEdgeOrder.length - 1) :=
      ⟨n, by omega⟩
    simpa only [rank, RetainedIntersectionExactFaceCutPair.alignedLinkFirst,
      RetainedIntersectionExactFaceCutPair.alignedLinkSecond] using
        chain.suffix_positions_consecutive rank
  have hind : ∀ (n : Nat)
      (hn : n < pair.prefixSharedEdgeOrder.length),
      (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv
            (⟨n, hn⟩ : Fin pair.prefixSharedEdgeOrder.length))).val =
        (pair.suffixSharedEdgePositionEmbedding
          (pair.sharedEdgeOrderEquiv profile.firstRank)).val + n := by
    intro n
    induction n with
    | zero =>
        intro hn
        rfl
    | succ n inductionHypothesis =>
        intro hn
        rw [hstep n hn, inductionHypothesis (by omega)]
        omega
  exact hind position.val position.isLt

/-- The endpoint ranks of a nontrivial aligned profile are distinct. -/
theorem LocalizedAlignedSharedEdgeProfile.firstRank_lt_lastRank
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face) :
    profile.firstRank < profile.lastRank := by
  change 0 < pair.prefixSharedEdgeOrder.length - 1
  have htwo := profile.two_le_order_length
  omega

/-- The actual prefix subwalk occupied by the complete common-run word. -/
def LocalizedAlignedCommonRunChain.prefixCommonRun
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (_chain : LocalizedAlignedCommonRunChain profile) :=
  pair.prefixSharedEdgeInterval profile.firstRank profile.lastRank
    profile.firstRank_lt_lastRank.le

/-- The actual suffix subwalk occupied by the same common-run word. -/
def LocalizedAlignedCommonRunChain.suffixCommonRun
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (_chain : LocalizedAlignedCommonRunChain profile) :=
  pair.suffixTrail.edgeInterval
    (pair.suffixSharedEdgePositionEmbedding
      (pair.sharedEdgeOrderEquiv profile.firstRank))
    (pair.suffixSharedEdgePositionEmbedding
      (pair.sharedEdgeOrderEquiv profile.lastRank))
    ((pair.suffixSharedEdgePositionEmbedding.le_iff_le).2
      (profile.sharedEdgeOrderEquiv_lt
        profile.firstRank_lt_lastRank).le)

/-- The prefix common-run subwalk has exactly the profile width. -/
@[simp] theorem LocalizedAlignedCommonRunChain.prefixCommonRun_length
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (chain : LocalizedAlignedCommonRunChain profile) :
    chain.prefixCommonRun.length =
      pair.prefixSharedEdgeOrder.length := by
  rw [LocalizedAlignedCommonRunChain.prefixCommonRun,
    RetainedIntersectionExactFaceCutPair.prefixSharedEdgeInterval,
    SimpleGraph.Walk.edgeInterval_length,
    chain.prefix_positions_affine profile.lastRank]
  simp only [LocalizedAlignedSharedEdgeProfile.lastRank_val]
  have htwo := profile.two_le_order_length
  omega

/-- The suffix common-run subwalk has the same exact width. -/
@[simp] theorem LocalizedAlignedCommonRunChain.suffixCommonRun_length
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (chain : LocalizedAlignedCommonRunChain profile) :
    chain.suffixCommonRun.length =
      pair.prefixSharedEdgeOrder.length := by
  rw [LocalizedAlignedCommonRunChain.suffixCommonRun,
    SimpleGraph.Walk.edgeInterval_length,
    chain.suffix_positions_affine profile.lastRank]
  simp only [LocalizedAlignedSharedEdgeProfile.lastRank_val]
  have htwo := profile.two_le_order_length
  omega

/-- The prefix common-run subwalk traverses literally the complete ordered
shared-edge word, with no intervening edge. -/
theorem LocalizedAlignedCommonRunChain.prefixCommonRun_edges
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (chain : LocalizedAlignedCommonRunChain profile) :
    chain.prefixCommonRun.edges = pair.prefixSharedEdgeOrder := by
  apply List.ext_getElem
  · simp only [SimpleGraph.Walk.length_edges,
      chain.prefixCommonRun_length]
  · intro index hrun hword
    let position : Fin pair.prefixSharedEdgeOrder.length :=
      ⟨index, hword⟩
    have hposition := chain.prefix_positions_affine position
    have hedge :=
      pair.prefixSharedEdgePositionEmbedding_preserves_edge position
    simp only [LocalizedAlignedCommonRunChain.prefixCommonRun,
      RetainedIntersectionExactFaceCutPair.prefixSharedEdgeInterval,
      SimpleGraph.Walk.edgeInterval_edges, List.getElem_take,
      List.getElem_drop]
    simpa only [position, List.get_eq_getElem, hposition] using hedge.symm

/-- The suffix common-run subwalk traverses the same ordered shared-edge
word, again with no intervening edge. -/
theorem LocalizedAlignedCommonRunChain.suffixCommonRun_edges
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (chain : LocalizedAlignedCommonRunChain profile) :
    chain.suffixCommonRun.edges = pair.prefixSharedEdgeOrder := by
  apply List.ext_getElem
  · simp only [SimpleGraph.Walk.length_edges,
      chain.suffixCommonRun_length]
  · intro index hrun hword
    let position : Fin pair.prefixSharedEdgeOrder.length :=
      ⟨index, hword⟩
    have hposition := chain.suffix_positions_affine position
    have hedge :
        pair.suffixTrail.edges.get
            (pair.suffixSharedEdgePositionEmbedding
              (pair.sharedEdgeOrderEquiv position)) =
          pair.prefixSharedEdgeOrder.get position := by
      calc
        pair.suffixTrail.edges.get
              (pair.suffixSharedEdgePositionEmbedding
                (pair.sharedEdgeOrderEquiv position)) =
            pair.prefixTrail.edges.get
              (pair.prefixSharedEdgePositionEmbedding position) :=
          (pair.trailEdges_get_sharedPositions_eq position).symm
        _ = pair.prefixSharedEdgeOrder.get position :=
          (pair.prefixSharedEdgePositionEmbedding_preserves_edge
            position).symm
    simp only [LocalizedAlignedCommonRunChain.suffixCommonRun,
      SimpleGraph.Walk.edgeInterval_edges, List.getElem_take,
      List.getElem_drop]
    simpa only [position, List.get_eq_getElem, hposition] using hedge

/-- The two successor trails therefore contain one literal common edge
trunk in the same order. -/
theorem LocalizedAlignedCommonRunChain.commonRun_edges_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (chain : LocalizedAlignedCommonRunChain profile) :
    chain.prefixCommonRun.edges = chain.suffixCommonRun.edges := by
  rw [chain.prefixCommonRun_edges, chain.suffixCommonRun_edges]

/-- The prefix common trunk inherits edge simplicity from its successor
trail. -/
theorem LocalizedAlignedCommonRunChain.prefixCommonRun_isTrail
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (chain : LocalizedAlignedCommonRunChain profile) :
    chain.prefixCommonRun.IsTrail := by
  rw [LocalizedAlignedCommonRunChain.prefixCommonRun]
  exact pair.prefixSharedEdgeInterval_isTrail _ _ _

/-- The suffix copy of the common trunk is edge-simple as well. -/
theorem LocalizedAlignedCommonRunChain.suffixCommonRun_isTrail
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (chain : LocalizedAlignedCommonRunChain profile) :
    chain.suffixCommonRun.IsTrail := by
  rw [LocalizedAlignedCommonRunChain.suffixCommonRun]
  exact pair.suffixRetained_isTrail.edgeInterval _ _ _

/-- The terminal aligned geometry as one explicit merge--split trunk:
both simple successor subwalks traverse the same width-at-least-two edge
word, whose distinct boundary edges lie on the designated remote face and
whose traversal darts agree at both ends. -/
structure LocalizedAlignedCommonRunTrunk
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face) where
  chain : LocalizedAlignedCommonRunChain profile
  two_le_length : 2 ≤ chain.prefixCommonRun.length
  prefix_isTrail : chain.prefixCommonRun.IsTrail
  suffix_isTrail : chain.suffixCommonRun.IsTrail
  prefix_edges :
    chain.prefixCommonRun.edges = pair.prefixSharedEdgeOrder
  suffix_edges :
    chain.suffixCommonRun.edges = pair.prefixSharedEdgeOrder
  first_edge_ne_last :
    pair.sharedEdgeAt profile.firstRank ≠
      pair.sharedEdgeAt profile.lastRank
  first_edge_ne_oldCross :
    pair.sharedEdgeAt profile.firstRank ≠ oldCross
  last_edge_ne_oldCross :
    pair.sharedEdgeAt profile.lastRank ≠ oldCross
  first_edge_mem_face :
    retainedEdgeToAmbientEdge data
        (pair.sharedEdgeAt profile.firstRank) ∈
      orbitFaceBoundary graphData.toRotationSystem face
  last_edge_mem_face :
    retainedEdgeToAmbientEdge data
        (pair.sharedEdgeAt profile.lastRank) ∈
      orbitFaceBoundary graphData.toRotationSystem face
  first_darts_eq :
    pair.suffixSharedEdgeDart profile.firstRank =
      pair.prefixSharedEdgeDart profile.firstRank
  last_darts_eq :
    pair.suffixSharedEdgeDart profile.lastRank =
      pair.prefixSharedEdgeDart profile.lastRank

/-- Every common-run chain canonically supplies its complete trunk
certificate. -/
def LocalizedAlignedCommonRunChain.toCommonRunTrunk
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (chain : LocalizedAlignedCommonRunChain profile) :
    LocalizedAlignedCommonRunTrunk profile := by
  have hfirstLocalized := profile.localized
    (pair.sharedEdgeAt profile.firstRank)
    (pair.sharedEdgeAt_mem_sharedEdges profile.firstRank)
  have hlastLocalized := profile.localized
    (pair.sharedEdgeAt profile.lastRank)
    (pair.sharedEdgeAt_mem_sharedEdges profile.lastRank)
  exact {
    chain := chain
    two_le_length := by
      rw [chain.prefixCommonRun_length]
      exact profile.two_le_order_length
    prefix_isTrail := chain.prefixCommonRun_isTrail
    suffix_isTrail := chain.suffixCommonRun_isTrail
    prefix_edges := chain.prefixCommonRun_edges
    suffix_edges := chain.suffixCommonRun_edges
    first_edge_ne_last :=
      pair.sharedEdgeAt_injective.ne profile.firstRank_lt_lastRank.ne
    first_edge_ne_oldCross := hfirstLocalized.1
    last_edge_ne_oldCross := hlastLocalized.1
    first_edge_mem_face := hfirstLocalized.2
    last_edge_mem_face := hlastLocalized.2
    first_darts_eq := profile.darts_eq profile.firstRank
    last_darts_eq := profile.darts_eq profile.lastRank }

/-- Upgrade a merely inhabited common-run branch to its explicit trunk
certificate. -/
theorem LocalizedAlignedCommonRunChain.nonempty_commonRunTrunk
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (chain : Nonempty (LocalizedAlignedCommonRunChain profile)) :
    Nonempty (LocalizedAlignedCommonRunTrunk profile) := by
  rcases chain with ⟨chain⟩
  exact ⟨chain.toCommonRunTrunk⟩

/-- The fusion-profile normal form with the degenerate aligned branch
strengthened from local empty gaps to one certified common trunk. -/
inductive LocalizedFusionChainTrunkResolution
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem) where
  | commonRunTrunk
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (trunk : Nonempty (LocalizedAlignedCommonRunTrunk profile))
  | alignedBubbleCycle
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (bubble : Nonempty (LocalizedAlignedBubblePrimalCycle profile))
  | strictlyShorterMixedPortCycles
      (descent : Nonempty
        (LocalizedStrictlyShorterMixedPortCycles pair oldCross face))
  | orderInversionPrimalCycle
      (descent : Nonempty
        (LocalizedOrderInversionPrimalCycle pair oldCross face))

/-- Strengthen every prior fusion-chain resolution to the exact common
trunk normal form. -/
theorem LocalizedFusionChainProfileResolution.nonempty_trunkResolution
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (resolution : LocalizedFusionChainProfileResolution pair oldCross face) :
    Nonempty (LocalizedFusionChainTrunkResolution pair oldCross face) := by
  cases resolution with
  | commonRunChain profile chain =>
      exact ⟨LocalizedFusionChainTrunkResolution.commonRunTrunk profile
        (LocalizedAlignedCommonRunChain.nonempty_commonRunTrunk chain)⟩
  | alignedBubbleCycle profile bubble =>
      exact ⟨LocalizedFusionChainTrunkResolution.alignedBubbleCycle
        profile bubble⟩
  | strictlyShorterMixedPortCycles descent =>
      exact ⟨
        LocalizedFusionChainTrunkResolution.strictlyShorterMixedPortCycles
          descent⟩
  | orderInversionPrimalCycle descent =>
      exact ⟨LocalizedFusionChainTrunkResolution.orderInversionPrimalCycle
        descent⟩

/-- A resolved successor profile exposes the strengthened common-trunk
normal form without any additional hypothesis. -/
theorem LocalizedSuccessorFusionChainProfile.nonempty_trunkResolution
    {graphData : Data G} {data : AdjacentPairData G}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {prefixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2)}
    {suffixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3)}
    (successor : LocalizedSuccessorFusionChainProfile oldCross face
      prefixSuccessor suffixSuccessor) :
    Nonempty (LocalizedFusionChainTrunkResolution successor.pair oldCross
      face) := by
  rcases successor.resolution with ⟨resolution⟩
  exact resolution.nonempty_trunkResolution

/-- The successor-pair trichotomy with its width-at-least-two branch
upgraded all the way to the common-trunk normal form. -/
def LocalizedFusionSuccessorResolution.TrunkOutcome
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {pair : CrossCentralExactFaceCutPair graphData data cross}
    {face : OrbitFace graphData.toRotationSystem}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    (successors : LocalizedFusionSuccessorResolution pair face
      firstFusion secondFusion) : Prop :=
    successors.prefixSuccessor.edges.Disjoint
        successors.suffixSuccessor.edges ∨
      (∃ (nextCross : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).edgeSet)
          (nextPair : CrossCentralExactFaceCutPair graphData data nextCross),
        nextCross ≠ cross ∧
          retainedEdgeToAmbientEdge data nextCross ∈
            orbitFaceBoundary graphData.toRotationSystem face ∧
          nextPair.prefixTrail = successors.prefixSuccessor ∧
          nextPair.suffixTrail = successors.suffixSuccessor) ∨
      (∃ successor : LocalizedSuccessorFusionChainProfile cross face
          successors.prefixSuccessor successors.suffixSuccessor,
        Nonempty (LocalizedFusionChainTrunkResolution successor.pair cross
          face))

/-- Every resolved successor pair realizes its strengthened trunk
outcome. -/
theorem LocalizedFusionSuccessorResolution.finite_trunk_outcome
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {pair : CrossCentralExactFaceCutPair graphData data cross}
    {face : OrbitFace graphData.toRotationSystem}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    (successors : LocalizedFusionSuccessorResolution pair face
      firstFusion secondFusion) :
    successors.TrunkOutcome := by
  unfold LocalizedFusionSuccessorResolution.TrunkOutcome
  rcases successors.finite_outcome with hdisjoint | hrebase | hprofile
  · exact Or.inl hdisjoint
  · exact Or.inr (Or.inl hrebase)
  · rcases hprofile with ⟨successor⟩
    exact Or.inr (Or.inr
      ⟨successor, successor.nonempty_trunkResolution⟩)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
