import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Data.List.Duplicate
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainClosedMonodromy

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SimpleGraph

/-- A walk equipped with the edge-nonrepetition property. In a finite graph
this is a finite type because its length is bounded by the edge count. -/
def FiniteTrailWalk {W : Type*} (H : SimpleGraph W) (u v : W) :=
  {walk : H.Walk u v // walk.IsTrail}

variable {W : Type*} [Fintype W] [DecidableEq W]
  (H : SimpleGraph W) [DecidableRel H.Adj]

/-- Embed a trail walk into the finite set of walks shorter than one plus
the graph's edge count. -/
def finiteTrailWalkEmbedding (u v : W) :
    FiniteTrailWalk H u v →
      {walk : H.Walk u v // walk.length < H.edgeFinset.card + 1} :=
  fun walk =>
    ⟨walk.1, Nat.lt_succ_of_le walk.2.length_le_card_edgeFinset⟩

instance finiteFiniteTrailWalk (u v : W) :
    Finite (FiniteTrailWalk H u v) :=
  Finite.of_injective (finiteTrailWalkEmbedding H u v) (by
    intro first second heq
    have hwalk := congrArg
      (fun encoded : {walk : H.Walk u v //
        walk.length < H.edgeFinset.card + 1} => encoded.1) heq
    exact Subtype.ext hwalk)

noncomputable instance fintypeFiniteTrailWalk (u v : W) :
    Fintype (FiniteTrailWalk H u v) :=
  Fintype.ofFinite _

end SimpleGraph

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- Exactness of the closed prefix cut makes its retained part a trail. -/
theorem CrossCentralExactFaceCutPair.prefixRetained_isTrail
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    pair.prefixTrail.IsTrail := by
  rw [SimpleGraph.Walk.isTrail_def]
  have hclosure := pair.prefixTrail_isTrail.edges_nodup
  change (((data.retainedWalkToAmbient pair.prefixTrail).append
    data.oppositePortCentralReturn).edges).Nodup at hclosure
  rw [SimpleGraph.Walk.edges_append] at hclosure
  have hambient :
      (data.retainedWalkToAmbient pair.prefixTrail).edges.Nodup :=
    hclosure.of_append_left
  rw [GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedWalkToAmbient,
    SimpleGraph.Walk.edges_map] at hambient
  exact List.Nodup.of_map _ hambient

/-- Exactness of the closed suffix cut makes its retained part a trail. -/
theorem CrossCentralExactFaceCutPair.suffixRetained_isTrail
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    pair.suffixTrail.IsTrail := by
  rw [SimpleGraph.Walk.isTrail_def]
  have hclosure := pair.suffixTrail_isTrail.edges_nodup
  change (((data.retainedWalkToAmbient pair.suffixTrail).append
    data.alternateOppositePortCentralReturnRetained).edges).Nodup at hclosure
  rw [SimpleGraph.Walk.edges_append] at hclosure
  have hambient :
      (data.retainedWalkToAmbient pair.suffixTrail).edges.Nodup :=
    hclosure.of_append_left
  rw [GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedWalkToAmbient,
    SimpleGraph.Walk.edges_map] at hambient
  exact List.Nodup.of_map _ hambient

/-- The two trails and two face-label functions determine an exact-cut pair;
all remaining fields are propositions. -/
theorem CrossCentralExactFaceCutPair.ext_data
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (first second : CrossCentralExactFaceCutPair graphData data cross)
    (hprefixTrail : first.prefixTrail = second.prefixTrail)
    (hsuffixTrail : first.suffixTrail = second.suffixTrail)
    (hprefixLabels : first.prefixLabels = second.prefixLabels)
    (hsuffixLabels : first.suffixLabels = second.suffixLabels) :
    first = second := by
  cases first
  cases second
  simp_all

/-- Finite data code for an exact-cut pair at a fixed cross edge. -/
abbrev CrossCentralExactFaceCutFiniteCode
    (graphData : Data G) (data : AdjacentPairData G) :=
  SimpleGraph.FiniteTrailWalk
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
      (data.retainedPort 0) (data.retainedPort 2) ×
    SimpleGraph.FiniteTrailWalk
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex)
      (data.retainedPort 1) (data.retainedPort 3) ×
    (OrbitFace graphData.toRotationSystem → F2) ×
    (OrbitFace graphData.toRotationSystem → F2)

/-- Encode an exact-cut pair by its proof-relevant finite data. -/
def CrossCentralExactFaceCutPair.finiteCode
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    CrossCentralExactFaceCutFiniteCode graphData data :=
  (⟨pair.prefixTrail, pair.prefixRetained_isTrail⟩,
    ⟨pair.suffixTrail, pair.suffixRetained_isTrail⟩,
    pair.prefixLabels, pair.suffixLabels)

/-- The finite data code loses no exact-cut information. -/
theorem CrossCentralExactFaceCutPair.finiteCode_injective
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet} :
    Function.Injective
      (CrossCentralExactFaceCutPair.finiteCode
        (graphData := graphData) (data := data) (cross := cross)) := by
  intro first second hcode
  apply CrossCentralExactFaceCutPair.ext_data
  · exact congrArg
      (fun code : CrossCentralExactFaceCutFiniteCode graphData data =>
        code.1.1) hcode
  · exact congrArg
      (fun code : CrossCentralExactFaceCutFiniteCode graphData data =>
        code.2.1.1) hcode
  · exact congrArg
      (fun code : CrossCentralExactFaceCutFiniteCode graphData data =>
        code.2.2.1) hcode
  · exact congrArg
      (fun code : CrossCentralExactFaceCutFiniteCode graphData data =>
        code.2.2.2) hcode

instance finiteCrossCentralExactFaceCutPair
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet} :
    Finite (CrossCentralExactFaceCutPair graphData data cross) :=
  Finite.of_injective
    (CrossCentralExactFaceCutPair.finiteCode
      (graphData := graphData) (data := data) (cross := cross))
    CrossCentralExactFaceCutPair.finiteCode_injective

/-- A complete exact-rebase state consists of its retained cross edge and
the exact-cut pair certified at that edge. -/
abbrev CrossCentralExactFaceCutState
    (graphData : Data G) (data : AdjacentPairData G) :=
  Σ cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet,
    CrossCentralExactFaceCutPair graphData data cross

noncomputable instance fintypeCrossCentralExactFaceCutState
    (graphData : Data G) (data : AdjacentPairData G) :
    Fintype (CrossCentralExactFaceCutState graphData data) :=
  Fintype.ofFinite _

/-- Exact-rebase states whose cross lies on one fixed ambient face. -/
abbrev FaceSupportedCrossCentralExactFaceCutState
    (graphData : Data G) (data : AdjacentPairData G)
    (face : OrbitFace graphData.toRotationSystem) :=
  {state : CrossCentralExactFaceCutState graphData data //
    retainedEdgeToAmbientEdge data state.1 ∈
      orbitFaceBoundary graphData.toRotationSystem face}

noncomputable instance fintypeFaceSupportedCrossCentralExactFaceCutState
    (graphData : Data G) (data : AdjacentPairData G)
    (face : OrbitFace graphData.toRotationSystem) :
    Fintype (FaceSupportedCrossCentralExactFaceCutState
      graphData data face) :=
  Fintype.ofFinite _

/-- A complete transfer-channel state also records the supporting face.
This permits a rebase run to change its selected coordinate face while
remaining in one finite state space. -/
abbrev CrossCentralExactFaceCutChannelState
    (graphData : Data G) (data : AdjacentPairData G) :=
  Σ face : OrbitFace graphData.toRotationSystem,
    FaceSupportedCrossCentralExactFaceCutState graphData data face

noncomputable instance fintypeCrossCentralExactFaceCutChannelState
    (graphData : Data G) (data : AdjacentPairData G) :
    Fintype (CrossCentralExactFaceCutChannelState graphData data) :=
  Fintype.ofFinite _

/-- A list longer than the complete face-supported state space repeats a
full exact-cut state, including both trails and both label functions. -/
theorem faceSupportedExactRebaseStates_not_nodup_of_card_lt_length
    {graphData : Data G} {data : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    (states : List (FaceSupportedCrossCentralExactFaceCutState
      graphData data face))
    (hlength : Fintype.card
        (FaceSupportedCrossCentralExactFaceCutState graphData data face) <
      states.length) :
    ¬states.Nodup := by
  intro hnodup
  exact (Nat.not_lt_of_ge hnodup.length_le_card) hlength

/-- Pigeonhole form of finite exact-rebase pumping: a sufficiently long
face-supported run contains a duplicated certified state. -/
theorem exists_duplicate_faceSupportedExactRebaseState_of_card_lt_length
    {graphData : Data G} {data : AdjacentPairData G}
    {face : OrbitFace graphData.toRotationSystem}
    (states : List (FaceSupportedCrossCentralExactFaceCutState
      graphData data face))
    (hlength : Fintype.card
        (FaceSupportedCrossCentralExactFaceCutState graphData data face) <
      states.length) :
    ∃ state, List.Duplicate state states :=
  List.exists_duplicate_iff_not_nodup.mpr
    (faceSupportedExactRebaseStates_not_nodup_of_card_lt_length
      states hlength)

/-- A channel-state run longer than the full face-varying state space
repeats a face, cross, exact trail pair, and both label functions. -/
theorem exactRebaseChannelStates_not_nodup_of_card_lt_length
    {graphData : Data G} {data : AdjacentPairData G}
    (states : List (CrossCentralExactFaceCutChannelState graphData data))
    (hlength : Fintype.card
        (CrossCentralExactFaceCutChannelState graphData data) <
      states.length) :
    ¬states.Nodup := by
  intro hnodup
  exact (Nat.not_lt_of_ge hnodup.length_le_card) hlength

/-- Face-varying pumping form for exact-rebase channels. -/
theorem exists_duplicate_exactRebaseChannelState_of_card_lt_length
    {graphData : Data G} {data : AdjacentPairData G}
    (states : List (CrossCentralExactFaceCutChannelState graphData data))
    (hlength : Fintype.card
        (CrossCentralExactFaceCutChannelState graphData data) <
      states.length) :
    ∃ state, List.Duplicate state states :=
  List.exists_duplicate_iff_not_nodup.mpr
    (exactRebaseChannelStates_not_nodup_of_card_lt_length states hlength)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
