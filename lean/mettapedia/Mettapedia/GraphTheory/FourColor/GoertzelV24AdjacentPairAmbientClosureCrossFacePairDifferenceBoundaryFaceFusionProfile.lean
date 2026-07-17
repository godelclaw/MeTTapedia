import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionRebase

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceOrbitIncidence
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WalkCycleParity
open GoertzelV24WalkFaceCut
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

/-- The finite set of retained edges used by both complementary port
walks. -/
def commonRetainedEdgeFinset
    (data : AdjacentPairData G)
    (prefixTrail : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (suffixTrail : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3)) :
    Finset (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet :=
  Finset.univ.filter fun edge =>
    edge.1 ∈ prefixTrail.edges ∧ edge.1 ∈ suffixTrail.edges

@[simp] theorem mem_commonRetainedEdgeFinset_iff
    (data : AdjacentPairData G)
    (prefixTrail : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (suffixTrail : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    edge ∈ commonRetainedEdgeFinset data prefixTrail suffixTrail ↔
      edge.1 ∈ prefixTrail.edges ∧ edge.1 ∈ suffixTrail.edges := by
  rw [commonRetainedEdgeFinset, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ edge)

/-- The common retained-edge finset exactly represents the intersection
of the two raw retained edge lists. -/
theorem mem_both_retainedTrail_edges_iff_exists_commonRetainedEdge
    (data : AdjacentPairData G)
    (prefixTrail : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (suffixTrail : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (edge : Sym2 (retainedVertexSet data.firstVertex data.secondVertex)) :
    edge ∈ prefixTrail.edges ∧ edge ∈ suffixTrail.edges ↔
      ∃ shared ∈ commonRetainedEdgeFinset data prefixTrail suffixTrail,
        edge = shared.1 := by
  constructor
  · intro hboth
    let shared : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet :=
      ⟨edge, prefixTrail.edges_subset_edgeSet hboth.1⟩
    exact ⟨shared,
      (mem_commonRetainedEdgeFinset_iff data prefixTrail suffixTrail
        shared).2 hboth, rfl⟩
  · rintro ⟨shared, hshared, rfl⟩
    exact (mem_commonRetainedEdgeFinset_iff data prefixTrail suffixTrail
      shared).1 hshared

/-- Inclusion into the ambient graph carries the finite retained
intersection exactly to the corresponding ambient edges. -/
theorem mem_both_retainedWalkToAmbient_edges_iff_exists_commonRetainedEdge
    (data : AdjacentPairData G)
    (prefixTrail : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (suffixTrail : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (edge : Sym2 V) :
    edge ∈ (data.retainedWalkToAmbient prefixTrail).edges ∧
        edge ∈ (data.retainedWalkToAmbient suffixTrail).edges ↔
      ∃ shared ∈ commonRetainedEdgeFinset data prefixTrail suffixTrail,
        edge = (retainedEdgeToAmbientEdge data shared).1 := by
  constructor
  · rintro ⟨hprefix, hsuffix⟩
    rw [GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedWalkToAmbient,
      SimpleGraph.Walk.edges_map] at hprefix hsuffix
    rcases List.mem_map.mp hprefix with
      ⟨prefixSource, hprefixSource, hprefixValue⟩
    rcases List.mem_map.mp hsuffix with
      ⟨suffixSource, hsuffixSource, hsuffixValue⟩
    have hsources : prefixSource = suffixSource :=
      Sym2.map.injective Subtype.val_injective
        (hprefixValue.trans hsuffixValue.symm)
    subst suffixSource
    let shared : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet :=
      ⟨prefixSource, prefixTrail.edges_subset_edgeSet hprefixSource⟩
    refine ⟨shared, ?_, ?_⟩
    · exact (mem_commonRetainedEdgeFinset_iff data prefixTrail suffixTrail
        shared).2 ⟨hprefixSource, hsuffixSource⟩
    · rw [retainedEdgeToAmbientEdge_val]
      exact hprefixValue.symm
  · rintro ⟨shared, hshared, rfl⟩
    have hboth := (mem_commonRetainedEdgeFinset_iff data
      prefixTrail suffixTrail shared).1 hshared
    exact ⟨
      (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
        data prefixTrail shared).2 hboth.1,
      (retainedEdgeToAmbientEdge_mem_retainedWalkToAmbient_edges_iff
        data suffixTrail shared).2 hboth.2⟩

/-- Closing complementary retained walks adds the central edge to their
finite common retained-edge profile and adds no other common edge. -/
theorem mem_both_oppositePortClosures_iff_exists_commonRetainedEdge
    (data : AdjacentPairData G)
    (prefixTrail : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (suffixTrail : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (edge : Sym2 V) :
    edge ∈ (data.oppositePortClosure prefixTrail).edges ∧
        edge ∈ (data.alternateOppositePortClosure suffixTrail).edges ↔
      (∃ shared ∈ commonRetainedEdgeFinset data prefixTrail suffixTrail,
        edge = (retainedEdgeToAmbientEdge data shared).1) ∨
      edge = centralEdgeValue data := by
  constructor
  · rintro ⟨hprefixClosure, hsuffixClosure⟩
    change edge ∈ ((data.retainedWalkToAmbient prefixTrail).append
      data.oppositePortCentralReturn).edges at hprefixClosure
    change edge ∈ ((data.retainedWalkToAmbient suffixTrail).append
      data.alternateOppositePortCentralReturnRetained).edges at hsuffixClosure
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at hprefixClosure hsuffixClosure
    rcases hprefixClosure with hprefix | hreturn
    · rcases hsuffixClosure with hsuffix | haltReturn
      · exact Or.inl
          ((mem_both_retainedWalkToAmbient_edges_iff_exists_commonRetainedEdge
            data prefixTrail suffixTrail edge).1 ⟨hprefix, hsuffix⟩)
      · rw [data.alternateOppositePortCentralReturnRetained_edges] at haltReturn
        have hdisjoint :=
          data.retainedWalkToAmbient_edges_disjoint_alternateOppositePortCentralReturn
            prefixTrail
        rw [List.disjoint_left] at hdisjoint
        exact False.elim (hdisjoint hprefix haltReturn)
    · rcases hsuffixClosure with hsuffix | haltReturn
      · have hdisjoint :=
          data.retainedWalkToAmbient_edges_disjoint_oppositePortCentralReturn
            suffixTrail
        rw [List.disjoint_left] at hdisjoint
        exact False.elim (hdisjoint hsuffix hreturn)
      · exact Or.inr
          ((data.mem_oppositePortCentralReturns_iff_eq_centralEdgeValue
            edge).1 ⟨hreturn, haltReturn⟩)
  · rintro (hshared | hcentral)
    · rcases hshared with ⟨shared, hshared, rfl⟩
      have hboth :=
        (mem_both_retainedWalkToAmbient_edges_iff_exists_commonRetainedEdge
          data prefixTrail suffixTrail
            (retainedEdgeToAmbientEdge data shared).1).2
          ⟨shared, hshared, rfl⟩
      constructor
      · change (retainedEdgeToAmbientEdge data shared).1 ∈
          ((data.retainedWalkToAmbient prefixTrail).append
            data.oppositePortCentralReturn).edges
        rw [SimpleGraph.Walk.edges_append, List.mem_append]
        exact Or.inl hboth.1
      · change (retainedEdgeToAmbientEdge data shared).1 ∈
          ((data.retainedWalkToAmbient suffixTrail).append
            data.alternateOppositePortCentralReturnRetained).edges
        rw [SimpleGraph.Walk.edges_append, List.mem_append]
        exact Or.inl hboth.2
    · subst edge
      exact ⟨data.centralEdgeValue_mem_oppositePortClosure_edges prefixTrail,
        data.centralEdgeValue_mem_alternateOppositePortClosure_edges
          suffixTrail⟩

/-- Exact binary face cuts for two complementary port trails, with their
entire finite retained intersection left as an explicit profile. -/
structure RetainedIntersectionExactFaceCutPair
    (graphData : Data G) (data : AdjacentPairData G) where
  prefixTrail : (DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2)
  suffixTrail : (DeletedAdjacentPairGraph G data.firstVertex
    data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3)
  prefixLabels : OrbitFace graphData.toRotationSystem → F2
  suffixLabels : OrbitFace graphData.toRotationSystem → F2
  prefixTrail_isTrail : (data.oppositePortClosure prefixTrail).IsTrail
  suffixTrail_isTrail :
    (data.alternateOppositePortClosure suffixTrail).IsTrail
  prefixBoundary :
    orbitFaceBoundaryLinearMap graphData.toRotationSystem prefixLabels =
      walkEdgeParity (data.oppositePortClosure prefixTrail)
  suffixBoundary :
    orbitFaceBoundaryLinearMap graphData.toRotationSystem suffixLabels =
      walkEdgeParity (data.alternateOppositePortClosure suffixTrail)
  prefixExact : ∀ dart : graphData.toRotationSystem.D,
    prefixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
        prefixLabels (dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha dart)) ↔
      (graphData.toRotationSystem.edgeOf dart).1 ∈
        (data.oppositePortClosure prefixTrail).edges
  suffixExact : ∀ dart : graphData.toRotationSystem.D,
    suffixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
        suffixLabels (dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha dart)) ↔
      (graphData.toRotationSystem.edgeOf dart).1 ∈
        (data.alternateOppositePortClosure suffixTrail).edges

/-- The retained part of the simultaneous cut profile. -/
def RetainedIntersectionExactFaceCutPair.sharedEdges
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    Finset (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet :=
  commonRetainedEdgeFinset data pair.prefixTrail pair.suffixTrail

@[simp] theorem RetainedIntersectionExactFaceCutPair.mem_sharedEdges_iff
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (edge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) :
    edge ∈ pair.sharedEdges ↔
      edge.1 ∈ pair.prefixTrail.edges ∧
        edge.1 ∈ pair.suffixTrail.edges := by
  exact mem_commonRetainedEdgeFinset_iff data pair.prefixTrail
    pair.suffixTrail edge

/-- The paired face labels change together exactly on the mapped retained
profile together with the restored central edge. -/
theorem RetainedIntersectionExactFaceCutPair.jointExact
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (dart : graphData.toRotationSystem.D) :
    (pair.prefixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
          pair.prefixLabels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ∧
      pair.suffixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
          pair.suffixLabels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart))) ↔
      (∃ shared ∈ pair.sharedEdges,
        (graphData.toRotationSystem.edgeOf dart).1 =
          (retainedEdgeToAmbientEdge data shared).1) ∨
      (graphData.toRotationSystem.edgeOf dart).1 =
        centralEdgeValue data := by
  rw [pair.prefixExact dart, pair.suffixExact dart]
  exact mem_both_oppositePortClosures_iff_exists_commonRetainedEdge
    data pair.prefixTrail pair.suffixTrail
      (graphData.toRotationSystem.edgeOf dart).1

/-- Minimality supplies the exact finite-intersection face-cut profile for
any two complementary port trails. -/
theorem exists_retainedIntersectionExactFaceCutPair
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (prefixTrail : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (suffixTrail : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (hprefixTrail : (data.oppositePortClosure prefixTrail).IsTrail)
    (hsuffixTrail :
      (data.alternateOppositePortClosure suffixTrail).IsTrail) :
    ∃ pair : RetainedIntersectionExactFaceCutPair graphData data,
      pair.prefixTrail = prefixTrail ∧ pair.suffixTrail = suffixTrail := by
  rcases exists_exactOrbitFaceCutPair_of_minimal graphData minimal
      (data.oppositePortClosure prefixTrail)
      (data.alternateOppositePortClosure suffixTrail)
      hprefixTrail hsuffixTrail with
    ⟨prefixLabels, suffixLabels, hprefixBoundary, hsuffixBoundary,
      hprefixExact, hsuffixExact, _hjoint⟩
  exact ⟨{
    prefixTrail := prefixTrail
    suffixTrail := suffixTrail
    prefixLabels := prefixLabels
    suffixLabels := suffixLabels
    prefixTrail_isTrail := hprefixTrail
    suffixTrail_isTrail := hsuffixTrail
    prefixBoundary := hprefixBoundary
    suffixBoundary := hsuffixBoundary
    prefixExact := hprefixExact
    suffixExact := hsuffixExact }, rfl, rfl⟩

/-- The retained profile is empty exactly when its two trails are
edge-disjoint. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdges_eq_empty_iff
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    pair.sharedEdges = ∅ ↔
      pair.prefixTrail.edges.Disjoint pair.suffixTrail.edges := by
  constructor
  · intro hempty
    rw [List.disjoint_left]
    intro edge hprefix hsuffix
    let shared : (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).edgeSet :=
      ⟨edge, pair.prefixTrail.edges_subset_edgeSet hprefix⟩
    have hmem : shared ∈ pair.sharedEdges :=
      (pair.mem_sharedEdges_iff shared).2 ⟨hprefix, hsuffix⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty shared hmem
  · intro hdisjoint
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro edge hedge
    rw [List.disjoint_left] at hdisjoint
    have hboth := (pair.mem_sharedEdges_iff edge).1 hedge
    exact (hdisjoint hboth.1) hboth.2

/-- Every finite retained-intersection profile is empty, a singleton, or
has at least two edges. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdges_card_trichotomy
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    pair.sharedEdges = ∅ ∨
      (∃ edge, pair.sharedEdges = {edge}) ∨
      2 ≤ pair.sharedEdges.card := by
  by_cases hzero : pair.sharedEdges.card = 0
  · exact Or.inl (Finset.card_eq_zero.mp hzero)
  · by_cases hone : pair.sharedEdges.card = 1
    · exact Or.inr (Or.inl (Finset.card_eq_one.mp hone))
    · exact Or.inr (Or.inr (by omega))

/-- A singleton finite-intersection profile is precisely a cross-central
exact face-cut pair. -/
def RetainedIntersectionExactFaceCutPair.toCrossCentralExactFaceCutPair
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (hsingleton : pair.sharedEdges = {cross}) :
    CrossCentralExactFaceCutPair graphData data cross := by
  have hintersection : ∀ edge : Sym2
      (retainedVertexSet data.firstVertex data.secondVertex),
      edge ∈ pair.prefixTrail.edges ∧ edge ∈ pair.suffixTrail.edges ↔
        edge = cross.1 := by
    intro edge
    constructor
    · intro hboth
      let candidate : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).edgeSet :=
        ⟨edge, pair.prefixTrail.edges_subset_edgeSet hboth.1⟩
      have hcandidate : candidate ∈ pair.sharedEdges :=
        (pair.mem_sharedEdges_iff candidate).2 hboth
      have hcandidateEq : candidate = cross := by
        rw [hsingleton, Finset.mem_singleton] at hcandidate
        exact hcandidate
      exact congrArg Subtype.val hcandidateEq
    · intro hedge
      rw [hedge]
      have hcross : cross ∈ pair.sharedEdges := by
        rw [hsingleton]
        exact Finset.mem_singleton_self cross
      exact (pair.mem_sharedEdges_iff cross).1 hcross
  have hedgesDistinct : (retainedEdgeToAmbientEdge data cross).1 ≠
      centralEdgeValue data := by
    intro hedge
    exact retainedEdgeToAmbientEdge_ne_centralEdge data cross
      (Subtype.ext hedge)
  have hjointExact : ∀ dart : graphData.toRotationSystem.D,
      (pair.prefixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
            pair.prefixLabels (dartOrbitFace graphData.toRotationSystem
              (graphData.toRotationSystem.alpha dart)) ∧
        pair.suffixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
            pair.suffixLabels (dartOrbitFace graphData.toRotationSystem
              (graphData.toRotationSystem.alpha dart))) ↔
        (graphData.toRotationSystem.edgeOf dart).1 =
            (retainedEdgeToAmbientEdge data cross).1 ∨
          (graphData.toRotationSystem.edgeOf dart).1 =
            centralEdgeValue data := by
    intro dart
    rw [pair.jointExact dart]
    constructor
    · rintro (⟨shared, hshared, hedge⟩ | hcentral)
      · left
        have hsharedEq : shared = cross := by
          rw [hsingleton, Finset.mem_singleton] at hshared
          exact hshared
        simpa [hsharedEq] using hedge
      · exact Or.inr hcentral
    · rintro (hedge | hcentral)
      · left
        refine ⟨cross, ?_, hedge⟩
        rw [hsingleton]
        exact Finset.mem_singleton_self cross
      · exact Or.inr hcentral
  exact {
    prefixTrail := pair.prefixTrail
    suffixTrail := pair.suffixTrail
    prefixLabels := pair.prefixLabels
    suffixLabels := pair.suffixLabels
    prefixTrail_isTrail := pair.prefixTrail_isTrail
    suffixTrail_isTrail := pair.suffixTrail_isTrail
    prefixBoundary := pair.prefixBoundary
    suffixBoundary := pair.suffixBoundary
    prefixExact := pair.prefixExact
    suffixExact := pair.suffixExact
    retainedIntersectionExact := hintersection
    edgesDistinct := hedgesDistinct
    jointExact := hjointExact }

/-- The exact finite profile has the semantic trichotomy needed by
successive fusion: disjoint trails, a reusable singleton exact pair, or a
genuinely wider finite interface. -/
theorem RetainedIntersectionExactFaceCutPair.disjoint_or_singletonPair_or_two_le_card
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    pair.prefixTrail.edges.Disjoint pair.suffixTrail.edges ∨
      (∃ (cross : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).edgeSet)
          (_crossPair : CrossCentralExactFaceCutPair graphData data cross),
        pair.sharedEdges = {cross}) ∨
      2 ≤ pair.sharedEdges.card := by
  rcases pair.sharedEdges_card_trichotomy with hempty |
      ⟨cross, hsingleton⟩ | hmultiple
  · exact Or.inl (pair.sharedEdges_eq_empty_iff.mp hempty)
  · exact Or.inr (Or.inl ⟨cross,
      pair.toCrossCentralExactFaceCutPair cross hsingleton, hsingleton⟩)
  · exact Or.inr (Or.inr hmultiple)

/-- A profile has width at least two exactly when it contains two distinct
retained edges. -/
theorem RetainedIntersectionExactFaceCutPair.two_le_card_iff_exists_distinct
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data) :
    2 ≤ pair.sharedEdges.card ↔
      ∃ left right,
        left ∈ pair.sharedEdges ∧ right ∈ pair.sharedEdges ∧
          left ≠ right := by
  constructor
  · intro htwo
    exact Finset.one_lt_card_iff.mp (by omega)
  · rintro ⟨left, right, hleft, hright, hne⟩
    have hone : 1 < pair.sharedEdges.card :=
      Finset.one_lt_card_iff.mpr ⟨left, right, hleft, hright, hne⟩
    omega

/-- If every shared retained edge lies on one ambient face, injectivity of
the retained embedding bounds the profile width by that face boundary. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdges_card_le_faceBoundary_card
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (face : OrbitFace graphData.toRotationSystem)
    (hface : ∀ edge ∈ pair.sharedEdges,
      retainedEdgeToAmbientEdge data edge ∈
        orbitFaceBoundary graphData.toRotationSystem face) :
    pair.sharedEdges.card ≤
      (orbitFaceBoundary graphData.toRotationSystem face).card := by
  calc
    pair.sharedEdges.card =
        (pair.sharedEdges.image (retainedEdgeToAmbientEdge data)).card :=
      (Finset.card_image_of_injective pair.sharedEdges
        data.retainedEdgeToAmbientEdge_injective).symm
    _ ≤ (orbitFaceBoundary graphData.toRotationSystem face).card :=
      Finset.card_le_card (Finset.image_subset_iff.mpr hface)

/-- The successors of a remote-face fusion carry an exact finite profile,
and every edge in that profile is a new cross candidate on the remote
face. -/
theorem CrossCentralExactFaceCutPair.exists_localizedSuccessorIntersectionProfile
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (face : OrbitFace graphData.toRotationSystem)
    {firstRoot : V} (firstFusion : G.Walk firstRoot firstRoot)
    (hfirstSupport : ∀ edge : G.edgeSet,
      edge.1 ∈ firstFusion.edges →
        edge.1 ∈ (data.oppositePortClosure pair.prefixTrail).edges ∨
          edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    {secondRoot : V} (secondFusion : G.Walk secondRoot secondRoot)
    (hsecondSupport : ∀ edge : G.edgeSet,
      edge.1 ∈ secondFusion.edges →
        edge.1 ∈
            (data.alternateOppositePortClosure pair.suffixTrail).edges ∨
          edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    (prefixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2))
    (hprefixAvoids : cross.1 ∉ prefixSuccessor.edges)
    (hprefixCycle :
      (data.oppositePortClosure prefixSuccessor).IsCycle)
    (hprefixSubset : (data.retainedWalkToAmbient prefixSuccessor).edges ⊆
      firstFusion.edges)
    (suffixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3))
    (hsuffixCycle :
      (data.alternateOppositePortClosure suffixSuccessor).IsCycle)
    (hsuffixSubset : (data.retainedWalkToAmbient suffixSuccessor).edges ⊆
      secondFusion.edges) :
    ∃ successorPair : RetainedIntersectionExactFaceCutPair graphData data,
      successorPair.prefixTrail = prefixSuccessor ∧
        successorPair.suffixTrail = suffixSuccessor ∧
        (∀ edge ∈ successorPair.sharedEdges,
          edge ≠ cross ∧
            retainedEdgeToAmbientEdge data edge ∈
              orbitFaceBoundary graphData.toRotationSystem face) ∧
        successorPair.sharedEdges.card ≤
          (orbitFaceBoundary graphData.toRotationSystem face).card := by
  rcases exists_retainedIntersectionExactFaceCutPair graphData minimal data
      prefixSuccessor suffixSuccessor hprefixCycle.isTrail
        hsuffixCycle.isTrail with
    ⟨successorPair, hprefixEq, hsuffixEq⟩
  have hlocalized : ∀ edge ∈ successorPair.sharedEdges,
      edge ≠ cross ∧
        retainedEdgeToAmbientEdge data edge ∈
          orbitFaceBoundary graphData.toRotationSystem face := by
    intro edge hedge
    have hboth := (successorPair.mem_sharedEdges_iff edge).1 hedge
    rw [hprefixEq, hsuffixEq] at hboth
    have hne : edge ≠ cross := by
      intro hedgeEq
      apply hprefixAvoids
      exact congrArg Subtype.val hedgeEq ▸ hboth.1
    refine ⟨hne, ?_⟩
    exact pair.successorIntersection_mem_remoteFace face
      firstFusion hfirstSupport secondFusion hsecondSupport
        prefixSuccessor hprefixAvoids hprefixSubset suffixSuccessor
        hsuffixSubset edge hboth.1 hboth.2
  refine ⟨successorPair, hprefixEq, hsuffixEq, hlocalized, ?_⟩
  exact successorPair.sharedEdges_card_le_faceBoundary_card face
    (fun edge hedge => (hlocalized edge hedge).2)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
