import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileOrderInversionCircuit

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24TwoEdgeCutMinimality
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

/-- Identity profile monodromy puts every physical shared edge at the same
rank in the suffix order. -/
theorem RetainedIntersectionExactFaceCutPair.sharedEdgeOrderEquiv_val_eq_self_of_sharedEdgeMonodromy_eq_refl
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hidentity : pair.sharedEdgeMonodromy =
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length))
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    (pair.sharedEdgeOrderEquiv position : Nat) = position := by
  have happly : pair.sharedEdgeMonodromy position = position :=
    congrArg
      (fun permutation : Equiv.Perm
          (Fin pair.prefixSharedEdgeOrder.length) ↦ permutation position)
      hidentity
  have hvalue := congrArg Fin.val happly
  rw [pair.sharedEdgeMonodromy_apply_val] at hvalue
  exact hvalue

/-- Consequently the two complete shared-edge words agree literally, not
merely up to permutation. -/
theorem RetainedIntersectionExactFaceCutPair.prefixSharedEdgeOrder_eq_suffixSharedEdgeOrder_of_sharedEdgeMonodromy_eq_refl
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hidentity : pair.sharedEdgeMonodromy =
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length)) :
    pair.prefixSharedEdgeOrder = pair.suffixSharedEdgeOrder := by
  apply List.ext_get pair.sharedEdgeOrders_length_eq
  intro index hprefix hsuffix
  let position : Fin pair.prefixSharedEdgeOrder.length :=
    ⟨index, hprefix⟩
  have hposition : pair.sharedEdgeOrderEquiv position =
      (⟨index, hsuffix⟩ : Fin pair.suffixSharedEdgeOrder.length) := by
    apply Fin.ext
    exact pair.sharedEdgeOrderEquiv_val_eq_self_of_sharedEdgeMonodromy_eq_refl
      hidentity position
  exact (pair.sharedEdgeOrderEquiv_preserves_edge position).symm.trans
    (congrArg (fun suffixPosition ↦
      pair.suffixSharedEdgeOrder.get suffixPosition) hposition)

/-- Identity signed monodromy also aligns the oriented dart at every shared
edge. -/
theorem RetainedIntersectionExactFaceCutPair.suffixSharedEdgeDart_eq_prefixSharedEdgeDart_of_sharedEdgeSignedMonodromy_eq_refl
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (hidentity : pair.sharedEdgeSignedMonodromy =
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool))
    (position : Fin pair.prefixSharedEdgeOrder.length) :
    pair.suffixSharedEdgeDart position =
      pair.prefixSharedEdgeDart position := by
  have hchirality :=
    ((pair.sharedEdgeSignedMonodromy_eq_refl_iff).1 hidentity).2 position
  exact (pair.sharedEdgeChirality_eq_true_iff position).1 hchirality

/-- The geometric content of the surviving identity branch: at least two
new edges on one remote face occur in the same order and orientation on the
two successor trails. -/
structure LocalizedAlignedSharedEdgeProfile
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem) where
  two_le_card : 2 ≤ pair.sharedEdges.card
  ordered_edges_eq :
    pair.prefixSharedEdgeOrder = pair.suffixSharedEdgeOrder
  darts_eq : ∀ position : Fin pair.prefixSharedEdgeOrder.length,
    pair.suffixSharedEdgeDart position =
      pair.prefixSharedEdgeDart position
  localized : ∀ edge ∈ pair.sharedEdges,
    edge ≠ oldCross ∧
      retainedEdgeToAmbientEdge data edge ∈
        orbitFaceBoundary graphData.toRotationSystem face

/-- Package a width-at-least-two identity profile as its explicit aligned
fusion-chain geometry. -/
theorem RetainedIntersectionExactFaceCutPair.nonempty_localizedAlignedSharedEdgeProfile_of_sharedEdgeSignedMonodromy_eq_refl
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem)
    (htwo : 2 ≤ pair.sharedEdges.card)
    (hlocalized : ∀ edge ∈ pair.sharedEdges,
      edge ≠ oldCross ∧
        retainedEdgeToAmbientEdge data edge ∈
          orbitFaceBoundary graphData.toRotationSystem face)
    (hidentity : pair.sharedEdgeSignedMonodromy =
      Equiv.refl (Fin pair.prefixSharedEdgeOrder.length × Bool)) :
    Nonempty (LocalizedAlignedSharedEdgeProfile pair oldCross face) := by
  have hunsigned :=
    ((pair.sharedEdgeSignedMonodromy_eq_refl_iff).1 hidentity).1
  exact ⟨{
    two_le_card := htwo
    ordered_edges_eq :=
      pair.prefixSharedEdgeOrder_eq_suffixSharedEdgeOrder_of_sharedEdgeMonodromy_eq_refl
        hunsigned
    darts_eq :=
      pair.suffixSharedEdgeDart_eq_prefixSharedEdgeDart_of_sharedEdgeSignedMonodromy_eq_refl
        hidentity
    localized := hlocalized }⟩

/-- A localized remote-face successor has an exact finite trichotomy. Its
profile is empty and the two successor paths are edge-disjoint; it is a
singleton and rebases the exact cross at a new edge of the same face; or it
has width at least two and carries the resolved signed-profile normal form. -/
theorem CrossCentralExactFaceCutPair.exists_localizedSuccessorResolvedProfileTrichotomy
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
    prefixSuccessor.edges.Disjoint suffixSuccessor.edges ∨
      (∃ (nextCross : (DeletedAdjacentPairGraph G data.firstVertex
            data.secondVertex).edgeSet)
          (nextPair : CrossCentralExactFaceCutPair graphData data nextCross),
        nextCross ≠ cross ∧
          retainedEdgeToAmbientEdge data nextCross ∈
            orbitFaceBoundary graphData.toRotationSystem face ∧
          nextPair.prefixTrail = prefixSuccessor ∧
          nextPair.suffixTrail = suffixSuccessor) ∨
      ∃ successorPair : RetainedIntersectionExactFaceCutPair graphData data,
        successorPair.prefixTrail = prefixSuccessor ∧
          successorPair.suffixTrail = suffixSuccessor ∧
          (∀ edge ∈ successorPair.sharedEdges,
            edge ≠ cross ∧
              retainedEdgeToAmbientEdge data edge ∈
                orbitFaceBoundary graphData.toRotationSystem face) ∧
          successorPair.sharedEdges.card ≤
            (orbitFaceBoundary graphData.toRotationSystem face).card ∧
          2 ≤ successorPair.sharedEdges.card ∧
          (Nonempty (LocalizedAlignedSharedEdgeProfile successorPair
              cross face) ∨
            Nonempty (LocalizedStrictlyShorterMixedPortCycles successorPair
              cross face) ∨
            Nonempty (LocalizedOrderInversionPrimalCycle successorPair
              cross face)) := by
  rcases pair.exists_localizedSuccessorResolvedSignedProfileNormalForm minimal
      face firstFusion hfirstSupport secondFusion hsecondSupport
      prefixSuccessor hprefixAvoids hprefixCycle hprefixSubset
      suffixSuccessor hsuffixCycle hsuffixSubset with
    ⟨successorPair, hprefixEq, hsuffixEq, hlocalized, hwidth,
      hnormal⟩
  rcases successorPair.sharedEdges_card_trichotomy with
    hempty | ⟨nextCross, hsingleton⟩ | htwo
  · exact Or.inl (by
      have hdisjoint :=
        (successorPair.sharedEdges_eq_empty_iff).1 hempty
      simpa only [hprefixEq, hsuffixEq] using hdisjoint)
  · right
    left
    have hnextMem : nextCross ∈ successorPair.sharedEdges := by
      rw [hsingleton]
      exact Finset.mem_singleton_self nextCross
    have hnextLocalized := hlocalized nextCross hnextMem
    let nextPair :=
      successorPair.toCrossCentralExactFaceCutPair nextCross hsingleton
    exact ⟨nextCross, nextPair, hnextLocalized.1, hnextLocalized.2,
      by
        change successorPair.prefixTrail = prefixSuccessor
        exact hprefixEq,
      by
        change successorPair.suffixTrail = suffixSuccessor
        exact hsuffixEq⟩
  · have hgeometric :
        Nonempty (LocalizedAlignedSharedEdgeProfile successorPair
            cross face) ∨
          Nonempty (LocalizedStrictlyShorterMixedPortCycles successorPair
            cross face) ∨
          Nonempty (LocalizedOrderInversionPrimalCycle successorPair
            cross face) := by
      rcases hnormal with hidentity | hmixed | hcycle
      · exact Or.inl
          (successorPair.nonempty_localizedAlignedSharedEdgeProfile_of_sharedEdgeSignedMonodromy_eq_refl
            cross face htwo hlocalized hidentity)
      · exact Or.inr (Or.inl hmixed)
      · exact Or.inr (Or.inr hcycle)
    exact Or.inr (Or.inr
      ⟨successorPair, hprefixEq, hsuffixEq, hlocalized, hwidth, htwo,
        hgeometric⟩)

/-- Resolving both remote-face fusion cycles now propagates all the way to
the finite profile trichotomy. Thus the only outcomes are a retained fusion
cycle, edge-disjoint successors, an exact rebase, or a width-at-least-two
resolved signed profile. -/
theorem CrossCentralExactFaceCutPair.fusionCyclePair_retainedCycle_or_resolvedSuccessorProfile
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross)
    (face : OrbitFace graphData.toRotationSystem)
    (hboundary : ∀ port : Fin 4, boundaryEdge data port ∉
      orbitFaceBoundary graphData.toRotationSystem face)
    {firstRoot : V} (firstFusion : G.Walk firstRoot firstRoot)
    (hfirstCycle : firstFusion.IsCycle)
    (hfirstCross : (retainedEdgeToAmbientEdge data cross).1 ∉
      firstFusion.edges)
    (hfirstSupport : ∀ edge : G.edgeSet,
      edge.1 ∈ firstFusion.edges →
        edge.1 ∈ (data.oppositePortClosure pair.prefixTrail).edges ∨
          edge ∈ orbitFaceBoundary graphData.toRotationSystem face)
    {secondRoot : V} (secondFusion : G.Walk secondRoot secondRoot)
    (hsecondCycle : secondFusion.IsCycle)
    (hsecondCross : (retainedEdgeToAmbientEdge data cross).1 ∉
      secondFusion.edges)
    (hsecondSupport : ∀ edge : G.edgeSet,
      edge.1 ∈ secondFusion.edges →
        edge.1 ∈
            (data.alternateOppositePortClosure pair.suffixTrail).edges ∨
          edge ∈ orbitFaceBoundary graphData.toRotationSystem face) :
    (∃ (hroot : firstRoot ∈
          retainedVertexSet data.firstVertex data.secondVertex)
        (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk ⟨firstRoot, hroot⟩ ⟨firstRoot, hroot⟩),
      retainedFusion.IsCycle ∧
        data.retainedWalkToAmbient retainedFusion = firstFusion) ∨
    (∃ (hroot : secondRoot ∈
          retainedVertexSet data.firstVertex data.secondVertex)
        (retainedFusion : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk ⟨secondRoot, hroot⟩ ⟨secondRoot, hroot⟩),
      retainedFusion.IsCycle ∧
        data.retainedWalkToAmbient retainedFusion = secondFusion) ∨
    ∃ (prefixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 0) (data.retainedPort 2))
        (suffixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.retainedPort 1) (data.retainedPort 3)),
      prefixSuccessor.IsPath ∧
        cross.1 ∉ prefixSuccessor.edges ∧
        (data.oppositePortClosure prefixSuccessor).IsCycle ∧
        (data.retainedWalkToAmbient prefixSuccessor).edges ⊆
          firstFusion.edges ∧
      suffixSuccessor.IsPath ∧
        cross.1 ∉ suffixSuccessor.edges ∧
        (data.alternateOppositePortClosure suffixSuccessor).IsCycle ∧
        (data.retainedWalkToAmbient suffixSuccessor).edges ⊆
          secondFusion.edges ∧
      (prefixSuccessor.edges.Disjoint suffixSuccessor.edges ∨
        (∃ (nextCross : (DeletedAdjacentPairGraph G data.firstVertex
              data.secondVertex).edgeSet)
            (nextPair : CrossCentralExactFaceCutPair graphData data nextCross),
          nextCross ≠ cross ∧
            retainedEdgeToAmbientEdge data nextCross ∈
              orbitFaceBoundary graphData.toRotationSystem face ∧
            nextPair.prefixTrail = prefixSuccessor ∧
            nextPair.suffixTrail = suffixSuccessor) ∨
        ∃ successorPair : RetainedIntersectionExactFaceCutPair graphData data,
          successorPair.prefixTrail = prefixSuccessor ∧
            successorPair.suffixTrail = suffixSuccessor ∧
            (∀ edge ∈ successorPair.sharedEdges,
              edge ≠ cross ∧
                retainedEdgeToAmbientEdge data edge ∈
                  orbitFaceBoundary graphData.toRotationSystem face) ∧
            successorPair.sharedEdges.card ≤
              (orbitFaceBoundary graphData.toRotationSystem face).card ∧
            2 ≤ successorPair.sharedEdges.card ∧
            (Nonempty (LocalizedAlignedSharedEdgeProfile successorPair
                cross face) ∨
              Nonempty
                (LocalizedStrictlyShorterMixedPortCycles successorPair
                  cross face) ∨
              Nonempty (LocalizedOrderInversionPrimalCycle successorPair
                cross face))) := by
  rcases pair.fusionCyclePair_retainedCycle_or_successorPair face hboundary
      firstFusion hfirstCycle hfirstCross hfirstSupport
      secondFusion hsecondCycle hsecondCross hsecondSupport with
    hfirstRetained | hsecondRetained |
      ⟨prefixSuccessor, suffixSuccessor,
        hprefixPath, hprefixAvoids, hprefixCycle, hprefixSubset,
        hsuffixPath, hsuffixAvoids, hsuffixCycle, hsuffixSubset, _⟩
  · exact Or.inl hfirstRetained
  · exact Or.inr (Or.inl hsecondRetained)
  · have hresolved :=
      pair.exists_localizedSuccessorResolvedProfileTrichotomy minimal face
        firstFusion hfirstSupport secondFusion hsecondSupport
        prefixSuccessor hprefixAvoids hprefixCycle hprefixSubset
        suffixSuccessor hsuffixCycle hsuffixSubset
    exact Or.inr (Or.inr
      ⟨prefixSuccessor, suffixSuccessor,
        hprefixPath, hprefixAvoids, hprefixCycle, hprefixSubset,
        hsuffixPath, hsuffixAvoids, hsuffixCycle, hsuffixSubset,
        hresolved⟩)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
