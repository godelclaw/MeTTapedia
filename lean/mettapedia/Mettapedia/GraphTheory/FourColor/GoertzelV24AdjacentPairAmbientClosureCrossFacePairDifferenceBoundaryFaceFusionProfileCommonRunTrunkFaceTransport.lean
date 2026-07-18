import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileCommonRunAmbientEndpointFaceTurns
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicFaceCutTrailTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionAmbientTrailFaceCutTransport

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Reversing a dart exchanges its two Boolean side coordinates. -/
theorem dartSideOrbitFace_alpha
    (RS : RotationSystem V E) (dart : RS.D) (side : Bool) :
    RS.dartSideOrbitFace (RS.alpha dart) side =
      RS.dartSideOrbitFace dart (!side) := by
  cases side <;> simp [dartSideOrbitFace, RS.alpha_involutive]

/-- On an incident two-sided face, reversing a dart complements the
canonical side coordinate. -/
theorem incidentFaceSide_alpha_eq_not
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (dart : RS.D) (face : OrbitFace RS)
    (hedge : RS.edgeOf dart ∈ orbitFaceBoundary RS face) :
    RS.incidentFaceSide (RS.alpha dart) face =
      !RS.incidentFaceSide dart face := by
  have hedgeAlpha : RS.edgeOf (RS.alpha dart) ∈
      orbitFaceBoundary RS face := by
    rw [RS.edge_alpha]
    exact hedge
  have hforward := RS.dartSideOrbitFace_incidentFaceSide_eq
    htwoSided dart face hedge
  have hreverse := RS.dartSideOrbitFace_incidentFaceSide_eq
    htwoSided (RS.alpha dart) face hedgeAlpha
  have hcoordinates :
      (!(RS.incidentFaceSide (RS.alpha dart) face)) =
        RS.incidentFaceSide dart face := by
    apply RS.dartSideOrbitFace_injective htwoSided dart
    rw [← RS.dartSideOrbitFace_alpha dart
        (RS.incidentFaceSide (RS.alpha dart) face),
      hreverse, hforward]
  have hnot := congrArg (fun side : Bool => !side) hcoordinates
  simpa using hnot

/-- Along two consecutive nonbacktracking darts whose edges lie on one
two-sided face, the face occupies the same oriented side of both darts. -/
theorem incidentFaceSide_eq_of_faceCutTrailStep
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    {first second : RS.D} {face : OrbitFace RS}
    (hstep : RS.FaceCutTrailStep first second)
    (hfirstEdge : RS.edgeOf first ∈ orbitFaceBoundary RS face)
    (hsecondEdge : RS.edgeOf second ∈ orbitFaceBoundary RS face) :
    RS.incidentFaceSide first face =
      RS.incidentFaceSide second face := by
  have hfirstFace := RS.dartSideOrbitFace_incidentFaceSide_eq
    htwoSided first face hfirstEdge
  have hsecondFace := RS.dartSideOrbitFace_incidentFaceSide_eq
    htwoSided second face hsecondEdge
  rcases RS.rho_eq_or_rho_eq_of_cubic hcubic hrotation
      hstep.1 hstep.2 with hforward | hreverse
  · cases hfirstSide : RS.incidentFaceSide first face with
    | false =>
        cases hsecondSide : RS.incidentFaceSide second face with
        | false => rfl
        | true =>
            exfalso
            simp [dartSideOrbitFace, hfirstSide] at hfirstFace
            simp [dartSideOrbitFace, hsecondSide] at hsecondFace
            have hcorner :=
              dartOrbitFace_alpha_eq_dartOrbitFace_rho
                RS (RS.alpha first)
            rw [hforward] at hcorner
            apply htwoSided (RS.alpha first)
            calc
              dartOrbitFace RS (RS.alpha first) = face := hfirstFace
              _ = dartOrbitFace RS second := hsecondFace.symm
              _ = dartOrbitFace RS (RS.alpha (RS.alpha first)) :=
                hcorner.symm
    | true =>
        cases hsecondSide : RS.incidentFaceSide second face with
        | false =>
            exfalso
            simp [dartSideOrbitFace, hfirstSide] at hfirstFace
            simp [dartSideOrbitFace, hsecondSide] at hsecondFace
            have hcorner :
                dartOrbitFace RS first = dartOrbitFace RS second := by
              calc
                dartOrbitFace RS first =
                    dartOrbitFace RS (RS.alpha (RS.alpha first)) :=
                  congrArg (dartOrbitFace RS)
                    (RS.alpha_involutive first).symm
                _ = dartOrbitFace RS (RS.rho (RS.alpha first)) :=
                  dartOrbitFace_alpha_eq_dartOrbitFace_rho
                    RS (RS.alpha first)
                _ = dartOrbitFace RS second :=
                  congrArg (dartOrbitFace RS) hforward
            apply htwoSided second
            calc
              dartOrbitFace RS second = dartOrbitFace RS first :=
                hcorner.symm
              _ = face := hfirstFace
              _ = dartOrbitFace RS (RS.alpha second) :=
                hsecondFace.symm
        | true => rfl
  · cases hfirstSide : RS.incidentFaceSide first face with
    | false =>
        cases hsecondSide : RS.incidentFaceSide second face with
        | false => rfl
        | true =>
            exfalso
            simp [dartSideOrbitFace, hfirstSide] at hfirstFace
            simp [dartSideOrbitFace, hsecondSide] at hsecondFace
            have hcorner :=
              dartOrbitFace_alpha_eq_dartOrbitFace_rho RS second
            rw [hreverse] at hcorner
            apply htwoSided second
            calc
              dartOrbitFace RS second = face := hsecondFace
              _ = dartOrbitFace RS (RS.alpha first) :=
                hfirstFace.symm
              _ = dartOrbitFace RS (RS.alpha second) :=
                hcorner.symm
    | true =>
        cases hsecondSide : RS.incidentFaceSide second face with
        | false =>
            exfalso
            simp [dartSideOrbitFace, hfirstSide] at hfirstFace
            simp [dartSideOrbitFace, hsecondSide] at hsecondFace
            have hcorner :=
              dartOrbitFace_alpha_eq_dartOrbitFace_rho RS second
            rw [hreverse] at hcorner
            apply htwoSided (RS.alpha first)
            calc
              dartOrbitFace RS (RS.alpha first) =
                  dartOrbitFace RS (RS.alpha second) := hcorner.symm
              _ = face := hsecondFace
              _ = dartOrbitFace RS first := hfirstFace.symm
              _ = dartOrbitFace RS (RS.alpha (RS.alpha first)) :=
                congrArg (dartOrbitFace RS)
                  (RS.alpha_involutive first).symm
        | true => rfl

/-- A nonempty nonbacktracking dart trail carried by one two-sided face has
constant oriented face-side coordinate from its first to its last dart. -/
theorem incidentFaceSide_head_eq_getLast_of_faceCutTrail
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (face : OrbitFace RS) (darts : List RS.D) (hne : darts ≠ [])
    (hchain : darts.IsChain RS.FaceCutTrailStep)
    (hface : ∀ dart ∈ darts,
      RS.edgeOf dart ∈ orbitFaceBoundary RS face) :
    RS.incidentFaceSide (darts.head hne) face =
      RS.incidentFaceSide (darts.getLast hne) face := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  induction rest generalizing first with
  | nil => rfl
  | cons second rest inductionHypothesis =>
      have hfirstSecond := RS.incidentFaceSide_eq_of_faceCutTrailStep
        hcubic hrotation htwoSided hchain.rel
          (hface first (by simp)) (hface second (by simp))
      have htail := inductionHypothesis second (by simp) hchain.of_cons (by
        intro dart hdart
        exact hface dart (by simp [hdart]))
      calc
        RS.incidentFaceSide
            ((first :: second :: rest).head (by simp)) face =
            RS.incidentFaceSide second face := hfirstSecond
        _ = RS.incidentFaceSide
            ((second :: rest).getLast (by simp)) face := htail
        _ = RS.incidentFaceSide
            ((first :: second :: rest).getLast (by simp)) face := by
          simp

end RotationSystem

namespace SimpleGraphDartRotation.Data

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance trunkFaceTransportGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- An edge-simple graph walk contained in one quotient-face boundary has
the same canonical face-side coordinate on its first and last darts. -/
theorem walk_incidentFaceSide_firstDart_eq_lastDart_of_edges_mem_face
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (face : OrbitFace graphData.toRotationSystem)
    {start finish : V} (walk : G.Walk start finish)
    (hnil : ¬walk.Nil) (htrail : walk.IsTrail)
    (hface : ∀ edge : G.edgeSet, edge.1 ∈ walk.edges →
      edge ∈ orbitFaceBoundary graphData.toRotationSystem face) :
    graphData.toRotationSystem.incidentFaceSide
        (walk.firstDart hnil) face =
      graphData.toRotationSystem.incidentFaceSide
        (walk.lastDart hnil) face := by
  let RS := graphData.toRotationSystem
  have hdartsNe : walk.darts ≠ [] :=
    SimpleGraph.Walk.darts_eq_nil.not.mpr hnil
  have hvertices : walk.darts.IsChain (fun first second =>
      RS.vertOf second = RS.vertOf (RS.alpha first)) := by
    apply walk.isChain_dartAdj_darts.imp
    intro first second hadj
    change second.fst = first.symm.fst
    exact hadj.symm
  have hedges : (walk.darts.map RS.edgeOf).Nodup := by
    apply List.Nodup.of_map Subtype.val
    rw [List.map_map]
    change (walk.darts.map SimpleGraph.Dart.edge).Nodup
    exact htrail.edges_nodup
  have hchain : walk.darts.IsChain RS.FaceCutTrailStep :=
    RS.isChain_faceCutTrailStep_of_edgeOf_nodup
      walk.darts hvertices hedges
  have hdartFace : ∀ dart ∈ walk.darts,
      RS.edgeOf dart ∈ orbitFaceBoundary RS face := by
    intro dart hdart
    apply hface (RS.edgeOf dart)
    change dart.edge ∈ walk.edges
    rw [SimpleGraph.Walk.edges]
    exact List.mem_map.mpr ⟨dart, hdart, rfl⟩
  have hmiddle := RS.incidentFaceSide_head_eq_getLast_of_faceCutTrail
    hcubic hrotation htwoSided face walk.darts hdartsNe hchain hdartFace
  have hfirst := congrArg
    (fun dart : G.Dart => RS.incidentFaceSide dart face)
    (walk.firstDart_eq_head_darts hnil)
  have hlast := congrArg
    (fun dart : G.Dart => RS.incidentFaceSide dart face)
    (walk.getLast_darts_eq_lastDart hdartsNe)
  exact hfirst.trans (hmiddle.trans hlast)

end

end SimpleGraphDartRotation.Data

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24AdjacentPairInsertion

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The common trunk is nonempty; in fact its certified width is at least
two. -/
theorem LocalizedAlignedCommonRunTrunk.prefixCommonRun_not_nil
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile) :
    ¬trunk.chain.prefixCommonRun.Nil := by
  apply SimpleGraph.Walk.not_nil_iff_lt_length.mpr
  exact lt_of_lt_of_le (by omega) trunk.two_le_length

/-- The first dart of the common-run walk is the first selected profile
dart. -/
theorem LocalizedAlignedCommonRunTrunk.prefixCommonRun_firstDart
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile) :
    trunk.chain.prefixCommonRun.firstDart
        trunk.prefixCommonRun_not_nil =
      pair.prefixSharedEdgeDart profile.firstRank := by
  apply SimpleGraph.Dart.ext
  simp [LocalizedAlignedCommonRunChain.prefixCommonRun,
    RetainedIntersectionExactFaceCutPair.prefixSharedEdgeInterval,
    SimpleGraph.Walk.edgeInterval,
    RetainedIntersectionExactFaceCutPair.prefixSharedEdgeDart,
    SimpleGraph.Walk.dartAtEdgePosition,
    SimpleGraph.Walk.firstDart_toProd]
  symm
  exact congrArg SimpleGraph.Dart.toProd
    (pair.prefixTrail.darts_getElem_eq_getVert
      (pair.prefixSharedEdgePositionEmbedding profile.firstRank).val
      (by simpa only [SimpleGraph.Walk.length_darts,
          SimpleGraph.Walk.length_edges] using
        (pair.prefixSharedEdgePositionEmbedding profile.firstRank).isLt))

/-- The last dart of the common-run walk is the last selected profile
dart. -/
theorem LocalizedAlignedCommonRunTrunk.prefixCommonRun_lastDart
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile) :
    trunk.chain.prefixCommonRun.lastDart
        trunk.prefixCommonRun_not_nil =
      pair.prefixSharedEdgeDart profile.lastRank := by
  have hpositionOrder :
      (pair.prefixSharedEdgePositionEmbedding profile.firstRank).val ≤
        (pair.prefixSharedEdgePositionEmbedding profile.lastRank).val :=
    (pair.prefixSharedEdgePositionEmbedding.le_iff_le).2
      profile.firstRank_lt_lastRank.le
  have hlastLength :
      (pair.prefixSharedEdgePositionEmbedding profile.lastRank).val <
        pair.prefixTrail.length := by
    simpa only [SimpleGraph.Walk.length_edges] using
      (pair.prefixSharedEdgePositionEmbedding profile.lastRank).isLt
  have hremaining :
      (pair.prefixSharedEdgePositionEmbedding profile.lastRank).val -
          (pair.prefixSharedEdgePositionEmbedding profile.firstRank).val + 1 ≤
        pair.prefixTrail.length -
          (pair.prefixSharedEdgePositionEmbedding profile.firstRank).val := by
    omega
  have hlastIndex :
      (pair.prefixSharedEdgePositionEmbedding profile.firstRank).val +
          (Nat.min
              ((pair.prefixSharedEdgePositionEmbedding profile.lastRank).val -
                (pair.prefixSharedEdgePositionEmbedding profile.firstRank).val + 1)
              (pair.prefixTrail.length -
                (pair.prefixSharedEdgePositionEmbedding profile.firstRank).val) - 1) =
        (pair.prefixSharedEdgePositionEmbedding profile.lastRank).val := by
    simp only [Nat.min, Nat.min_eq_left hremaining]
    omega
  apply SimpleGraph.Dart.ext
  simp [LocalizedAlignedCommonRunChain.prefixCommonRun,
    RetainedIntersectionExactFaceCutPair.prefixSharedEdgeInterval,
    SimpleGraph.Walk.edgeInterval,
    RetainedIntersectionExactFaceCutPair.prefixSharedEdgeDart,
    SimpleGraph.Walk.dartAtEdgePosition,
    SimpleGraph.Walk.lastDart_toProd]
  change
    (pair.prefixTrail.getVert
        ((pair.prefixSharedEdgePositionEmbedding profile.firstRank).val +
          (Nat.min
              ((pair.prefixSharedEdgePositionEmbedding profile.lastRank).val -
                (pair.prefixSharedEdgePositionEmbedding profile.firstRank).val + 1)
              (pair.prefixTrail.length -
                (pair.prefixSharedEdgePositionEmbedding profile.firstRank).val) - 1)),
      pair.prefixTrail.getVert
        ((pair.prefixSharedEdgePositionEmbedding profile.lastRank).val + 1)) =
      pair.prefixTrail.darts[
        (pair.prefixSharedEdgePositionEmbedding profile.lastRank).val].toProd
  rw [hlastIndex]
  symm
  exact congrArg SimpleGraph.Dart.toProd
    (pair.prefixTrail.darts_getElem_eq_getVert
      (pair.prefixSharedEdgePositionEmbedding profile.lastRank).val
      (by simpa only [SimpleGraph.Walk.length_darts,
          SimpleGraph.Walk.length_edges] using
        (pair.prefixSharedEdgePositionEmbedding profile.lastRank).isLt))

/-- Every edge of the included common-run trunk lies on the ambient face
that localizes the shared profile. -/
theorem LocalizedAlignedCommonRunTrunk.ambientPrefixCommonRun_edges_mem_face
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile) :
    ∀ edge : G.edgeSet,
      edge.1 ∈ (data.retainedWalkToAmbient
          trunk.chain.prefixCommonRun).edges →
        edge ∈ orbitFaceBoundary graphData.toRotationSystem face := by
  intro edge hedge
  rw [GoertzelV24AdjacentPairBoundary.AdjacentPairData.retainedWalkToAmbient,
    SimpleGraph.Walk.edges_map] at hedge
  rcases List.mem_map.mp hedge with
    ⟨retainedValue, hretainedValue, hvalue⟩
  let retainedEdge : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet :=
    ⟨retainedValue,
      trunk.chain.prefixCommonRun.edges_subset_edgeSet hretainedValue⟩
  have hword : retainedValue ∈ pair.prefixSharedEdgeOrder := by
    rw [← trunk.prefix_edges]
    exact hretainedValue
  have hboth := (pair.mem_prefixSharedEdgeOrder_iff retainedValue).1 hword
  have hshared : retainedEdge ∈ pair.sharedEdges :=
    (pair.mem_sharedEdges_iff retainedEdge).2 hboth
  have hlocalized := (profile.localized retainedEdge hshared).2
  have heq : retainedEdgeToAmbientEdge data retainedEdge = edge := by
    apply Subtype.ext
    calc
      (retainedEdgeToAmbientEdge data retainedEdge).1 =
          retainedValue.map Subtype.val := rfl
      _ = edge.1 := hvalue
  rw [← heq]
  exact hlocalized

/-- Traversing the included common-run trunk preserves the designated
face's canonical side coordinate from the first profile dart to the last. -/
theorem LocalizedAlignedCommonRunTrunk.ambientEndpointFaceSide_eq
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (trunk : LocalizedAlignedCommonRunTrunk profile)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem) :
    graphData.toRotationSystem.incidentFaceSide
        (pair.ambientPrefixSharedEdgeDart profile.firstRank) face =
      graphData.toRotationSystem.incidentFaceSide
        (pair.ambientPrefixSharedEdgeDart profile.lastRank) face := by
  have hambientNil := retainedWalkToAmbient_not_nil data
    trunk.chain.prefixCommonRun trunk.prefixCommonRun_not_nil
  have htransport :=
    graphData.walk_incidentFaceSide_firstDart_eq_lastDart_of_edges_mem_face
      hcubic hrotation htwoSided face
      (data.retainedWalkToAmbient trunk.chain.prefixCommonRun)
      hambientNil
      (retainedWalkToAmbient_isTrail data trunk.prefix_isTrail)
      trunk.ambientPrefixCommonRun_edges_mem_face
  rw [retainedWalkToAmbient_firstDart data trunk.chain.prefixCommonRun
        trunk.prefixCommonRun_not_nil hambientNil,
      retainedWalkToAmbient_lastDart data trunk.chain.prefixCommonRun
        trunk.prefixCommonRun_not_nil hambientNil,
      trunk.prefixCommonRun_firstDart,
      trunk.prefixCommonRun_lastDart] at htransport
  simpa only [
    RetainedIntersectionExactFaceCutPair.ambientPrefixSharedEdgeDart]
    using htransport

/-- The outgoing trunk coordinate at the split is the Boolean complement
of the incoming trunk coordinate at the merge.  This is forced by facial
transport along the oriented trunk followed by reversal of its last dart. -/
theorem LocalizedAlignedCommonRunSplice.splitTrunkFaceSide_eq_not_merge
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem) :
    splice.splitTrunkFaceSide = !splice.mergeTrunkFaceSide := by
  have hlastEdge : graphData.toRotationSystem.edgeOf
        (pair.ambientPrefixSharedEdgeDart profile.lastRank) ∈
      orbitFaceBoundary graphData.toRotationSystem face := by
    have hedge : graphData.toRotationSystem.edgeOf
          (pair.ambientPrefixSharedEdgeDart profile.lastRank) =
        retainedEdgeToAmbientEdge data
          (pair.sharedEdgeAt profile.lastRank) := by
      apply Subtype.ext
      simp [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf]
    rw [hedge]
    exact splice.trunk.last_edge_mem_face
  have hreverse :=
    graphData.toRotationSystem.incidentFaceSide_alpha_eq_not htwoSided
      (pair.ambientPrefixSharedEdgeDart profile.lastRank) face hlastEdge
  have htransport := splice.trunk.ambientEndpointFaceSide_eq
    hcubic hrotation htwoSided
  unfold LocalizedAlignedCommonRunSplice.splitTrunkFaceSide
    LocalizedAlignedCommonRunSplice.mergeTrunkFaceSide
  rw [SimpleGraphDartRotation.Data.toRotationSystem_alpha] at hreverse
  exact hreverse.trans (congrArg (fun side : Bool => !side) htransport.symm)

end


end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
