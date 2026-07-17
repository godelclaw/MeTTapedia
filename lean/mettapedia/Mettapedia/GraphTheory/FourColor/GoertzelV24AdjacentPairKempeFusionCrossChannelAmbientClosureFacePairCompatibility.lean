import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelAmbientClosureFacePairProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionCrossChannelRejectedFaceTransfer

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24WalkCycleParity
open GoertzelV24WalkFaceCut
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24MinimalFaceIntersections

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance ambientClosureFacePairCompatibilityGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- In a graph-backed minimal map, the finite incidence profile computes the
exact number of common quotient faces of two distinct edges. -/
theorem card_edgeOrbitFacePair_inter_eq_profile_of_minimal
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {first second : G.edgeSet} (hne : first ≠ second) :
    ((edgeOrbitFacePair graphData first) ∩
        (edgeOrbitFacePair graphData second)).card =
      match edgeOrbitFacePairProfile graphData first second with
      | .disjoint => 0
      | .leftLeft => 1
      | .leftRight => 1
      | .rightLeft => 1
      | .rightRight => 1 := by
  let RS := graphData.toRotationSystem
  let firstDart := RS.dartRepresentative first
  let secondDart := RS.dartRepresentative second
  have hle := card_edgeOrbitFacePair_inter_le_one_of_minimal
    graphData minimal hne
  have hspec := edgeOrbitFacePairProfile_spec graphData first second
  cases hprofile : edgeOrbitFacePairProfile graphData first second with
  | disjoint =>
      simp only [hprofile] at hspec
      have hinterEmpty :
          (edgeOrbitFacePair graphData first) ∩
              (edgeOrbitFacePair graphData second) = ∅ := by
        ext face
        constructor
        · intro hmem
          simp only [Finset.mem_inter, edgeOrbitFacePair,
            Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with ⟨hfirst | hfirst, hsecond | hsecond⟩
          · exact (hspec.1 (hfirst.symm.trans hsecond)).elim
          · exact (hspec.2.1 (hfirst.symm.trans hsecond)).elim
          · exact (hspec.2.2.1 (hfirst.symm.trans hsecond)).elim
          · exact (hspec.2.2.2 (hfirst.symm.trans hsecond)).elim
        · simp
      simp [hinterEmpty]
  | leftLeft =>
      simp only [hprofile] at hspec
      have hmem : dartOrbitFace RS firstDart ∈
          (edgeOrbitFacePair graphData first) ∩
            (edgeOrbitFacePair graphData second) := by
        simp only [Finset.mem_inter, edgeOrbitFacePair,
          Finset.mem_insert, Finset.mem_singleton]
        exact ⟨Or.inl rfl, Or.inl hspec⟩
      have hpositive : 1 ≤ ((edgeOrbitFacePair graphData first) ∩
          (edgeOrbitFacePair graphData second)).card :=
        Finset.one_le_card.mpr ⟨_, hmem⟩
      change ((edgeOrbitFacePair graphData first) ∩
        (edgeOrbitFacePair graphData second)).card = 1
      omega
  | leftRight =>
      simp only [hprofile] at hspec
      have hmem : dartOrbitFace RS firstDart ∈
          (edgeOrbitFacePair graphData first) ∩
            (edgeOrbitFacePair graphData second) := by
        simp only [Finset.mem_inter, edgeOrbitFacePair,
          Finset.mem_insert, Finset.mem_singleton]
        exact ⟨Or.inl rfl, Or.inr hspec⟩
      have hpositive : 1 ≤ ((edgeOrbitFacePair graphData first) ∩
          (edgeOrbitFacePair graphData second)).card :=
        Finset.one_le_card.mpr ⟨_, hmem⟩
      change ((edgeOrbitFacePair graphData first) ∩
        (edgeOrbitFacePair graphData second)).card = 1
      omega
  | rightLeft =>
      simp only [hprofile] at hspec
      have hmem : dartOrbitFace RS (RS.alpha firstDart) ∈
          (edgeOrbitFacePair graphData first) ∩
            (edgeOrbitFacePair graphData second) := by
        simp only [Finset.mem_inter, edgeOrbitFacePair,
          Finset.mem_insert, Finset.mem_singleton]
        exact ⟨Or.inr rfl, Or.inl hspec⟩
      have hpositive : 1 ≤ ((edgeOrbitFacePair graphData first) ∩
          (edgeOrbitFacePair graphData second)).card :=
        Finset.one_le_card.mpr ⟨_, hmem⟩
      change ((edgeOrbitFacePair graphData first) ∩
        (edgeOrbitFacePair graphData second)).card = 1
      omega
  | rightRight =>
      simp only [hprofile] at hspec
      have hmem : dartOrbitFace RS (RS.alpha firstDart) ∈
          (edgeOrbitFacePair graphData first) ∩
            (edgeOrbitFacePair graphData second) := by
        simp only [Finset.mem_inter, edgeOrbitFacePair,
          Finset.mem_insert, Finset.mem_singleton]
        exact ⟨Or.inr rfl, Or.inr hspec⟩
      have hpositive : 1 ≤ ((edgeOrbitFacePair graphData first) ∩
          (edgeOrbitFacePair graphData second)).card :=
        Finset.one_le_card.mpr ⟨_, hmem⟩
      change ((edgeOrbitFacePair graphData first) ∩
        (edgeOrbitFacePair graphData second)).card = 1
      omega

/-- The ordered pair of two binary face-cut coordinates. -/
def pairedOrbitFaceLabels {Face : Type*}
    (firstLabels secondLabels : Face → F2) : Face → Color :=
  fun face => (firstLabels face, secondLabels face)

private theorem f2_opposite_unique {common firstOpposite secondOpposite : F2}
    (hfirst : common ≠ firstOpposite)
    (hsecond : common ≠ secondOpposite) :
    firstOpposite = secondOpposite := by
  fin_cases common <;> fin_cases firstOpposite <;>
    fin_cases secondOpposite <;> simp_all

private theorem pairedOrbitFaceLabels_opposite_eq
    {Face : Type*} (firstLabels secondLabels : Face → F2)
    {common firstOpposite secondOpposite : Face}
    (hfirstFirst : firstLabels common ≠ firstLabels firstOpposite)
    (hfirstSecond : firstLabels common ≠ firstLabels secondOpposite)
    (hsecondFirst : secondLabels common ≠ secondLabels firstOpposite)
    (hsecondSecond : secondLabels common ≠ secondLabels secondOpposite) :
    pairedOrbitFaceLabels firstLabels secondLabels firstOpposite =
      pairedOrbitFaceLabels firstLabels secondLabels secondOpposite := by
  apply Prod.ext
  · exact f2_opposite_unique hfirstFirst hfirstSecond
  · exact f2_opposite_unique hsecondFirst hsecondSecond

/-- Exact compatibility demanded of two binary cuts by the actual oriented
face-incidence profile of a pair of edges. -/
def PairedEdgeFaceProfileCompatible
    (graphData : Data G) (first second : G.edgeSet)
    (firstLabels secondLabels : OrbitFace graphData.toRotationSystem → F2) :
    Prop :=
  let RS := graphData.toRotationSystem
  let firstDart := RS.dartRepresentative first
  let secondDart := RS.dartRepresentative second
  match edgeOrbitFacePairProfile graphData first second with
  | .disjoint => True
  | .leftLeft =>
      pairedOrbitFaceLabels firstLabels secondLabels
          (dartOrbitFace RS (RS.alpha firstDart)) =
        pairedOrbitFaceLabels firstLabels secondLabels
          (dartOrbitFace RS (RS.alpha secondDart))
  | .leftRight =>
      pairedOrbitFaceLabels firstLabels secondLabels
          (dartOrbitFace RS (RS.alpha firstDart)) =
        pairedOrbitFaceLabels firstLabels secondLabels
          (dartOrbitFace RS secondDart)
  | .rightLeft =>
      pairedOrbitFaceLabels firstLabels secondLabels
          (dartOrbitFace RS firstDart) =
        pairedOrbitFaceLabels firstLabels secondLabels
          (dartOrbitFace RS (RS.alpha secondDart))
  | .rightRight =>
      pairedOrbitFaceLabels firstLabels secondLabels
          (dartOrbitFace RS firstDart) =
        pairedOrbitFaceLabels firstLabels secondLabels
          (dartOrbitFace RS secondDart)

/-- If both binary cuts change across each of two edges, every one-face
incidence state forces equality of the paired labels on the two opposite
faces. The disjoint state carries no such equality. -/
theorem pairedOrbitFaceLabels_eq_opposite_of_profile
    (graphData : Data G) (first second : G.edgeSet)
    (firstLabels secondLabels : OrbitFace graphData.toRotationSystem → F2)
    (hfirstFirst : firstLabels (dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.dartRepresentative first)) ≠
      firstLabels (dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha
          (graphData.toRotationSystem.dartRepresentative first))))
    (hfirstSecond : firstLabels (dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.dartRepresentative second)) ≠
      firstLabels (dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha
          (graphData.toRotationSystem.dartRepresentative second))))
    (hsecondFirst : secondLabels (dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.dartRepresentative first)) ≠
      secondLabels (dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha
          (graphData.toRotationSystem.dartRepresentative first))))
    (hsecondSecond : secondLabels (dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.dartRepresentative second)) ≠
      secondLabels (dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha
          (graphData.toRotationSystem.dartRepresentative second)))) :
    PairedEdgeFaceProfileCompatible graphData first second
      firstLabels secondLabels := by
  unfold PairedEdgeFaceProfileCompatible
  let RS := graphData.toRotationSystem
  let firstDart := RS.dartRepresentative first
  let secondDart := RS.dartRepresentative second
  have hspec := edgeOrbitFacePairProfile_spec graphData first second
  cases hprofile : edgeOrbitFacePairProfile graphData first second with
  | disjoint => simp
  | leftLeft =>
      simp only [hprofile] at hspec
      apply pairedOrbitFaceLabels_opposite_eq firstLabels secondLabels
      · exact hfirstFirst
      · simpa only [RS, firstDart, secondDart, hspec] using hfirstSecond
      · exact hsecondFirst
      · simpa only [RS, firstDart, secondDart, hspec] using hsecondSecond
  | leftRight =>
      simp only [hprofile] at hspec
      apply pairedOrbitFaceLabels_opposite_eq firstLabels secondLabels
      · exact hfirstFirst
      · simpa only [RS, firstDart, secondDart, hspec] using hfirstSecond.symm
      · exact hsecondFirst
      · simpa only [RS, firstDart, secondDart, hspec] using hsecondSecond.symm
  | rightLeft =>
      simp only [hprofile] at hspec
      apply pairedOrbitFaceLabels_opposite_eq firstLabels secondLabels
      · exact hfirstFirst.symm
      · simpa only [RS, firstDart, secondDart, hspec] using hfirstSecond
      · exact hsecondFirst.symm
      · simpa only [RS, firstDart, secondDart, hspec] using hsecondSecond
  | rightRight =>
      simp only [hprofile] at hspec
      apply pairedOrbitFaceLabels_opposite_eq firstLabels secondLabels
      · exact hfirstFirst.symm
      · simpa only [RS, firstDart, secondDart, hspec] using hfirstSecond.symm
      · exact hsecondFirst.symm
      · simpa only [RS, firstDart, secondDart, hspec] using hsecondSecond.symm

end

end GoertzelV24MinimalFaceIntersections

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- A compositional certificate for the two ambient closures meeting at one
retained cross edge and the restored central edge. -/
structure CrossCentralExactFaceCutPair
    (graphData : Data G) (data : AdjacentPairData G)
    (cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet) where
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
  retainedIntersectionExact :
    ∀ edge : Sym2 (retainedVertexSet data.firstVertex data.secondVertex),
      edge ∈ prefixTrail.edges ∧ edge ∈ suffixTrail.edges ↔ edge = cross.1
  edgesDistinct : (retainedEdgeToAmbientEdge data cross).1 ≠
    centralEdgeValue data
  jointExact : ∀ dart : graphData.toRotationSystem.D,
    (prefixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
          prefixLabels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ∧
      suffixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
          suffixLabels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart))) ↔
      (graphData.toRotationSystem.edgeOf dart).1 =
          (retainedEdgeToAmbientEdge data cross).1 ∨
        (graphData.toRotationSystem.edgeOf dart).1 = centralEdgeValue data

/-- The simultaneous exact-cut certificate on a retained cross edge and the
restored central edge instantiates the finite paired-label compatibility
table. -/
theorem pairedOrbitFaceLabels_eq_opposite_of_joint_retainedCross_central
    (graphData : Data G) (data : AdjacentPairData G)
    (cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (firstLabels secondLabels : OrbitFace graphData.toRotationSystem → F2)
    (hjoint : ∀ dart : graphData.toRotationSystem.D,
      (firstLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
            firstLabels (dartOrbitFace graphData.toRotationSystem
              (graphData.toRotationSystem.alpha dart)) ∧
        secondLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
            secondLabels (dartOrbitFace graphData.toRotationSystem
              (graphData.toRotationSystem.alpha dart))) ↔
        (graphData.toRotationSystem.edgeOf dart).1 =
            (retainedEdgeToAmbientEdge data cross).1 ∨
          (graphData.toRotationSystem.edgeOf dart).1 =
            centralEdgeValue data) :
    PairedEdgeFaceProfileCompatible graphData
      (retainedEdgeToAmbientEdge data cross) (centralEdge data)
      firstLabels secondLabels := by
  let RS := graphData.toRotationSystem
  let first := retainedEdgeToAmbientEdge data cross
  let second := centralEdge data
  let firstDart := RS.dartRepresentative first
  let secondDart := RS.dartRepresentative second
  have hfirstEdge : RS.edgeOf firstDart = first :=
    RS.dartRepresentative_edgeOf first
  have hsecondEdge : RS.edgeOf secondDart = second :=
    RS.dartRepresentative_edgeOf second
  have hfirstJoint := (hjoint firstDart).2 (Or.inl
    (congrArg Subtype.val hfirstEdge))
  have hsecondValue : (RS.edgeOf secondDart).1 = centralEdgeValue data := by
    rw [hsecondEdge]
    rfl
  have hsecondJoint := (hjoint secondDart).2 (Or.inr hsecondValue)
  exact pairedOrbitFaceLabels_eq_opposite_of_profile graphData first second
    firstLabels secondLabels hfirstJoint.1 hsecondJoint.1
      hfirstJoint.2 hsecondJoint.2

/-- Every exact cross-central pair satisfies the actual face-profile
compatibility law. -/
theorem CrossCentralExactFaceCutPair.profileCompatible
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    PairedEdgeFaceProfileCompatible graphData
      (retainedEdgeToAmbientEdge data cross) (centralEdge data)
      pair.prefixLabels pair.suffixLabels :=
  pairedOrbitFaceLabels_eq_opposite_of_joint_retainedCross_central
    graphData data cross pair.prefixLabels pair.suffixLabels pair.jointExact

/-- The selected retained edge belongs to the first retained trail. -/
theorem CrossCentralExactFaceCutPair.cross_mem_prefixTrail
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    cross.1 ∈ pair.prefixTrail.edges :=
  ((pair.retainedIntersectionExact cross.1).2 rfl).1

/-- Hence the ambient selected edge belongs to the first closed trail. -/
theorem CrossCentralExactFaceCutPair.cross_mem_oppositePortClosure
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    (pair : CrossCentralExactFaceCutPair graphData data cross) :
    (retainedEdgeToAmbientEdge data cross).1 ∈
      (data.oppositePortClosure pair.prefixTrail).edges :=
  (retainedEdgeToAmbientEdge_mem_oppositePortClosure_edges_iff
    data pair.prefixTrail cross).2 pair.cross_mem_prefixTrail

/-- The first cut in an exact rejected `bc` certificate records the local
cross transposition as unequal outgoing face labels. -/
theorem EvenKempeFusionLens.bcCrossExitPrefixLabels_ne_of_exactPair
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (lens01.bRoute.crossSplice lens23.cRoute site).support.map
        Subtype.val) :
    pair.prefixLabels (dartOrbitFace graphData.toRotationSystem
        (ambientFirstCrossExitDart data lens01.bRoute lens23.cRoute
          hab hbc site)) ≠
      pair.prefixLabels (dartOrbitFace graphData.toRotationSystem
        (ambientSecondCrossExitDart data lens01.bRoute lens23.cRoute
          hac hbc site)) := by
  apply EvenKempeFusionLens.bcCrossExitFaceLabels_ne_of_rejected
    graphData data lens01 lens23 hab hac hbc hcount site pair.prefixTrail
      (by
        intro edge hedge
        rw [hprefixEdges] at hedge
        exact hedge)
      minimal.spherical.cubic minimal.vertexRotationCyclic pair.prefixLabels
      pair.prefixExact hfalse pair.cross_mem_oppositePortClosure

/-- The symmetric rejected `cb` certificate has the same local inequality
for its first cut. -/
theorem EvenKempeFusionLens.cbCrossExitPrefixLabels_ne_of_exactPair
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false)
    (pair : CrossCentralExactFaceCutPair graphData data site.1)
    (hprefixEdges : pair.prefixTrail.edges =
      (lens01.cRoute.crossSplice lens23.bRoute site).support.map
        Subtype.val) :
    pair.prefixLabels (dartOrbitFace graphData.toRotationSystem
        (ambientFirstCrossExitDart data lens01.cRoute lens23.bRoute
          hac hbc.symm site)) ≠
      pair.prefixLabels (dartOrbitFace graphData.toRotationSystem
        (ambientSecondCrossExitDart data lens01.cRoute lens23.bRoute
          hab hbc.symm site)) := by
  apply EvenKempeFusionLens.cbCrossExitFaceLabels_ne_of_rejected
    graphData data lens01 lens23 hab hac hbc hcount site pair.prefixTrail
      (by
        intro edge hedge
        rw [hprefixEdges] at hedge
        exact hedge)
      minimal.spherical.cubic minimal.vertexRotationCyclic pair.prefixLabels
      pair.prefixExact hfalse pair.cross_mem_oppositePortClosure

/-- A rejected singleton `bc` cross supplies the full compositional
cross-central exact-cut certificate while retaining both exact splice
supports. -/
theorem EvenKempeFusionLens.exists_bcCrossCentralExactFaceCutPair_of_rejected
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.bcCrossSites lens23).length ≤ 1)
    (site : lens01.bRoute.CrossSite lens23.cRoute)
    (hfalse : EvenKempeFusionLens.bcCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    ∃ pair : CrossCentralExactFaceCutPair graphData data site.1,
      pair.prefixTrail.edges =
          (lens01.bRoute.crossSplice lens23.cRoute site).support.map
            Subtype.val ∧
        pair.suffixTrail.edges =
          (lens01.bRoute.crossSuffixSplice lens23.cRoute site).support.map
            Subtype.val := by
  rcases EvenKempeFusionLens.exists_bcExactCrossTrailPair_of_rejected
      graphData data lens01 lens23 hdata hab hac hbc hbDisjoint hcDisjoint
        hcount site hfalse with
    ⟨prefixTrail, suffixTrail, hprefixRetainedTrail, hsuffixRetainedTrail,
      _hprefixPositive, _hsuffixPositive, hprefixEdges, hsuffixEdges,
      hintersection⟩
  have hprefixTrail := data.oppositePortClosure_isTrail
    prefixTrail hprefixRetainedTrail
  have hsuffixTrail := data.alternateOppositePortClosure_isTrail
    suffixTrail hsuffixRetainedTrail
  rcases exists_exactOrbitFaceCutPair_of_minimal graphData minimal
      (data.oppositePortClosure prefixTrail)
      (data.alternateOppositePortClosure suffixTrail)
      hprefixTrail hsuffixTrail with
    ⟨prefixLabels, suffixLabels, hprefixBoundary, hsuffixBoundary,
      hprefixExact, hsuffixExact, hjoint⟩
  have hedgesDistinct : (retainedEdgeToAmbientEdge data site.1).1 ≠
      centralEdgeValue data := by
    intro hedge
    exact retainedEdgeToAmbientEdge_ne_centralEdge data site.1
      (Subtype.ext hedge)
  have hjointExact : ∀ dart : graphData.toRotationSystem.D,
      (prefixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
            prefixLabels (dartOrbitFace graphData.toRotationSystem
              (graphData.toRotationSystem.alpha dart)) ∧
        suffixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
            suffixLabels (dartOrbitFace graphData.toRotationSystem
              (graphData.toRotationSystem.alpha dart))) ↔
        (graphData.toRotationSystem.edgeOf dart).1 =
            (retainedEdgeToAmbientEdge data site.1).1 ∨
          (graphData.toRotationSystem.edgeOf dart).1 =
            centralEdgeValue data := by
    intro dart
    rw [hjoint dart]
    exact data.mem_both_oppositePortClosures_iff_of_exact_retained_intersection
      prefixTrail suffixTrail site.1 hintersection
        (graphData.toRotationSystem.edgeOf dart).1
  refine ⟨{
    prefixTrail := prefixTrail
    suffixTrail := suffixTrail
    prefixLabels := prefixLabels
    suffixLabels := suffixLabels
    prefixTrail_isTrail := hprefixTrail
    suffixTrail_isTrail := hsuffixTrail
    prefixBoundary := hprefixBoundary
    suffixBoundary := hsuffixBoundary
    prefixExact := hprefixExact
    suffixExact := hsuffixExact
    retainedIntersectionExact := hintersection
    edgesDistinct := hedgesDistinct
    jointExact := hjointExact }, hprefixEdges, hsuffixEdges⟩

/-- The symmetric rejected singleton `cb` cross supplies the same exact-cut
certificate with its two exact splice supports. -/
theorem EvenKempeFusionLens.exists_cbCrossCentralExactFaceCutPair_of_rejected
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color}
    (lens01 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 0 1)
    (lens23 : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c 2 3)
    (hdata : data.degreeTwoBoundaryData.WellFormed)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbDisjoint : lens01.bRoute.ambientPath.support.Disjoint
      lens23.bRoute.ambientPath.support)
    (hcDisjoint : lens01.cRoute.ambientPath.support.Disjoint
      lens23.cRoute.ambientPath.support)
    (hcount : (lens01.cbCrossSites lens23).length ≤ 1)
    (site : lens01.cRoute.CrossSite lens23.bRoute)
    (hfalse : EvenKempeFusionLens.cbCrossExitFaceTransferBit
      lens01 graphData lens23 hab hac hbc site = false) :
    ∃ pair : CrossCentralExactFaceCutPair graphData data site.1,
      pair.prefixTrail.edges =
          (lens01.cRoute.crossSplice lens23.bRoute site).support.map
            Subtype.val ∧
        pair.suffixTrail.edges =
          (lens01.cRoute.crossSuffixSplice lens23.bRoute site).support.map
            Subtype.val := by
  rcases EvenKempeFusionLens.exists_cbExactCrossTrailPair_of_rejected
      graphData data lens01 lens23 hdata hab hac hbc hbDisjoint hcDisjoint
        hcount site hfalse with
    ⟨prefixTrail, suffixTrail, hprefixRetainedTrail, hsuffixRetainedTrail,
      _hprefixPositive, _hsuffixPositive, hprefixEdges, hsuffixEdges,
      hintersection⟩
  have hprefixTrail := data.oppositePortClosure_isTrail
    prefixTrail hprefixRetainedTrail
  have hsuffixTrail := data.alternateOppositePortClosure_isTrail
    suffixTrail hsuffixRetainedTrail
  rcases exists_exactOrbitFaceCutPair_of_minimal graphData minimal
      (data.oppositePortClosure prefixTrail)
      (data.alternateOppositePortClosure suffixTrail)
      hprefixTrail hsuffixTrail with
    ⟨prefixLabels, suffixLabels, hprefixBoundary, hsuffixBoundary,
      hprefixExact, hsuffixExact, hjoint⟩
  have hedgesDistinct : (retainedEdgeToAmbientEdge data site.1).1 ≠
      centralEdgeValue data := by
    intro hedge
    exact retainedEdgeToAmbientEdge_ne_centralEdge data site.1
      (Subtype.ext hedge)
  have hjointExact : ∀ dart : graphData.toRotationSystem.D,
      (prefixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
            prefixLabels (dartOrbitFace graphData.toRotationSystem
              (graphData.toRotationSystem.alpha dart)) ∧
        suffixLabels (dartOrbitFace graphData.toRotationSystem dart) ≠
            suffixLabels (dartOrbitFace graphData.toRotationSystem
              (graphData.toRotationSystem.alpha dart))) ↔
        (graphData.toRotationSystem.edgeOf dart).1 =
            (retainedEdgeToAmbientEdge data site.1).1 ∨
          (graphData.toRotationSystem.edgeOf dart).1 =
            centralEdgeValue data := by
    intro dart
    rw [hjoint dart]
    exact data.mem_both_oppositePortClosures_iff_of_exact_retained_intersection
      prefixTrail suffixTrail site.1 hintersection
        (graphData.toRotationSystem.edgeOf dart).1
  refine ⟨{
    prefixTrail := prefixTrail
    suffixTrail := suffixTrail
    prefixLabels := prefixLabels
    suffixLabels := suffixLabels
    prefixTrail_isTrail := hprefixTrail
    suffixTrail_isTrail := hsuffixTrail
    prefixBoundary := hprefixBoundary
    suffixBoundary := hsuffixBoundary
    prefixExact := hprefixExact
    suffixExact := hsuffixExact
    retainedIntersectionExact := hintersection
    edgesDistinct := hedgesDistinct
    jointExact := hjointExact }, hprefixEdges, hsuffixEdges⟩

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
