import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionProfileCommonRunAmbientEndpointDarts

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open SimpleGraph
open SimpleGraphDartRotation

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Whether the first step of a displayed three-dart word follows the
displayed order. Malformed shorter words receive the default value `false`. -/
def threeDartWordOrientation (RS : RotationSystem V E)
    (darts : List RS.D) : Bool :=
  match darts with
  | first :: second :: _ => decide (RS.rho first = second)
  | _ => false

/-- A three-dart word together with its actual cyclic orientation under a
rotation permutation. `true` means the displayed order follows `rho`;
`false` means the reverse displayed order follows `rho`. -/
structure ThreeDartRotation (RS : RotationSystem V E)
    (darts : List RS.D) where
  first : RS.D
  second : RS.D
  third : RS.D
  word_eq : darts = [first, second, third]
  word_nodup : darts.Nodup
  orientation : Bool
  rho_first : RS.rho first = if orientation then second else third
  rho_second : RS.rho second = if orientation then third else first
  rho_third : RS.rho third = if orientation then first else second

/-- A certified three-dart rotation carries the canonical orientation bit
computed from its displayed word. -/
@[simp] theorem ThreeDartRotation.threeDartWordOrientation_eq
    {RS : RotationSystem V E} {darts : List RS.D}
    (rotation : ThreeDartRotation RS darts) :
    RS.threeDartWordOrientation darts = rotation.orientation := by
  have hdistinct : rotation.second ≠ rotation.third := by
    have hnodup := rotation.word_nodup
    rw [rotation.word_eq] at hnodup
    have hpairs : rotation.first ≠ rotation.second ∧
        rotation.first ≠ rotation.third ∧
        rotation.second ≠ rotation.third := by
      simpa [and_assoc] using hnodup
    exact hpairs.2.2
  cases horientation : rotation.orientation with
  | false =>
      have hrho : RS.rho rotation.first = rotation.third := by
        simpa [horientation] using rotation.rho_first
      have hne : RS.rho rotation.first ≠ rotation.second := by
        intro heq
        exact hdistinct (heq.symm.trans hrho)
      simp [threeDartWordOrientation, rotation.word_eq, hne]
  | true =>
      have hrho : RS.rho rotation.first = rotation.second := by
        simpa [horientation] using rotation.rho_first
      simp [threeDartWordOrientation, rotation.word_eq, hrho]

/-- A cyclic cubic rotation on three distinct darts based at one vertex has
one of the two possible cyclic orientations. -/
theorem rho_three_cycle_orientation_of_cubic
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    {first second third : RS.D}
    (hsecondBase : RS.vertOf second = RS.vertOf first)
    (hthirdBase : RS.vertOf third = RS.vertOf first)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    (RS.rho first = second ∧ RS.rho second = third ∧
        RS.rho third = first) ∨
      (RS.rho first = third ∧ RS.rho third = second ∧
        RS.rho second = first) := by
  rcases RS.rho_eq_second_or_third_of_cubic hcubic hrotation
      hsecondBase hthirdBase hfirstSecond hfirstThird hsecondThird with
    hforward | hreverse
  · have hcycle := RS.rho_three_cycle_of_eq_second hcubic hrotation
      hsecondBase hthirdBase hfirstSecond hfirstThird hsecondThird hforward
    exact Or.inl ⟨hforward, hcycle.1, hcycle.2⟩
  · have hcycle := RS.rho_three_cycle_of_eq_second hcubic hrotation
      hthirdBase hsecondBase hfirstThird hfirstSecond hsecondThird.symm
        hreverse
    exact Or.inr ⟨hreverse, hcycle.1, hcycle.2⟩

/-- A duplicate-free three-dart word based at one cubic cyclic vertex has
a certified local rotation orientation. -/
theorem nonempty_threeDartRotation_of_cubic
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (vertex : V) (darts : List RS.D)
    (hlength : darts.length = 3) (hnodup : darts.Nodup)
    (hbase : ∀ dart ∈ darts, RS.vertOf dart = vertex) :
    Nonempty (ThreeDartRotation RS darts) := by
  obtain ⟨first, second, third, rfl⟩ := List.length_eq_three.mp hlength
  have hfirstBase : RS.vertOf first = vertex := hbase first (by simp)
  have hsecondBase : RS.vertOf second = vertex := hbase second (by simp)
  have hthirdBase : RS.vertOf third = vertex := hbase third (by simp)
  have hdistinct : first ≠ second ∧ first ≠ third ∧ second ≠ third := by
    simpa [and_assoc] using hnodup
  rcases RS.rho_three_cycle_orientation_of_cubic hcubic hrotation
      (hsecondBase.trans hfirstBase.symm)
      (hthirdBase.trans hfirstBase.symm)
      hdistinct.1 hdistinct.2.1 hdistinct.2.2 with
    hforward | hreverse
  · exact ⟨{
      first := first
      second := second
      third := third
      word_eq := rfl
      word_nodup := hnodup
      orientation := true
      rho_first := by simpa using hforward.1
      rho_second := by simpa using hforward.2.1
      rho_third := by simpa using hforward.2.2 }⟩
  · exact ⟨{
      first := first
      second := second
      third := third
      word_eq := rfl
      word_nodup := hnodup
      orientation := false
      rho_first := by simpa using hreverse.1
      rho_second := by simpa using hreverse.2.2
      rho_third := by simpa using hreverse.2.1 }⟩

end RotationSystem

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The canonical ambient merge word realizes one of the two local cyclic
orders. -/
theorem LocalizedAlignedCommonRunSplice.nonempty_merge_ambientRotation
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (state : LocalizedCommonRunMergeArmState splice) :
    Nonempty (RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts) := by
  apply graphData.toRotationSystem.nonempty_threeDartRotation_of_cubic
    hcubic hrotation
    (pair.prefixSharedEdgeDart profile.firstRank).fst.1
    state.ambientOutgoingDarts state.ambientOutgoingDarts_length
    (splice.merge_ambientOutgoingDarts_nodup state)
  intro dart hdart
  exact state.ambientOutgoingDarts_fst_eq hdart

/-- The canonical ambient split word realizes one of the two local cyclic
orders. -/
theorem LocalizedAlignedCommonRunSplice.nonempty_split_ambientRotation
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {profile : LocalizedAlignedSharedEdgeProfile pair oldCross face}
    (splice : LocalizedAlignedCommonRunSplice profile)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (state : LocalizedCommonRunSplitArmState splice) :
    Nonempty (RotationSystem.ThreeDartRotation
      graphData.toRotationSystem state.ambientOutgoingDarts) := by
  apply graphData.toRotationSystem.nonempty_threeDartRotation_of_cubic
    hcubic hrotation
    (pair.prefixSharedEdgeDart profile.lastRank).snd.1
    state.ambientOutgoingDarts state.ambientOutgoingDarts_length
    (splice.split_ambientOutgoingDarts_nodup state)
  intro dart hdart
  exact state.ambientOutgoingDarts_fst_eq hdart

/-- The fusion-chain normal form with every clean four-arm endpoint equipped
with its ambient cyclic-order certificate. -/
inductive LocalizedFusionChainRotationResolution
    {graphData : Data G} {data : AdjacentPairData G}
    (pair : RetainedIntersectionExactFaceCutPair graphData data)
    (oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet)
    (face : OrbitFace graphData.toRotationSystem) where
  | parallelArmCycle
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (splice : LocalizedAlignedCommonRunSplice profile)
      (cycle : Nonempty (LocalizedCommonRunParallelArmCycle splice))
  | crossedArmCycle
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (splice : LocalizedAlignedCommonRunSplice profile)
      (cycle : Nonempty (LocalizedCommonRunCrossedArmCycle splice))
  | cleanFourArms
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (splice : LocalizedAlignedCommonRunSplice profile)
      (clean : Nonempty (LocalizedCommonRunCleanFourArms splice))
      (mergeState : LocalizedCommonRunMergeArmState splice)
      (splitState : LocalizedCommonRunSplitArmState splice)
      (mergeRotation : Nonempty (RotationSystem.ThreeDartRotation
        graphData.toRotationSystem mergeState.ambientOutgoingDarts))
      (splitRotation : Nonempty (RotationSystem.ThreeDartRotation
        graphData.toRotationSystem splitState.ambientOutgoingDarts))
  | alignedBubbleCycle
      (profile : LocalizedAlignedSharedEdgeProfile pair oldCross face)
      (bubble : Nonempty (LocalizedAlignedBubblePrimalCycle profile))
  | strictlyShorterMixedPortCycles
      (descent : Nonempty
        (LocalizedStrictlyShorterMixedPortCycles pair oldCross face))
  | orderInversionPrimalCycle
      (descent : Nonempty
        (LocalizedOrderInversionPrimalCycle pair oldCross face))

/-- Cubicity and vertex cyclicity refine every clean four-arm branch to
explicit merge and split rotation orientations. -/
theorem LocalizedFusionChainCrossedResolution.nonempty_rotationResolution
    {graphData : Data G} {data : AdjacentPairData G}
    {pair : RetainedIntersectionExactFaceCutPair graphData data}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    (resolution : LocalizedFusionChainCrossedResolution pair oldCross face)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    Nonempty (LocalizedFusionChainRotationResolution pair oldCross face) := by
  cases resolution with
  | parallelArmCycle profile splice cycle =>
      exact ⟨LocalizedFusionChainRotationResolution.parallelArmCycle
        profile splice cycle⟩
  | crossedArmCycle profile splice cycle =>
      exact ⟨LocalizedFusionChainRotationResolution.crossedArmCycle
        profile splice cycle⟩
  | cleanFourArms profile splice clean mergeState splitState =>
      exact ⟨LocalizedFusionChainRotationResolution.cleanFourArms
        profile splice clean mergeState splitState
          (splice.nonempty_merge_ambientRotation hcubic hrotation mergeState)
          (splice.nonempty_split_ambientRotation hcubic hrotation splitState)⟩
  | alignedBubbleCycle profile bubble =>
      exact ⟨LocalizedFusionChainRotationResolution.alignedBubbleCycle
        profile bubble⟩
  | strictlyShorterMixedPortCycles descent =>
      exact ⟨
        LocalizedFusionChainRotationResolution.strictlyShorterMixedPortCycles
          descent⟩
  | orderInversionPrimalCycle descent =>
      exact ⟨LocalizedFusionChainRotationResolution.orderInversionPrimalCycle
        descent⟩

/-- A width-at-least-two successor profile reaches the endpoint-rotation
resolved fusion-chain normal form. -/
theorem LocalizedSuccessorFusionChainProfile.nonempty_rotationResolution
    {graphData : Data G} {data : AdjacentPairData G}
    {oldCross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {face : OrbitFace graphData.toRotationSystem}
    {prefixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 0) (data.retainedPort 2)}
    {suffixSuccessor : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).Walk (data.retainedPort 1) (data.retainedPort 3)}
    (successor : LocalizedSuccessorFusionChainProfile oldCross face
      prefixSuccessor suffixSuccessor)
    (hprefix : successor.pair.prefixTrail.IsPath)
    (hsuffix : successor.pair.suffixTrail.IsPath)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    Nonempty (LocalizedFusionChainRotationResolution successor.pair oldCross
      face) := by
  rcases successor.nonempty_crossedResolution hprefix hsuffix with
    ⟨resolution⟩
  exact resolution.nonempty_rotationResolution hcubic hrotation

/-- The successor-pair trichotomy with its fusion-chain branch refined by
ambient endpoint rotation orders. -/
def LocalizedFusionSuccessorResolution.RotationOutcome
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
        Nonempty (LocalizedFusionChainRotationResolution successor.pair cross
          face))

/-- Every resolved successor pair realizes its endpoint-rotation-refined
outcome in a cubic cyclic rotation system. -/
theorem LocalizedFusionSuccessorResolution.finite_rotation_outcome
    {graphData : Data G} {data : AdjacentPairData G}
    {cross : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).edgeSet}
    {pair : CrossCentralExactFaceCutPair graphData data cross}
    {face : OrbitFace graphData.toRotationSystem}
    {firstRoot secondRoot : V}
    {firstFusion : G.Walk firstRoot firstRoot}
    {secondFusion : G.Walk secondRoot secondRoot}
    (successors : LocalizedFusionSuccessorResolution pair face
      firstFusion secondFusion)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem) :
    successors.RotationOutcome := by
  unfold LocalizedFusionSuccessorResolution.RotationOutcome
  rcases successors.finite_outcome with hdisjoint | hrebase | hprofile
  · exact Or.inl hdisjoint
  · exact Or.inr (Or.inl hrebase)
  · rcases hprofile with ⟨successor⟩
    have hprefix : successor.pair.prefixTrail.IsPath := by
      rw [successor.prefix_eq]
      exact successors.prefix_isPath
    have hsuffix : successor.pair.suffixTrail.IsPath := by
      rw [successor.suffix_eq]
      exact successors.suffix_isPath
    exact Or.inr (Or.inr ⟨successor,
      successor.nonempty_rotationResolution hprefix hsuffix hcubic
        hrotation⟩)

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
