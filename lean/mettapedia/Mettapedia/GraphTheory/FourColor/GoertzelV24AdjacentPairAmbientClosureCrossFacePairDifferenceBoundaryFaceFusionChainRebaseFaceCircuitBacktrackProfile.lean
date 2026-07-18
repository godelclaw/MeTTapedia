import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitSupportRigidity

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

namespace CrossCentralExactFaceCertifiedRebaseCircuit

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- The rigid endpoint form of a constant-face circuit block: its retained
cross and both retained paths return, with only two global binary label
complements left. -/
def MiddleBlockComplementProfile
    (middleFirst right :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (middleRest : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)) :
    Prop :=
  middleFirst.source.1 = right.source.1 ∧
    Even (middleFirst :: middleRest).length ∧
    middleFirst.source.2.prefixTrail = right.source.2.prefixTrail ∧
    middleFirst.source.2.suffixTrail = right.source.2.suffixTrail ∧
    ∃! profile : F2 × F2,
      (∀ face, right.source.2.prefixLabels face =
        middleFirst.source.2.prefixLabels face + profile.1) ∧
      (∀ face, right.source.2.suffixLabels face =
        middleFirst.source.2.suffixLabels face + profile.2)

/-- A prefix edge lost inside a constant-face block and recovered by one
arc of the complementary circuit segment on a different selected face. -/
def OutsidePrefixClosureRecovery
    (middleFace : OrbitFace graphData.toRotationSystem)
    (source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic))
    (outside : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)) :
    Prop :=
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  ∃ edge : G.edgeSet,
    edge ∉ orbitFaceBoundary graphData.toRotationSystem middleFace ∧
    edge.1 ∈ (data.oppositePortClosure source.2.prefixTrail).edges ∧
    edge.1 ∉ (data.oppositePortClosure target.2.prefixTrail).edges ∧
    ∃ arc ∈ outside,
      edge.1 ∉
          (data.oppositePortClosure arc.source.2.prefixTrail).edges ∧
      edge.1 ∈
          (data.oppositePortClosure arc.target.2.prefixTrail).edges ∧
      edge ∈ orbitFaceBoundary graphData.toRotationSystem
        arc.selectedFace ∧
      arc.selectedFace ≠ middleFace

/-- The corresponding localized recovery profile for the suffix closure. -/
def OutsideSuffixClosureRecovery
    (middleFace : OrbitFace graphData.toRotationSystem)
    (source target : CrossCentralExactFaceCutState graphData
      (baseData.rotationOrderedData graphData minimal.spherical.cubic
        minimal.vertexRotationCyclic))
    (outside : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)) :
    Prop :=
  let data := baseData.rotationOrderedData graphData
    minimal.spherical.cubic minimal.vertexRotationCyclic
  ∃ edge : G.edgeSet,
    edge ∉ orbitFaceBoundary graphData.toRotationSystem middleFace ∧
    edge.1 ∈
        (data.alternateOppositePortClosure source.2.suffixTrail).edges ∧
    edge.1 ∉
        (data.alternateOppositePortClosure target.2.suffixTrail).edges ∧
    ∃ arc ∈ outside,
      edge.1 ∉
          (data.alternateOppositePortClosure
            arc.source.2.suffixTrail).edges ∧
      edge.1 ∈
          (data.alternateOppositePortClosure
            arc.target.2.suffixTrail).edges ∧
      edge ∈ orbitFaceBoundary graphData.toRotationSystem
        arc.selectedFace ∧
      arc.selectedFace ≠ middleFace

/-- A two-face circuit excursion has a complete structural trichotomy. The
constant middle block either returns in the four-state complement normal
form, or one closure channel has an off-face loss recovered on a different
face of the complementary circuit segment. -/
theorem middleBlock_complementProfile_or_outside_prefixRecovery_or_suffixRecovery
    (circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (firstFace secondFace : OrbitFace graphData.toRotationSystem)
    (hfaces : firstFace ≠ secondFace)
    (left middleFirst right :
      CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData)
    (before middleRest after : List
      (CrossCentralExactFaceCertifiedRebaseArc graphData minimal baseData))
    (hsplit : circuit.first :: circuit.rest =
      before ++
        (left :: ((middleFirst :: middleRest) ++ (right :: after))))
    (hleftFace : left.selectedFace = firstFace)
    (hmiddleFaces : ∀ arc ∈ middleFirst :: middleRest,
      arc.selectedFace = secondFace)
    (hrightFace : right.selectedFace = firstFace) :
    MiddleBlockComplementProfile middleFirst right middleRest ∨
      OutsidePrefixClosureRecovery secondFace middleFirst.source
        right.source (right :: (after ++ before ++ [left])) ∨
      OutsideSuffixClosureRecovery secondFace middleFirst.source
        right.source (right :: (after ++ before ++ [left])) := by
  classical
  let middleArcs := middleFirst :: middleRest
  have hfullChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (before ++ (left :: (middleArcs ++ (right :: after)))) := by
    rw [← hsplit]
    exact circuit.consecutive
  have htailChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (left :: (middleArcs ++ (right :: after))) :=
    (List.isChain_append.mp hfullChain).2.1
  have hleftParts := List.isChain_cons_cons.mp htailChain
  have hmiddleAfterChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (middleArcs ++ (right :: after)) := by
    simpa [middleArcs] using hleftParts.2
  have hmiddleParts := List.isChain_append.mp hmiddleAfterChain
  have hmiddleChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows middleArcs :=
    hmiddleParts.1
  have hmiddleNe : middleArcs ≠ [] := by simp [middleArcs]
  let middleLast := middleArcs.getLast hmiddleNe
  have hlastMem : middleLast ∈ middleArcs.getLast? := by
    rw [List.getLast?_eq_getLast_of_ne_nil hmiddleNe]
    simp [middleLast]
  have hlastFollows :
      CrossCentralExactFaceCertifiedRebaseArc.Follows middleLast right :=
    hmiddleParts.2.2 middleLast hlastMem right (by simp)
  have hmiddleRun := exactSteps_of_arc_chain_on_face secondFace
    middleFirst middleRest (by simpa [middleArcs] using hmiddleChain)
      hmiddleFaces
  have hlastEq : middleLast.target = right.source := hlastFollows
  have hrun : ExactRebaseRelation.ExactSteps
      (CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
        minimal baseData secondFace)
      middleArcs.length middleFirst.source right.source := by
    change ExactRebaseRelation.ExactSteps
      (CrossCentralExactFaceCertifiedRebaseTransitionOnFace graphData
        minimal baseData secondFace)
      middleArcs.length middleFirst.source middleLast.target at hmiddleRun
    rw [hlastEq] at hmiddleRun
    exact hmiddleRun
  have hmiddleRightChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (middleArcs ++ [right]) := by
    apply hmiddleChain.append (List.IsChain.singleton _)
    intro last hlast first hfirst
    have hlast' : last = middleLast := by
      rcases List.mem_getLast?_eq_getLast hlast with ⟨hne, heq⟩
      simpa [middleLast] using heq
    have hfirst' : first = right := by simpa using hfirst.symm
    simpa [hlast', hfirst'] using hlastFollows
  have hexcurChain : List.IsChain
      CrossCentralExactFaceCertifiedRebaseArc.Follows
        (left :: (middleArcs ++ [right])) :=
    List.IsChain.cons_cons hleftParts.1 hmiddleRightChain
  have hcross : middleFirst.source.1 = right.source.1 := by
    apply cross_eq_across_constantFace_excursion firstFace secondFace
      hfaces left middleFirst right middleRest
    · simpa [middleArcs] using hexcurChain
    · exact hleftFace
    · exact hmiddleFaces
    · exact hrightFace
  have hsourcePrefix : middleFirst.source.2.prefixTrail.IsPath := by
    rw [← hleftParts.1]
    exact left.transition.target_prefix_isPath
  have hsourceSuffix : middleFirst.source.2.suffixTrail.IsPath := by
    rw [← hleftParts.1]
    exact left.transition.target_suffix_isPath
  have htargetPrefix : right.source.2.prefixTrail.IsPath := by
    rw [← hlastEq]
    exact middleLast.transition.target_prefix_isPath
  have htargetSuffix : right.source.2.suffixTrail.IsPath := by
    rw [← hlastEq]
    exact middleLast.transition.target_suffix_isPath
  rcases
      CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_labelComplementProfile_or_offFace_prefixLoss_or_suffixLoss
        hrun hcross hsourcePrefix htargetPrefix hsourceSuffix htargetSuffix with
    hnormal | hlossPrefix | hlossSuffix
  · left
    exact ⟨hcross, hnormal.1, hnormal.2.1, hnormal.2.2.1,
      hnormal.2.2.2⟩
  · right
    left
    rcases hlossPrefix with ⟨edge, hedgeOff, hsource, htarget⟩
    rcases circuit.exists_outside_prefixClosure_recovery left middleFirst
        right before middleRest after hsplit edge htarget hsource with
      ⟨arc, harc, harcSource, harcTarget, harcFace⟩
    refine ⟨edge, hedgeOff, hsource, htarget, arc, harc,
      harcSource, harcTarget, harcFace, ?_⟩
    intro heq
    exact hedgeOff (heq ▸ harcFace)
  · right
    right
    rcases hlossSuffix with ⟨edge, hedgeOff, hsource, htarget⟩
    rcases circuit.exists_outside_suffixClosure_recovery left middleFirst
        right before middleRest after hsplit edge htarget hsource with
      ⟨arc, harc, harcSource, harcTarget, harcFace⟩
    refine ⟨edge, hedgeOff, hsource, htarget, arc, harc,
      harcSource, harcTarget, harcFace, ?_⟩
    intro heq
    exact hedgeOff (heq ▸ harcFace)

end CrossCentralExactFaceCertifiedRebaseCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
