import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitFiniteProfileShortening

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

/-- The retained cross is determined by the two exact trails: it is their
unique common retained edge. -/
theorem CrossCentralExactFaceCutState.cross_eq_of_trails_eq
    {graphData : Data G} {data : AdjacentPairData G}
    (first second : CrossCentralExactFaceCutState graphData data)
    (hprefix : first.2.prefixTrail = second.2.prefixTrail)
    (hsuffix : first.2.suffixTrail = second.2.suffixTrail) :
    first.1 = second.1 := by
  apply Subtype.ext
  have hfirst : first.1.1 ∈ first.2.prefixTrail.edges ∧
      first.1.1 ∈ first.2.suffixTrail.edges :=
    (first.2.retainedIntersectionExact first.1.1).2 rfl
  have hsecond : first.1.1 ∈ second.2.prefixTrail.edges ∧
      first.1.1 ∈ second.2.suffixTrail.edges := by
    simpa [hprefix, hsuffix] using hfirst
  exact (second.2.retainedIntersectionExact first.1.1).1 hsecond

namespace CrossCentralExactFaceCertifiedRebaseCircuit

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- A globally shortest circuit supported on one selected face consists of
exactly two mutually returning rebases.  Three displayed arcs would restore
both retained trails and their exact cross after the first two steps, hence
repeat a rigid state. -/
theorem IsLengthMinimal.arcLength_eq_two_of_constantFace
    {circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData}
    (hminimal : circuit.IsLengthMinimal)
    (hfaces : ∀ arc ∈ circuit.first :: circuit.rest,
      arc.selectedFace = circuit.first.selectedFace) :
    circuit.arcLength = 2 := by
  have heven : Even circuit.arcLength := by
    exact circuit.length_even_of_selectedFace_eq
      circuit.first.selectedFace hfaces
  have hpositive : 0 < circuit.arcLength := by
    simp [arcLength]
  have hle : circuit.arcLength ≤ 2 := by
    by_contra hnot
    have hthree : 3 ≤ circuit.arcLength := by omega
    have hrestTwo : 2 ≤ circuit.rest.length := by
      simpa [arcLength] using hthree
    generalize hrestEq : circuit.rest = rest at hrestTwo
    cases rest with
    | nil => simp at hrestTwo
    | cons second rest =>
      cases rest with
      | nil => simp at hrestTwo
      | cons third after =>
        have hconsecutive := circuit.consecutive
        rw [hrestEq] at hconsecutive
        have hclosing := circuit.closing
        rw [hrestEq] at hclosing
        have hfirstSecond :
            CrossCentralExactFaceCertifiedRebaseArc.Follows
              circuit.first second :=
          (List.isChain_cons_cons.mp hconsecutive).1
        have htailChain : List.IsChain
            CrossCentralExactFaceCertifiedRebaseArc.Follows
              (second :: third :: after) :=
          (List.isChain_cons_cons.mp hconsecutive).2
        have hsecondThird :
            CrossCentralExactFaceCertifiedRebaseArc.Follows second third :=
          (List.isChain_cons_cons.mp htailChain).1
        have hthirdChain : List.IsChain
            CrossCentralExactFaceCertifiedRebaseArc.Follows
              (third :: after) :=
          (List.isChain_cons_cons.mp htailChain).2
        let face := circuit.first.selectedFace
        have hsecondFace : second.selectedFace = face :=
          hfaces second (by simp [hrestEq])
        have hthirdFaces : ∀ arc ∈ third :: after,
            arc.selectedFace = face := by
          intro arc harc
          exact hfaces arc (by simp [hrestEq, harc])
        have hfirstTransition :
            CrossCentralExactFaceCertifiedRebaseTransitionOnFace
              graphData minimal baseData face circuit.first.source
                second.source := by
          rw [← hfirstSecond]
          exact circuit.first.transition
        have hsecondTransition :
            CrossCentralExactFaceCertifiedRebaseTransitionOnFace
              graphData minimal baseData face second.source
                third.source := by
          rw [← hsecondThird, ← hsecondFace]
          exact second.transition
        have htailRun := exactSteps_of_arc_chain_on_face face third after
          hthirdChain hthirdFaces
        have htailClosing :
            ((third :: after).getLast (by simp)).target =
              circuit.first.source := by
          simpa [CrossCentralExactFaceCertifiedRebaseArc.Follows] using
            hclosing
        rw [htailClosing] at htailRun
        have htailRefl := htailRun.to_reflTransGen
        let data := baseData.rotationOrderedData graphData
          minimal.spherical.cubic minimal.vertexRotationCyclic
        have hprefixOff : ∀ edge : G.edgeSet,
            edge ∉ orbitFaceBoundary graphData.toRotationSystem face →
              (edge.1 ∈
                  (data.oppositePortClosure
                    circuit.first.source.2.prefixTrail).edges ↔
                edge.1 ∈
                  (data.oppositePortClosure
                    third.source.2.prefixTrail).edges) := by
          intro edge hoff
          constructor
          · exact
              CrossCentralExactFaceCertifiedRebaseTransitionOnFace.reflTransGen_prefixClosure_offFace_subset
                htailRefl edge hoff
          · intro hthird
            exact hfirstTransition.target_prefixClosure_offFace_subset_source
              edge hoff
                (hsecondTransition.target_prefixClosure_offFace_subset_source
                  edge hoff hthird)
        have hsuffixOff : ∀ edge : G.edgeSet,
            edge ∉ orbitFaceBoundary graphData.toRotationSystem face →
              (edge.1 ∈
                  (data.alternateOppositePortClosure
                    circuit.first.source.2.suffixTrail).edges ↔
                edge.1 ∈
                  (data.alternateOppositePortClosure
                    third.source.2.suffixTrail).edges) := by
          intro edge hoff
          constructor
          · exact
              CrossCentralExactFaceCertifiedRebaseTransitionOnFace.reflTransGen_suffixClosure_offFace_subset
                htailRefl edge hoff
          · intro hthird
            exact hfirstTransition.target_suffixClosure_offFace_subset_source
              edge hoff
                (hsecondTransition.target_suffixClosure_offFace_subset_source
                  edge hoff hthird)
        have htwoRun : ExactRebaseRelation.ExactSteps
            (CrossCentralExactFaceCertifiedRebaseTransitionOnFace
              graphData minimal baseData face) 2 circuit.first.source
                third.source := by
          exact ExactRebaseRelation.ExactSteps.tail
            (ExactRebaseRelation.ExactSteps.tail
              (ExactRebaseRelation.ExactSteps.refl circuit.first.source)
                hfirstTransition) hsecondTransition
        have hsourcePrefix : circuit.first.source.2.prefixTrail.IsPath := by
          have hpath :=
            ((circuit.first :: second :: third :: after).getLast
              (by simp)).transition.target_prefix_isPath
          rw [hclosing] at hpath
          exact hpath
        have hsourceSuffix : circuit.first.source.2.suffixTrail.IsPath := by
          have hpath :=
            ((circuit.first :: second :: third :: after).getLast
              (by simp)).transition.target_suffix_isPath
          rw [hclosing] at hpath
          exact hpath
        have htargetPrefix : third.source.2.prefixTrail.IsPath := by
          rw [← hsecondThird]
          exact second.transition.target_prefix_isPath
        have htargetSuffix : third.source.2.suffixTrail.IsPath := by
          rw [← hsecondThird]
          exact second.transition.target_suffix_isPath
        have htrails :=
          CrossCentralExactFaceCertifiedRebaseTransitionOnFace.exactSteps_trails_eq_and_existsUnique_labelComplementProfile_of_even
            htwoRun (by norm_num) hprefixOff hsuffixOff hsourcePrefix
              htargetPrefix hsourceSuffix htargetSuffix
        have hcross := CrossCentralExactFaceCutState.cross_eq_of_trails_eq
          circuit.first.source third.source htrails.1 htrails.2.1
        have hcode : circuit.first.source.rigidCode =
            third.source.rigidCode :=
          (CrossCentralExactFaceCutState.rigidCode_eq_iff _ _).2
            ⟨hcross, htrails.1, htrails.2.1⟩
        exact (hminimal.rigidCode_ne_of_split circuit.first third []
          [second] after (by simp [hrestEq])).elim hcode
  rcases heven with ⟨half, hhalf⟩
  omega

end CrossCentralExactFaceCertifiedRebaseCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
