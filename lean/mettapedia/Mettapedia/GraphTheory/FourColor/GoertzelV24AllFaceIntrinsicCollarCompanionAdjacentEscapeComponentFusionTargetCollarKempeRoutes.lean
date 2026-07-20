import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentFusionTargetCollarMatrix
import Mettapedia.GraphTheory.FourColor.GoertzelV24KempePortPrimalTrail

set_option autoImplicit false

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24CorridorPumping
open GoertzelV24FourDefectBoundary
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Reverse the displayed order of a selected color pair without changing
the underlying vertices or adjacencies of its bicolored subgraph. -/
def SimpleGraph.Coloring.bicoloredSwapHom
    {W α : Type*} {H : SimpleGraph W}
    (C : H.Coloring α) (a b : α) :
    C.bicoloredSubgraph b a →g C.bicoloredSubgraph a b where
  toFun vertex := ⟨vertex.1, vertex.2.elim Or.inr Or.inl⟩
  map_rel' := fun hadj => hadj

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- When all four boundary requests lie in one valid color pair,
uncolorability forces exactly the two cyclic same-side Kempe components. -/
theorem hasSameSideKempeReachabilityProfile_of_selected_colorWord
    (data : AdjacentPairData G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    {a b : Color} (hab : ValidColorPair a b)
    (hselected : ∀ port : Fin 4,
      data.degreeTwoBoundaryData.colorWord C port = a ∨
        data.degreeTwoBoundaryData.colorWord C port = b) :
    data.degreeTwoBoundaryData.HasSameSideKempeReachabilityProfile
      C a b := by
  let boundary := data.degreeTwoBoundaryData
  have hwell := data.degreeTwoBoundaryData_wellFormed hcubic
  have hpaired :
      ∀ K : (C.bicoloredSubgraph a b).ConnectedComponent,
        (boundary.KempeComponentMeetsPort C a b K 0 ↔
          boundary.KempeComponentMeetsPort C a b K 1) ∧
        (boundary.KempeComponentMeetsPort C a b K 2 ↔
          boundary.KempeComponentMeetsPort C a b K 3) := by
    intro K
    exact ⟨
      data.kempeComponentMeetsPort_zero_iff_one_of_selected_request
        hcubic hnotColorable C hC hab K (hselected 0),
      data.kempeComponentMeetsPort_two_iff_three_of_selected_request
        hcubic hnotColorable C hC hab K (hselected 2)⟩
  have hprofile : boundary.HasTwoSameSideKempeCutProfile C a b :=
    boundary.exists_two_sameSide_kempeComponents
      hwell C hab hselected hpaired
  exact boundary.hasSameSideKempeReachabilityProfile_of_twoComponentProfile
    C a b hprofile

/-- Equal selected requests at two connected ports give a simple even
Kempe route whose terminal edges carry the other selected color. -/
theorem nonempty_evenKempePortPath_of_equal_selected_requests
    {portCount : Nat}
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (data : DegreeTwoBoundaryData H portCount)
    (hdata : data.WellFormed)
    (C : H.EdgeColoring Color) (hC : IsTaitEdgeColoring H C)
    {a b : Color} (hab : ValidColorPair a b)
    (left right : Fin portCount)
    (hleft : data.colorWord C left = a)
    (hright : data.colorWord C right = a)
    (hconnected : data.KempePortsConnected C a b left right) :
    Nonempty (data.EvenKempePortPath C a b left right) := by
  rcases (data.hasSimpleKempePortPath_iff_kempePortsConnected
      C a b left right).2 hconnected with
    ⟨leftEdge, rightEdge, leftIncident, rightIncident, path, isPath⟩
  have leftColor : C leftEdge.1 = b :=
    data.incident_bicolored_edge_color_eq_second_of_colorWord_eq_first
      hdata C hC hab left hleft leftIncident leftEdge.2
  have rightColor : C rightEdge.1 = b :=
    data.incident_bicolored_edge_color_eq_second_of_colorWord_eq_first
      hdata C hC hab right hright rightIncident rightEdge.2
  have evenLength : Even path.length :=
    C.bicoloredWalk_even_length_of_endpoint_colors_eq
      a b hab.2.2 path (leftColor.trans rightColor.symm)
  exact ⟨{
    leftEdge := leftEdge
    rightEdge := rightEdge
    leftIncident := leftIncident
    rightIncident := rightIncident
    leftColor := leftColor
    rightColor := rightColor
    path := path
    isPath := isPath
    evenLength := evenLength }⟩

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

namespace IntrinsicShortTargetEscapeCollar

variable {cycle :
    CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle rebaseCircuit}
  {targetEdge : G.edgeSet}
  (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)

/-- The target escape's request on ports `0,1`. -/
def targetOwnFirstColor : Color :=
  collar.targetData.degreeTwoBoundaryData.colorWord
    collar.targetEscape.coloring 0

/-- The target escape's distinct request on ports `2,3`. -/
def targetOwnSecondColor : Color :=
  collar.targetData.degreeTwoBoundaryData.colorWord
    collar.targetEscape.coloring 2

/-- The two target side requests are a valid ordered color pair. -/
theorem targetOwnValidColorPair :
    ValidColorPair collar.targetOwnFirstColor
      collar.targetOwnSecondColor := by
  exact ⟨collar.targetOwnBoundaryWord_nonzero.1,
    collar.targetOwnBoundaryWord_nonzero.2.2.1,
    collar.targetEscape.boundary_adjacent01_23.2.2⟩

/-- The same requests in the reverse order are also a valid pair. -/
theorem targetOwnValidColorPair_symm :
    ValidColorPair collar.targetOwnSecondColor
      collar.targetOwnFirstColor := by
  exact ⟨collar.targetOwnValidColorPair.2.1,
    collar.targetOwnValidColorPair.1,
    collar.targetOwnValidColorPair.2.2.symm⟩

/-- Every target boundary request lies in the ordered pair of its two
same-side request colors. -/
theorem targetOwnColorWord_selected (port : Fin 4) :
    collar.targetData.degreeTwoBoundaryData.colorWord
        collar.targetEscape.coloring port = collar.targetOwnFirstColor ∨
      collar.targetData.degreeTwoBoundaryData.colorWord
        collar.targetEscape.coloring port = collar.targetOwnSecondColor := by
  fin_cases port
  · exact Or.inl rfl
  · exact Or.inl collar.targetEscape.boundary_adjacent01_23.1.symm
  · exact Or.inr rfl
  · exact Or.inr collar.targetEscape.boundary_adjacent01_23.2.1.symm

/-- The target escape has exactly the same-side reachability partition
for its two request colors. -/
theorem targetOwnHasSameSideKempeReachabilityProfile :
    collar.targetData.degreeTwoBoundaryData.HasSameSideKempeReachabilityProfile
      collar.targetEscape.coloring collar.targetOwnFirstColor
        collar.targetOwnSecondColor := by
  apply hasSameSideKempeReachabilityProfile_of_selected_colorWord
    collar.targetData
  · exact incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  · exact graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal
  · exact collar.targetEscape.isTait
  · exact collar.targetOwnValidColorPair
  · exact collar.targetOwnColorWord_selected

/-- The same reachability partition is available with the two colors
listed in reverse order. -/
theorem targetOwnHasSameSideKempeReachabilityProfile_symm :
    collar.targetData.degreeTwoBoundaryData.HasSameSideKempeReachabilityProfile
      collar.targetEscape.coloring collar.targetOwnSecondColor
        collar.targetOwnFirstColor := by
  apply hasSameSideKempeReachabilityProfile_of_selected_colorWord
    collar.targetData
  · exact incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  · exact graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal
  · exact collar.targetEscape.isTait
  · exact collar.targetOwnValidColorPair_symm
  · intro port
    rcases collar.targetOwnColorWord_selected port with hfirst | hsecond
    · exact Or.inr hfirst
    · exact Or.inl hsecond

/-- The two genuine same-side Kempe routes inside the target-pair
deletion. Their color order is chosen so that the terminal edges carry the
second color in each route. -/
structure TargetOwnSameSideKempeRoutes where
  firstRoute : collar.targetData.degreeTwoBoundaryData.EvenKempePortPath
    collar.targetEscape.coloring collar.targetOwnFirstColor
      collar.targetOwnSecondColor 0 1
  secondRoute : collar.targetData.degreeTwoBoundaryData.EvenKempePortPath
    collar.targetEscape.coloring collar.targetOwnSecondColor
      collar.targetOwnFirstColor 2 3

/-- The target escape always supplies both same-side Kempe routes. -/
theorem nonempty_targetOwnSameSideKempeRoutes :
    Nonempty collar.TargetOwnSameSideKempeRoutes := by
  let boundary := collar.targetData.degreeTwoBoundaryData
  let coloring := collar.targetEscape.coloring
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hwell := collar.targetData.degreeTwoBoundaryData_wellFormed hcubic
  have connected01 : boundary.KempePortsConnected coloring
      collar.targetOwnFirstColor collar.targetOwnSecondColor 0 1 :=
    (collar.targetOwnHasSameSideKempeReachabilityProfile 0 1).2 (by simp)
  have connected23 : boundary.KempePortsConnected coloring
      collar.targetOwnSecondColor collar.targetOwnFirstColor 2 3 :=
    (collar.targetOwnHasSameSideKempeReachabilityProfile_symm 2 3).2
      (by simp)
  rcases nonempty_evenKempePortPath_of_equal_selected_requests
      boundary hwell coloring collar.targetEscape.isTait
      collar.targetOwnValidColorPair 0 1 rfl
      collar.targetEscape.boundary_adjacent01_23.1.symm connected01 with
    ⟨firstRoute⟩
  rcases nonempty_evenKempePortPath_of_equal_selected_requests
      boundary hwell coloring collar.targetEscape.isTait
      collar.targetOwnValidColorPair_symm 2 3 rfl
      collar.targetEscape.boundary_adjacent01_23.2.1.symm connected23 with
    ⟨secondRoute⟩
  exact ⟨⟨firstRoute, secondRoute⟩⟩

namespace TargetOwnSameSideKempeRoutes

variable (routes : collar.TargetOwnSameSideKempeRoutes)

/-- The two same-side routes lie in the two distinct components of the
same unordered bicolored subgraph, so their ambient line-path supports
are disjoint. -/
theorem ambientPath_support_disjoint :
    routes.firstRoute.ambientPath.support.Disjoint
      routes.secondRoute.ambientPath.support := by
  rw [List.disjoint_left]
  intro edge hfirst hsecond
  let coloring := collar.targetEscape.coloring
  let firstColor := collar.targetOwnFirstColor
  let secondColor := collar.targetOwnSecondColor
  rcases (routes.firstRoute.mem_ambientPath_support_iff edge).1 hfirst with
    ⟨hfirstSelected, hfirstPath⟩
  rcases (routes.secondRoute.mem_ambientPath_support_iff edge).1 hsecond with
    ⟨hsecondSelected, hsecondPath⟩
  let sharedFirst : coloring.bicoloredSet firstColor secondColor :=
    ⟨edge, hfirstSelected⟩
  let sharedSecond : coloring.bicoloredSet secondColor firstColor :=
    ⟨edge, hsecondSelected⟩
  have sharedFirst_mem : sharedFirst ∈ routes.firstRoute.path.support := by
    simpa only [sharedFirst] using hfirstPath
  have sharedSecond_mem : sharedSecond ∈
      routes.secondRoute.path.support := by
    simpa only [sharedSecond] using hsecondPath
  have firstReachable :
      (coloring.bicoloredSubgraph firstColor secondColor).Reachable
        routes.firstRoute.leftEdge sharedFirst :=
    (routes.firstRoute.path.takeUntil sharedFirst sharedFirst_mem).reachable
  have secondReachableReversed :
      (coloring.bicoloredSubgraph secondColor firstColor).Reachable
        routes.secondRoute.leftEdge sharedSecond :=
    (routes.secondRoute.path.takeUntil sharedSecond
      sharedSecond_mem).reachable
  let swapHom := SimpleGraph.Coloring.bicoloredSwapHom
    coloring firstColor secondColor
  have secondReachable := secondReachableReversed.map swapHom
  have sharedToSecond :
      (coloring.bicoloredSubgraph firstColor secondColor).Reachable
        sharedFirst (swapHom routes.secondRoute.leftEdge) := by
    have shared_eq : swapHom sharedSecond = sharedFirst := by
      apply Subtype.ext
      rfl
    rw [← shared_eq]
    exact secondReachable.symm
  have connected02 :
      collar.targetData.degreeTwoBoundaryData.KempePortsConnected
        coloring firstColor secondColor 0 2 :=
    ⟨routes.firstRoute.leftEdge,
      swapHom routes.secondRoute.leftEdge,
      routes.firstRoute.leftIncident,
      routes.secondRoute.leftIncident,
      firstReachable.trans sharedToSecond⟩
  have hside :=
    (collar.targetOwnHasSameSideKempeReachabilityProfile 0 2).1
      connected02
  simp at hside

/-- The first Kempe route lifts to a primal trail between target defect
vertices `0` and `1`. -/
theorem exists_firstPrimalTrail :
    ∃ trail : (DeletedAdjacentPairGraph G
        collar.targetData.firstVertex collar.targetData.secondVertex).Walk
        (collar.targetData.degreeTwoBoundaryData.defectVertex 0)
        (collar.targetData.degreeTwoBoundaryData.defectVertex 1),
      trail.IsTrail ∧
        trail.edges = routes.firstRoute.ambientPath.support.map Subtype.val := by
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  apply routes.firstRoute.exists_primalTrail
    (collar.targetData.degreeTwoBoundaryData_wellFormed hcubic)
    collar.targetOwnValidColorPair
  · exact Or.inl rfl
  · exact Or.inl collar.targetEscape.boundary_adjacent01_23.1.symm
  · decide

/-- The second Kempe route lifts to a primal trail between target defect
vertices `2` and `3`. -/
theorem exists_secondPrimalTrail :
    ∃ trail : (DeletedAdjacentPairGraph G
        collar.targetData.firstVertex collar.targetData.secondVertex).Walk
        (collar.targetData.degreeTwoBoundaryData.defectVertex 2)
        (collar.targetData.degreeTwoBoundaryData.defectVertex 3),
      trail.IsTrail ∧
        trail.edges = routes.secondRoute.ambientPath.support.map Subtype.val := by
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  apply routes.secondRoute.exists_primalTrail
    (collar.targetData.degreeTwoBoundaryData_wellFormed hcubic)
    collar.targetOwnValidColorPair_symm
  · exact Or.inl rfl
  · exact Or.inl collar.targetEscape.boundary_adjacent01_23.2.1.symm
  · decide

end TargetOwnSameSideKempeRoutes

/-- The target deletion therefore contains actual edge-simple bypasses
for both boundary-pair passages through the removed adjacent pair. -/
theorem exists_targetOwnSameSideKempePrimalTrails :
    ∃ routes : collar.TargetOwnSameSideKempeRoutes,
      (∃ firstTrail : (DeletedAdjacentPairGraph G
          collar.targetData.firstVertex collar.targetData.secondVertex).Walk
          (collar.targetData.degreeTwoBoundaryData.defectVertex 0)
          (collar.targetData.degreeTwoBoundaryData.defectVertex 1),
        firstTrail.IsTrail ∧
          firstTrail.edges =
            routes.firstRoute.ambientPath.support.map Subtype.val) ∧
      (∃ secondTrail : (DeletedAdjacentPairGraph G
          collar.targetData.firstVertex collar.targetData.secondVertex).Walk
          (collar.targetData.degreeTwoBoundaryData.defectVertex 2)
          (collar.targetData.degreeTwoBoundaryData.defectVertex 3),
        secondTrail.IsTrail ∧
          secondTrail.edges =
            routes.secondRoute.ambientPath.support.map Subtype.val) := by
  rcases collar.nonempty_targetOwnSameSideKempeRoutes with ⟨routes⟩
  exact ⟨routes, routes.exists_firstPrimalTrail,
    routes.exists_secondPrimalTrail⟩

/-- The two target-deletion bypass trails may be chosen simultaneously
with disjoint edge lists. -/
theorem exists_targetOwnSameSideKempePrimalTrails_disjoint :
    ∃ (routes : collar.TargetOwnSameSideKempeRoutes)
      (firstTrail : (DeletedAdjacentPairGraph G
        collar.targetData.firstVertex collar.targetData.secondVertex).Walk
        (collar.targetData.degreeTwoBoundaryData.defectVertex 0)
        (collar.targetData.degreeTwoBoundaryData.defectVertex 1))
      (secondTrail : (DeletedAdjacentPairGraph G
        collar.targetData.firstVertex collar.targetData.secondVertex).Walk
        (collar.targetData.degreeTwoBoundaryData.defectVertex 2)
        (collar.targetData.degreeTwoBoundaryData.defectVertex 3)),
      firstTrail.IsTrail ∧
      secondTrail.IsTrail ∧
      firstTrail.edges =
        routes.firstRoute.ambientPath.support.map Subtype.val ∧
      secondTrail.edges =
        routes.secondRoute.ambientPath.support.map Subtype.val ∧
      firstTrail.edges.Disjoint secondTrail.edges := by
  rcases collar.nonempty_targetOwnSameSideKempeRoutes with ⟨routes⟩
  rcases routes.exists_firstPrimalTrail with
    ⟨firstTrail, firstIsTrail, firstEdges⟩
  rcases routes.exists_secondPrimalTrail with
    ⟨secondTrail, secondIsTrail, secondEdges⟩
  refine ⟨routes, firstTrail, secondTrail, firstIsTrail, secondIsTrail,
    firstEdges, secondEdges, ?_⟩
  rw [firstEdges, secondEdges]
  exact routes.ambientPath_support_disjoint.map Subtype.val_injective

/-- No target-own two-color component crosses from one side of the
removed adjacent pair to the other.  Thus every central collar passage is
the exact obstruction to replacing it by one of the two same-side Kempe
bypasses. -/
theorem not_targetOwnKempePortsConnected_cross
    (firstUsesOne secondUsesThree : Bool) :
    ¬ collar.targetData.degreeTwoBoundaryData.KempePortsConnected
      collar.targetEscape.coloring collar.targetOwnFirstColor
        collar.targetOwnSecondColor
        (TargetCollarTraversalClass.firstCrossPort firstUsesOne)
        (TargetCollarTraversalClass.secondCrossPort secondUsesThree) := by
  intro hconnected
  have hsameSide :=
    (collar.targetOwnHasSameSideKempeReachabilityProfile
      (TargetCollarTraversalClass.firstCrossPort firstUsesOne)
      (TargetCollarTraversalClass.secondCrossPort secondUsesThree)).1
      hconnected
  cases firstUsesOne <;> cases secondUsesThree <;>
    simp [TargetCollarTraversalClass.firstCrossPort,
      TargetCollarTraversalClass.secondCrossPort] at hsameSide

/-- Every target-collar traversal is now classified by the actual Kempe
geometry of the target deletion: the three noncentral classes have the two
simultaneously edge-disjoint same-side bypass trails, while a central class
selects a pair of ports that no target-own Kempe component connects. -/
theorem targetOwnSameSidePrimalTrails_or_crossObstruction
    (traversalClass : TargetCollarTraversalClass) :
    ((traversalClass = .firstBoundaryPair ∨
        traversalClass = .secondBoundaryPair ∨
        traversalClass = .bothBoundaryPairs) ∧
      ∃ (routes : collar.TargetOwnSameSideKempeRoutes)
        (firstTrail : (DeletedAdjacentPairGraph G
          collar.targetData.firstVertex collar.targetData.secondVertex).Walk
          (collar.targetData.degreeTwoBoundaryData.defectVertex 0)
          (collar.targetData.degreeTwoBoundaryData.defectVertex 1))
        (secondTrail : (DeletedAdjacentPairGraph G
          collar.targetData.firstVertex collar.targetData.secondVertex).Walk
          (collar.targetData.degreeTwoBoundaryData.defectVertex 2)
          (collar.targetData.degreeTwoBoundaryData.defectVertex 3)),
        firstTrail.IsTrail ∧ secondTrail.IsTrail ∧
        firstTrail.edges =
          routes.firstRoute.ambientPath.support.map Subtype.val ∧
        secondTrail.edges =
          routes.secondRoute.ambientPath.support.map Subtype.val ∧
        firstTrail.edges.Disjoint secondTrail.edges) ∨
    ∃ firstUsesOne secondUsesThree,
      traversalClass = .cross firstUsesOne secondUsesThree ∧
      ¬ collar.targetData.degreeTwoBoundaryData.KempePortsConnected
        collar.targetEscape.coloring collar.targetOwnFirstColor
          collar.targetOwnSecondColor
          (TargetCollarTraversalClass.firstCrossPort firstUsesOne)
          (TargetCollarTraversalClass.secondCrossPort secondUsesThree) := by
  cases traversalClass with
  | firstBoundaryPair =>
      exact Or.inl ⟨Or.inl rfl,
        collar.exists_targetOwnSameSideKempePrimalTrails_disjoint⟩
  | secondBoundaryPair =>
      exact Or.inl ⟨Or.inr (Or.inl rfl),
        collar.exists_targetOwnSameSideKempePrimalTrails_disjoint⟩
  | bothBoundaryPairs =>
      exact Or.inl ⟨Or.inr (Or.inr rfl),
        collar.exists_targetOwnSameSideKempePrimalTrails_disjoint⟩
  | cross firstUsesOne secondUsesThree =>
      exact Or.inr ⟨firstUsesOne, secondUsesThree, rfl,
        collar.not_targetOwnKempePortsConnected_cross
          firstUsesOne secondUsesThree⟩

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
