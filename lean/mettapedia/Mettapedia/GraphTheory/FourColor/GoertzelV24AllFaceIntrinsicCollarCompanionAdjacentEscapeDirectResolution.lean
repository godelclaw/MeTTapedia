import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicCollarCompanionAdjacentEscapeComponentFusionTargetCollarResolution

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

namespace GoertzelV24FourDefectBoundary

/-- Switching ports zero and one of the canonical adjacent-pair word makes
the boundary word constant at its second color. -/
theorem boundaryKempeSwap_zeroOne_constant_of_adjacent01_23
    (word : SquareBoundaryWord) (hadjacent : word.Adjacent01_23) :
    ∀ port : Fin 4,
      boundaryKempeSwap (word 0) (word 2) {0, 1} word port = word 2 := by
  intro port
  fin_cases port
  · simp [boundaryKempeSwap]
  · simp [boundaryKempeSwap]
    rw [← hadjacent.1]
    exact Equiv.swap_apply_left _ _
  · rfl
  · exact hadjacent.2.1.symm

end GoertzelV24FourDefectBoundary

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- In a vertex-minimal uncolorable cubic sphere, four selected boundary
requests force the exact two same-side Kempe components, retaining their
component identities rather than only their reachability partition. -/
theorem hasTwoSameSideKempeCutProfile_of_selected_colorWord_of_minimal
    {graphData : Data G}
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (data : AdjacentPairData G)
    (C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color)
    (hC : IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) C)
    {a b : Color} (hab : ValidColorPair a b)
    (hselected : ∀ port : Fin 4,
      data.degreeTwoBoundaryData.colorWord C port = a ∨
        data.degreeTwoBoundaryData.colorWord C port = b) :
    data.degreeTwoBoundaryData.HasTwoSameSideKempeCutProfile C a b := by
  let boundary := data.degreeTwoBoundaryData
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal
  have hwell := data.degreeTwoBoundaryData_wellFormed hcubic
  have hpaired :
      ∀ component : (C.bicoloredSubgraph a b).ConnectedComponent,
        (boundary.KempeComponentMeetsPort C a b component 0 ↔
          boundary.KempeComponentMeetsPort C a b component 1) ∧
        (boundary.KempeComponentMeetsPort C a b component 2 ↔
          boundary.KempeComponentMeetsPort C a b component 3) := by
    intro component
    exact ⟨
      data.kempeComponentMeetsPort_zero_iff_one_of_selected_request
        hcubic hnotColorable C hC hab component (hselected 0),
      data.kempeComponentMeetsPort_two_iff_three_of_selected_request
        hcubic hnotColorable C hC hab component (hselected 2)⟩
  exact boundary.exists_two_sameSide_kempeComponents
    hwell C hab hselected hpaired

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

namespace GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
namespace RotationOrderedCyclicKempeFusionChainNormalForm

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}
  {normal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}

attribute [local instance]
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.fusionFaceNetworkGraphEdgeSetDecidableEq
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.fusionFaceNetworkRetainedVertexFintype
  GoertzelV24AdjacentPairInsertion.AdjacentPairData.fusionFaceNetworkRetainedVertexDecidableEq

namespace KempeOrbitAdjacentEscape

variable (escape : normal.KempeOrbitAdjacentEscape)

/-- Switching the first exact same-side component of an adjacent escape
produces an all-equal coloring in one genuine Kempe step, hence a fully
resolved fusion normal form. -/
theorem nonempty_resolvedSameBaseKempeStep :
    Nonempty (normal.ResolvedSameBaseKempeStep escape) := by
  let data := RecoveredRotationOrderedData graphData minimal baseData
  let deleted := DeletedAdjacentPairGraph G data.firstVertex data.secondVertex
  let boundary := data.degreeTwoBoundaryData
  let firstColor := boundary.colorWord escape.coloring 0
  let secondColor := boundary.colorWord escape.coloring 2
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal
  have hwell := data.degreeTwoBoundaryData_wellFormed hcubic
  have hpair : ValidColorPair firstColor secondColor := by
    exact ⟨boundary.colorWord_ne_zero hwell escape.coloring 0,
      boundary.colorWord_ne_zero hwell escape.coloring 2,
      escape.boundary_adjacent01_23.2.2⟩
  have hselected : ∀ port : Fin 4,
      boundary.colorWord escape.coloring port = firstColor ∨
        boundary.colorWord escape.coloring port = secondColor := by
    intro port
    fin_cases port
    · exact Or.inl rfl
    · exact Or.inl escape.boundary_adjacent01_23.1.symm
    · exact Or.inr rfl
    · exact Or.inr escape.boundary_adjacent01_23.2.1.symm
  have hprofile : boundary.HasTwoSameSideKempeCutProfile
      escape.coloring firstColor secondColor :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.hasTwoSameSideKempeCutProfile_of_selected_colorWord_of_minimal
      minimal data escape.coloring escape.isTait hpair hselected
  rcases hprofile with
    ⟨firstComponent, _secondComponent, _hne,
      hfirstSupport, _hsecondSupport, _hexhaust⟩
  let successorColoring := escape.coloring.swapOnKempeComponent
    firstColor secondColor firstComponent
  have hsuccessorTait : IsTaitEdgeColoring deleted successorColoring :=
    GoertzelV24FramedTrail.isTaitEdgeColoring_swapOnKempeComponent
      escape.isTait hpair firstComponent
  have honeStep : deleted.EdgeKempeStep escape.coloring successorColoring :=
    deleted.edgeKempeStep_swapOnKempeComponent escape.coloring
      firstColor secondColor firstComponent
  have hboundaryWord : boundary.colorWord successorColoring =
      boundaryKempeSwap firstColor secondColor {0, 1}
        (boundary.colorWord escape.coloring) := by
    change boundary.colorWord
        (escape.coloring.swapOnKempeComponent
          firstColor secondColor firstComponent) = _
    rw [boundary.colorWord_swapOnKempeComponent_eq_boundaryKempeSwap
      escape.coloring hpair firstComponent, hfirstSupport]
  have hconstant : ∀ port : Fin 4,
      boundary.colorWord successorColoring port = secondColor := by
    intro port
    rw [hboundaryWord]
    exact boundaryKempeSwap_zeroOne_constant_of_adjacent01_23
      (boundary.colorWord escape.coloring)
        escape.boundary_adjacent01_23 port
  have hallEqual : SquareBoundaryWord.AllEqual
      (boundary.colorWord successorColoring) :=
    ⟨(hconstant 0).trans (hconstant 1).symm,
      (hconstant 1).trans (hconstant 2).symm,
      (hconstant 2).trans (hconstant 3).symm⟩
  have hstepClosure : successorColoring ∈
      deleted.EdgeKempeClosure escape.coloring :=
    deleted.mem_edgeKempeClosure_of_step
      (deleted.mem_edgeKempeClosure_self escape.coloring) honeStep
  have hfromAllEqual : successorColoring ∈
      deleted.EdgeKempeClosure normal.recoloring :=
    deleted.edgeKempeClosure_subset_of_mem
      escape.reachable_from_allEqual hstepClosure
  have hfromProfile : successorColoring ∈
      deleted.EdgeKempeClosure normal.profile.coloring :=
    deleted.edgeKempeClosure_subset_of_mem
      escape.reachable_from_profile hstepClosure
  rcases GoertzelV24FourEdgeCutKempeEscape.exists_validColorPair_with_first_of_ne_zero
      hpair.2.1 with
    ⟨otherColor, hotherPair⟩
  rcases data.exists_two_evenKempeFusionLenses_of_constant_colorWord
      hcubic hnotColorable successorColoring hsuccessorTait
        hotherPair hconstant with ⟨firstLens, secondLens⟩
  let successor : normal.AllEqualFusionSuccessor := {
    coloring := successorColoring
    isTait := hsuccessorTait
    boundary_allEqual := hallEqual
    reachable_from_allEqual := hfromAllEqual
    reachable_from_profile := hfromProfile
    constant := secondColor
    other := otherColor
    validPair := hotherPair
    boundary_constant := hconstant
    lens01 := firstLens
    lens23 := secondLens }
  rcases successor.exists_resolvedNormalForm with
    ⟨successorNormal, hrecoloring, hprofileColoring⟩
  refine ⟨{
    successorNormal := successorNormal
    oneStep := ?_
    profileColoring_eq_recoloring :=
      hprofileColoring.trans hrecoloring.symm
    outcome := successorNormal.terminalFusion_or_certifiedRebasePumpingLaunch }⟩
  rw [hrecoloring]
  exact honeStep

end KempeOrbitAdjacentEscape
end RotationOrderedCyclicKempeFusionChainNormalForm
end GoertzelV24RecoveredAdjacentPairFusionChainNormalForm

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

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
  {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
    graphData minimal baseData}

/-- Every canonical adjacent escape is already a certified resolved-fusion
endpoint: one exact same-side component switch reaches an all-equal fusion
normal form. -/
theorem certifiedAdjacentEscapeTerminal_resolvedFusion
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (escape : sourceNormal.KempeOrbitAdjacentEscape) :
    CertifiedAdjacentEscapeTerminal collar escape := by
  rcases escape.nonempty_resolvedSameBaseKempeStep with ⟨step⟩
  exact .resolvedFusion step

end IntrinsicShortTargetEscapeCollar
end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end
end Mettapedia.GraphTheory.FourColor
