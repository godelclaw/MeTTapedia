import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRemoteDualCycleReentryOrbit
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitPortPairingReductionKempeEscape
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeSwitchSquare

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24FourDefectBoundary
open GoertzelV24FourEdgeCutKempeEscape
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
open GoertzelV24RotationEdgeBridge
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24RecoveredAdjacentPairFusionChainNormalForm

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

namespace RotationOrderedCyclicKempeFusionChainNormalForm

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

/-- The strict adjacent boundary state obtained from the all-equal state of
a fusion normal form by reversible Kempe switching. -/
structure KempeOrbitAdjacentEscape
    (normal : RotationOrderedCyclicKempeFusionChainNormalForm graphData
      minimal baseData) where
  coloring : (DeletedAdjacentPairGraph G
    (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
    (RecoveredRotationOrderedData graphData minimal baseData).secondVertex).EdgeColoring Color
  isTait : IsTaitEdgeColoring
    (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
      (RecoveredRotationOrderedData graphData minimal baseData).secondVertex)
    coloring
  boundary_adjacent01_23 : SquareBoundaryWord.Adjacent01_23
    ((RecoveredRotationOrderedData graphData minimal
      baseData).degreeTwoBoundaryData.colorWord coloring)
  reachable_from_allEqual : coloring ∈
    (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
      (RecoveredRotationOrderedData graphData minimal baseData).secondVertex).EdgeKempeClosure
        normal.recoloring
  same_kempeClosure_as_allEqual :
    (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
      (RecoveredRotationOrderedData graphData minimal baseData).secondVertex).EdgeKempeClosure
        normal.recoloring =
    (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
      (RecoveredRotationOrderedData graphData minimal baseData).secondVertex).EdgeKempeClosure
        coloring
  reachable_from_profile : coloring ∈
    (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal baseData).firstVertex
      (RecoveredRotationOrderedData graphData minimal baseData).secondVertex).EdgeKempeClosure
        normal.profile.coloring

/-- Every rotation-ordered fusion normal form carries an adjacent boundary
state in the same Kempe orbit as its all-equal recoloring and in the Kempe
closure of its original profile coloring. -/
theorem nonempty_kempeOrbitAdjacentEscape
    (normal : RotationOrderedCyclicKempeFusionChainNormalForm graphData
      minimal baseData) :
    Nonempty normal.KempeOrbitAdjacentEscape := by
  let data := RecoveredRotationOrderedData graphData minimal baseData
  have hnoOppositeTrails :
      ∀ (firstTrail : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.degreeTwoBoundaryData.defectVertex 0)
            (data.degreeTwoBoundaryData.defectVertex 2))
        (secondTrail : (DeletedAdjacentPairGraph G data.firstVertex
          data.secondVertex).Walk
            (data.degreeTwoBoundaryData.defectVertex 1)
            (data.degreeTwoBoundaryData.defectVertex 3)),
        firstTrail.IsTrail → secondTrail.IsTrail →
          firstTrail.edges.Disjoint secondTrail.edges → False := by
    intro firstTrail secondTrail hfirst hsecond hdisjoint
    exact data.no_edge_disjoint_opposite_retained_trails_of_order
      graphData minimal normal.profile.portsCyclic firstTrail secondTrail
        hfirst hsecond hdisjoint
  obtain ⟨escape, hresult⟩ :=
    exists_adjacent_kempe_successor_of_no_disjoint_opposite_trails
      data.degreeTwoBoundaryData normal.profile.boundaryWellFormed
        normal.recoloring normal.recoloring_isTait normal.boundary_constant
          hnoOppositeTrails
  have hTait := hresult.1
  have hAdjacent := hresult.2.1
  have hreachable := hresult.2.2
  have hcubic : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 :=
    incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      graphData minimal.spherical.cubic
  have hnotColorable :
      ¬ ∃ ambientColoring : G.EdgeColoring Color,
          IsTaitEdgeColoring G ambientColoring :=
    graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
      graphData minimal
  have hsameSide :=
    GoertzelV24AdjacentPairInsertion.AdjacentPairData.sameSidePairs_of_not_taitColorable
      data hcubic hnotColorable escape hTait
  have hcanonical : SquareBoundaryWord.Adjacent01_23
      (data.degreeTwoBoundaryData.colorWord escape) := by
    exact Or.elim hAdjacent id (fun halternate => False.elim
      (halternate.2.2 (hsameSide.1.symm.trans halternate.2.1.symm)))
  have hsameClosure :
      (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).EdgeKempeClosure normal.recoloring =
      (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).EdgeKempeClosure escape :=
    SimpleGraph.Coloring.kempeClosure_eq_of_mem hreachable
  have hfromProfile : escape ∈
      (DeletedAdjacentPairGraph G data.firstVertex
        data.secondVertex).EdgeKempeClosure normal.profile.coloring :=
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).edgeKempeClosure_subset_of_mem
      normal.recoloring_mem_kempeClosure hreachable
  exact ⟨{
    coloring := escape
    isTait := hTait
    boundary_adjacent01_23 := hcanonical
    reachable_from_allEqual := hreachable
    same_kempeClosure_as_allEqual := hsameClosure
    reachable_from_profile := hfromProfile }⟩

end RotationOrderedCyclicKempeFusionChainNormalForm

/-- A named adjacent pair carries both a complete fusion outcome and the
reversible all-equal-to-adjacent Kempe state of the same normal form. -/
def HasRotationOrderedFusionKempeOrbitEscape
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (first second : V) : Prop :=
  ∃ baseData : AdjacentPairData G,
    baseData.firstVertex = first ∧
    baseData.secondVertex = second ∧
    ∃ normal : RotationOrderedCyclicKempeFusionChainNormalForm
        graphData minimal baseData,
      (normal.TerminalFusionOutcome ∨
        normal.CertifiedRebasePumpingLaunch) ∧
      Nonempty normal.KempeOrbitAdjacentEscape

/-- The complete terminal-or-rebase package of a named adjacent pair
therefore retains an actual reversible Kempe escape state. -/
theorem hasRotationOrderedFusionKempeOrbitEscape_of_terminalOrRebasePumping
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {first second : V}
    (fusion : HasRotationOrderedFusionTerminalOrRebasePumping
      graphData minimal first second) :
    HasRotationOrderedFusionKempeOrbitEscape
      graphData minimal first second := by
  rcases fusion with ⟨baseData, hfirst, hsecond, normal, houtcome⟩
  exact ⟨baseData, hfirst, hsecond, normal, houtcome,
    normal.nonempty_kempeOrbitAdjacentEscape⟩

end GoertzelV24RecoveredAdjacentPairFusionChainNormalForm

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm

/-- Every cross-face restart lands at a literal adjacent pair whose target
normal form carries the reversible planar Kempe escape state. -/
theorem CrossFaceAdjacentPairReentry.target_hasRotationOrderedFusionKempeOrbitEscape
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {baseData : AdjacentPairData G}
    {targetEdge : G.edgeSet}
    (reentry : CrossFaceAdjacentPairReentry graphData minimal baseData
      targetEdge) :
    ∃ first second : V,
      first ≠ second ∧ G.Adj first second ∧
        targetEdge.1 = s(first, second) ∧
        HasRotationOrderedFusionKempeOrbitEscape
          graphData minimal first second := by
  rcases reentry.target_fusion with
    ⟨first, second, hne, hadj, hedge, hfusion⟩
  exact ⟨first, second, hne, hadj, hedge,
    hasRotationOrderedFusionKempeOrbitEscape_of_terminalOrRebasePumping
      graphData minimal hfusion⟩

/-- Hence every directed cross-face orbit step lands on an oriented edge
with a complete same-base Kempe-orbit escape package. -/
theorem RotationOrderedFusionCrossFaceDartReentry.target_hasRotationOrderedFusionKempeOrbitEscape
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {source target : G.Dart}
    (reentry : RotationOrderedFusionCrossFaceDartReentry graphData minimal
      source target) :
    HasRotationOrderedFusionKempeOrbitEscape
      graphData minimal target.fst target.snd := by
  rcases reentry with
    ⟨_baseData, _targetEdge, _hsource, _htarget, _hedge, hfusion⟩
  exact
    hasRotationOrderedFusionKempeOrbitEscape_of_terminalOrRebasePumping
      graphData minimal hfusion

/-- The state-enriched cross-face relation records both the geometric
re-entry and the reversible Kempe-orbit package at its target dart. -/
def RotationOrderedFusionCrossFaceDartKempeOrbitReentry
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (source target : G.Dart) : Prop :=
  RotationOrderedFusionCrossFaceDartReentry graphData minimal source target ∧
    HasRotationOrderedFusionKempeOrbitEscape
      graphData minimal target.fst target.snd

/-- Every geometric directed re-entry canonically refines to the
state-enriched relation. -/
theorem RotationOrderedFusionCrossFaceDartReentry.toKempeOrbitReentry
    {graphData : Data G}
    {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
    {source target : G.Dart}
    (reentry : RotationOrderedFusionCrossFaceDartReentry graphData minimal
      source target) :
    RotationOrderedFusionCrossFaceDartKempeOrbitReentry graphData minimal
      source target :=
  ⟨reentry, reentry.target_hasRotationOrderedFusionKempeOrbitEscape⟩

/-- Starting at any dart, the all-face machine reaches a structural target
or a nonempty closed cross-face orbit in which every step retains a genuine
same-base Kempe escape state at its target. -/
theorem exists_reachable_rotationOrderedFusionStructuralTarget_or_crossFaceDartKempeOrbitReentryCycle
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (start : G.Dart) :
    (∃ finish : G.Dart,
        Relation.ReflTransGen
            (RotationOrderedFusionCrossFaceDartKempeOrbitReentry
              graphData minimal) start finish ∧
          RotationOrderedFusionStructuralTargetAtDart graphData minimal
            finish) ∨
      ∃ cycleDart : G.Dart,
        Relation.ReflTransGen
            (RotationOrderedFusionCrossFaceDartKempeOrbitReentry
              graphData minimal) start cycleDart ∧
          Relation.TransGen
            (RotationOrderedFusionCrossFaceDartKempeOrbitReentry
              graphData minimal) cycleDart cycleDart := by
  let refineStep := fun source target
      (step : RotationOrderedFusionCrossFaceDartReentry graphData minimal
        source target) => step.toKempeOrbitReentry
  rcases
      exists_reachable_rotationOrderedFusionStructuralTarget_or_crossFaceDartReentryCycle
        graphData minimal start with
    hterminal | hcycle
  · rcases hterminal with ⟨finish, hreach, hfinish⟩
    exact Or.inl ⟨finish, hreach.mono refineStep, hfinish⟩
  · rcases hcycle with ⟨cycleDart, hreach, hclosed⟩
    exact Or.inr ⟨cycleDart, hreach.mono refineStep,
      hclosed.mono refineStep⟩

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
