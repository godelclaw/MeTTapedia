import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceEscapeStateReentry
import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceIntrinsicShortCommonDiscrepancy
import Mettapedia.GraphTheory.FourColor.GoertzelV24InducedChainExtension

/-! Additive cancellation for closed all-face escape-state orbits. -/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FourDefectBoundary
open GoertzelV24InducedChainExtension
open GoertzelV24RecoveredAdjacentPairData
open GoertzelV24RecoveredAdjacentPairFusionChainNormalForm
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

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}

namespace RotationOrderedFusionEscapeColorState

/-- The ambient vertex predicate retained by a state's adjacent-pair
deletion. -/
abbrev retainedPredicate
    (state : RotationOrderedFusionEscapeColorState graphData minimal)
    (vertex : V) : Prop :=
  vertex ≠
      (RecoveredRotationOrderedData graphData minimal state.1).firstVertex ∧
    vertex ≠
      (RecoveredRotationOrderedData graphData minimal state.1).secondVertex

/-- Extend a state's actual escape coloring by zero across the six omitted
collar edges, producing one ambient color chain shared by every state. -/
def ambientColorChain
    (state : RotationOrderedFusionEscapeColorState graphData minimal) :
    G.edgeSet → Color :=
  inducedEdgeChainExtendZero G state.retainedPredicate state.2

@[simp]
theorem ambientColorChain_apply_inducedEdgeEmbedding
    (state : RotationOrderedFusionEscapeColorState graphData minimal)
    (edge : (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal state.1).firstVertex
      (RecoveredRotationOrderedData graphData minimal state.1).secondVertex).edgeSet) :
    state.ambientColorChain
        (inducedEdgeEmbedding G state.retainedPredicate edge) =
      state.2 edge :=
  inducedEdgeChainExtendZero_apply_inducedEdgeEmbedding
    G state.retainedPredicate state.2 edge

/-- On a retained edge, the state's ambient zero extension recovers its
literal escape color. -/
@[simp]
theorem ambientColorChain_apply_retainedEdgeToAmbientEdge
    (state : RotationOrderedFusionEscapeColorState graphData minimal)
    (edge : (DeletedAdjacentPairGraph G
      (RecoveredRotationOrderedData graphData minimal state.1).firstVertex
      (RecoveredRotationOrderedData graphData minimal state.1).secondVertex).edgeSet) :
    state.ambientColorChain
        (retainedEdgeToAmbientEdge
          (RecoveredRotationOrderedData graphData minimal state.1) edge) =
      state.2 edge := by
  exact state.ambientColorChain_apply_inducedEdgeEmbedding edge

/-- The ambient edge represented by an exact edge of an intrinsic collar's
four-vertex common deletion. -/
def commonCoreAmbientEdge
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (edge : collar.commonCore.edgeSet) : G.edgeSet :=
  retainedEdgeToAmbientEdge collar.sourceData
    (collar.commonEdgeInSource edge)

/-- Restricting the source state's ambient chain to the common core gives
the collar's source coloring literally. -/
@[simp]
theorem sourceAmbientColorChain_apply_commonCoreAmbientEdge
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : collar.commonCore.edgeSet) :
    (show RotationOrderedFusionEscapeColorState graphData minimal from
        ⟨baseData, sourceEscape.coloring⟩).ambientColorChain
          (commonCoreAmbientEdge collar edge) =
      collar.sourceCommonColoring sourceEscape edge := by
  exact ambientColorChain_apply_retainedEdgeToAmbientEdge
    (show RotationOrderedFusionEscapeColorState graphData minimal from
      ⟨baseData, sourceEscape.coloring⟩)
    (collar.commonEdgeInSource edge)

/-- Restricting the target state's ambient chain to the same common core
gives the collar's target coloring literally. -/
@[simp]
theorem targetAmbientColorChain_apply_commonCoreAmbientEdge
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (edge : collar.commonCore.edgeSet) :
    (show RotationOrderedFusionEscapeColorState graphData minimal from
        ⟨collar.targetBase, collar.targetEscape.coloring⟩).ambientColorChain
          (commonCoreAmbientEdge collar edge) =
      collar.targetCommonColoring edge := by
  rw [commonCoreAmbientEdge,
    collar.retainedEdgeToAmbientEdge_commonEdgeInSource_eq_target edge]
  exact ambientColorChain_apply_retainedEdgeToAmbientEdge
    (show RotationOrderedFusionEscapeColorState graphData minimal from
      ⟨collar.targetBase, collar.targetEscape.coloring⟩)
    (collar.commonEdgeInTarget edge)

/-- On the exact four-vertex common deletion, the sum of the aligned source
and target ambient chains is precisely the singleton collar discrepancy. -/
theorem alignedAmbientDiscrepancy_apply_commonCoreAmbientEdge
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape)
    (edge : collar.commonCore.edgeSet) :
    ((show RotationOrderedFusionEscapeColorState graphData minimal from
          ⟨baseData, sourceEscape.coloring⟩).ambientColorChain +
        (show RotationOrderedFusionEscapeColorState graphData minimal from
          ⟨collar.targetBase,
            collar.targetEscape.coloring⟩).ambientColorChain)
          (commonCoreAmbientEdge collar edge) =
      collar.commonDiscrepancy sourceEscape edge := by
  change
    (show RotationOrderedFusionEscapeColorState graphData minimal from
        ⟨baseData, sourceEscape.coloring⟩).ambientColorChain
          (commonCoreAmbientEdge collar edge) +
      (show RotationOrderedFusionEscapeColorState graphData minimal from
        ⟨collar.targetBase,
          collar.targetEscape.coloring⟩).ambientColorChain
          (commonCoreAmbientEdge collar edge) =
        collar.commonDiscrepancy sourceEscape edge
  rw [sourceAmbientColorChain_apply_commonCoreAmbientEdge,
    targetAmbientColorChain_apply_commonCoreAmbientEdge]
  rfl

/-- The aligned ambient discrepancy of an intrinsic singleton transition is
nonzero, because its restriction already contains the nonzero exact collar
discrepancy. -/
theorem alignedAmbientDiscrepancy_ne_zeroChain
    {baseData : AdjacentPairData G}
    {rebaseCircuit :
      CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    {targetEdge : G.edgeSet}
    {sourceNormal : RotationOrderedCyclicKempeFusionChainNormalForm
      graphData minimal baseData}
    (collar : cycle.IntrinsicShortTargetEscapeCollar targetEdge)
    (sourceEscape : sourceNormal.KempeOrbitAdjacentEscape) :
    (show G.edgeSet → Color from
        (show RotationOrderedFusionEscapeColorState graphData minimal from
            ⟨baseData, sourceEscape.coloring⟩).ambientColorChain +
          (show RotationOrderedFusionEscapeColorState graphData minimal from
            ⟨collar.targetBase,
              collar.targetEscape.coloring⟩).ambientColorChain) ≠
      zeroChain := by
  intro hzero
  rcases collar.commonDiscrepancy_support_nonempty sourceEscape with
    ⟨edge, hedge⟩
  have hvalue := congrFun hzero (commonCoreAmbientEdge collar edge)
  rw [alignedAmbientDiscrepancy_apply_commonCoreAmbientEdge
    collar sourceEscape edge] at hvalue
  exact (mem_support_iff.mp hedge) hvalue

/-- The additive discrepancy carried by one stateful reentry. -/
def reentryDiscrepancy
    (source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)) :
    G.edgeSet → Color :=
  source.1.ambientColorChain + target.1.ambientColorChain

/-- Every stateful reentry either carries a nonzero intrinsic singleton
discrepancy or is witnessed by the exact recovery geometry.  Thus the
algebraic obstruction is attached to the real recursive transition rather
than to a separately chosen collar. -/
theorem AdmissibleReentry.discrepancy_ne_zeroChain_or_recoveryGeometry
    {source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)}
    (step : AdmissibleReentry source target) :
    reentryDiscrepancy source target ≠ zeroChain ∨
      ∃ targetEdge : G.edgeSet,
        centralEdge
            (RecoveredRotationOrderedData graphData minimal source.1.1) ≠
          targetEdge ∧
        centralEdge
            (RecoveredRotationOrderedData graphData minimal target.1.1) =
          targetEdge ∧
        ∃ circuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
            minimal source.1.1,
          circuit.IsLengthMinimal ∧
            ∃ rotated : CrossCentralExactFaceCertifiedRebaseCircuit graphData
                minimal source.1.1,
              rotated.arcLength = circuit.arcLength ∧
                ∃ transfer : ClosureRecoveryFaceTransfer rotated,
                  targetEdge = transfer.recovery.edge := by
  rcases step with
    ⟨sourceNormal, _sourceLaunch, sourceEscape, hsourceColor, targetEdge,
      htargetNe, htargetCentral, geometry, _targetNormal, _targetOutcome,
      _targetEscape, _htargetColor⟩
  rcases geometry with
    ⟨circuit, _hminimal, cycle, _hintrinsic, collar, htargetState⟩ |
      ⟨circuit, hminimal, rotated, hlength, transfer, htargetEdge⟩
  · left
    have hsourceAmbient :
        source.1.ambientColorChain =
          (show RotationOrderedFusionEscapeColorState graphData minimal from
            ⟨source.1.1, sourceEscape.coloring⟩).ambientColorChain := by
      unfold ambientColorChain
      rw [hsourceColor]
    have htargetAmbient :
        target.1.ambientColorChain =
          (show RotationOrderedFusionEscapeColorState graphData minimal from
            ⟨collar.targetBase,
              collar.targetEscape.coloring⟩).ambientColorChain :=
      congrArg ambientColorChain htargetState
    rw [reentryDiscrepancy, hsourceAmbient, htargetAmbient]
    exact alignedAmbientDiscrepancy_ne_zeroChain collar sourceEscape
  · exact Or.inr ⟨targetEdge, htargetNe, htargetCentral, circuit,
      hminimal, rotated, hlength, transfer, htargetEdge⟩

/-- A transition chain together with the sum of its successive ambient
discrepancies.  Keeping the total as an index lets the proof stay inside
`Prop` while retaining the exact color chain. -/
inductive ReentryDiscrepancyChain :
    AdmissibleState (graphData := graphData) (minimal := minimal) →
    AdmissibleState (graphData := graphData) (minimal := minimal) →
    (G.edgeSet → Color) → Prop
  | single {source target}
      (step : AdmissibleReentry source target) :
      ReentryDiscrepancyChain source target
        (reentryDiscrepancy source target)
  | tail {source middle target total}
      (path : ReentryDiscrepancyChain source middle total)
      (step : AdmissibleReentry middle target) :
      ReentryDiscrepancyChain source target
        (total + reentryDiscrepancy middle target)

namespace ReentryDiscrepancyChain

/-- Every nonempty transition path has an exact accumulated discrepancy. -/
theorem exists_of_transGen
    {source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)}
    (path : Relation.TransGen
      (AdmissibleReentry (graphData := graphData) (minimal := minimal))
      source target) :
    ∃ total : G.edgeSet → Color,
      ReentryDiscrepancyChain source target total := by
  induction path with
  | single step =>
      exact ⟨reentryDiscrepancy _ _, .single step⟩
  | tail _ step ih =>
      rcases ih with ⟨total, htotal⟩
      exact ⟨total + reentryDiscrepancy _ _, .tail htotal step⟩

/-- Successive middle-state chains cancel in characteristic two: every
accumulated discrepancy is exactly the sum of the endpoint potentials. -/
theorem eq_ambientColorChain_add
    {source target :
      AdmissibleState (graphData := graphData) (minimal := minimal)}
    {total : G.edgeSet → Color}
    (path : ReentryDiscrepancyChain source target total) :
    total = source.1.ambientColorChain + target.1.ambientColorChain := by
  induction path with
  | single _ => rfl
  | tail path _ ih =>
      rw [ih]
      simp only [reentryDiscrepancy]
      rw [add_assoc, chain_add_self_add]

/-- The accumulated discrepancy of a nonempty closed escape-state orbit is
the zero ambient chain. -/
theorem eq_zero_of_closed
    {state :
      AdmissibleState (graphData := graphData) (minimal := minimal)}
    {total : G.edgeSet → Color}
    (path : ReentryDiscrepancyChain state state total) :
    total = 0 := by
  rw [path.eq_ambientColorChain_add]
  funext edge
  exact color_add_self _

/-- A closed transition orbit admits an exact discrepancy chain, and every
such chain has zero total. -/
theorem exists_eq_zero_of_transGen_cycle
    {state :
      AdmissibleState (graphData := graphData) (minimal := minimal)}
    (cycle : Relation.TransGen
      (AdmissibleReentry (graphData := graphData) (minimal := minimal))
      state state) :
    ∃ total : G.edgeSet → Color,
      ReentryDiscrepancyChain state state total ∧ total = 0 := by
  rcases exists_of_transGen cycle with ⟨total, path⟩
  exact ⟨total, path, path.eq_zero_of_closed⟩

/-- Every additive observable of a closed orbit's accumulated discrepancy
vanishes.  Hence any additive geometric monodromy on the same chain must
also vanish. -/
theorem additiveObservable_eq_zero_of_closed
    {state :
      AdmissibleState (graphData := graphData) (minimal := minimal)}
    {total : G.edgeSet → Color}
    (path : ReentryDiscrepancyChain state state total)
    {A : Type*} [AddCommMonoid A]
    (observable : (G.edgeSet → Color) →+ A) :
    observable total = 0 := by
  rw [path.eq_zero_of_closed]
  exact observable.map_zero

end ReentryDiscrepancyChain

end RotationOrderedFusionEscapeColorState

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
