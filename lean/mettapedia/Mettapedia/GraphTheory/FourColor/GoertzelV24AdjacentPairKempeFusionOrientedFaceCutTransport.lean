import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionFaceCutTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionRouteStateFaceCutTransport

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24FaceCutTransport
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

/-- The local transfer sends the nonselected exit label back to the
selected entry label. -/
@[simp] theorem FusionFaceSymbol.routeTransfer_not_exitTurn
    (symbol : FusionFaceSymbol) :
    symbol.routeTransfer (!symbol.exitTurn) = symbol.entryTurn := by
  rcases symbol with ⟨chirality, entryTurn, exitTurn⟩
  cases entryTurn <;> cases exitTurn <;>
    simp [FusionFaceSymbol.routeTransfer]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- The nonselected entry arm at a fusion site, expressed in the two
separate route orders. -/
def routeOrderedFusionEntryOtherState
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) :
    (Fin lens.fusionSiteCount × Bool) × Bool :=
  lens.fusionArmReindexing hab hac
    ((position, false),
      !(bOrderedFusionFaceSymbol graphData data lens hab hac position).entryTurn)

/-- The selected exit arm paired with the nonselected entry arm. -/
def routeOrderedFusionExitTurnState
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) :
    (Fin lens.fusionSiteCount × Bool) × Bool :=
  lens.fusionArmReindexing hab hac
    ((position, true),
      (bOrderedFusionFaceSymbol graphData data lens hab hac position).exitTurn)

/-- The nonselected exit arm at a fusion site. -/
def routeOrderedFusionExitOtherState
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) :
    (Fin lens.fusionSiteCount × Bool) × Bool :=
  lens.fusionArmReindexing hab hac
    ((position, true),
      !(bOrderedFusionFaceSymbol graphData data lens hab hac position).exitTurn)

/-- The selected entry arm paired with the nonselected exit arm. -/
def routeOrderedFusionEntryTurnState
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) :
    (Fin lens.fusionSiteCount × Bool) × Bool :=
  lens.fusionArmReindexing hab hac
    ((position, false),
      (bOrderedFusionFaceSymbol graphData data lens hab hac position).entryTurn)

/-- Reindexing a canonical arm state and then interpreting it recovers the
same physical ambient dart. -/
@[simp] theorem routeOrderedFusionArmDart_fusionArmReindexing
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (state : (Fin lens.fusionSiteCount × Bool) × Bool) :
    routeOrderedFusionArmDart data lens hab hac
        (lens.fusionArmReindexing hab hac state) =
      bIndexedFusionArmDart data lens hab hac state := by
  rw [routeOrderedFusionArmDart,
    (lens.fusionArmReindexing hab hac).symm_apply_apply]

@[simp] theorem routeOrderedFusionArmDart_entryOtherState
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) :
    routeOrderedFusionArmDart data lens hab hac
        (routeOrderedFusionEntryOtherState
          graphData data lens hab hac position) =
      fusionEntryOtherDart graphData data lens hab hac
        (lens.bFusionSiteAt position) := by
  rw [routeOrderedFusionEntryOtherState,
    routeOrderedFusionArmDart_fusionArmReindexing]
  simp [bIndexedFusionArmDart, bOrderedFusionFaceSymbol]

@[simp] theorem routeOrderedFusionArmDart_exitTurnState
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) :
    routeOrderedFusionArmDart data lens hab hac
        (routeOrderedFusionExitTurnState
          graphData data lens hab hac position) =
      fusionExitTurnDart graphData data lens hab hac
        (lens.bFusionSiteAt position) := by
  rw [routeOrderedFusionExitTurnState,
    routeOrderedFusionArmDart_fusionArmReindexing]
  simp [bIndexedFusionArmDart, bOrderedFusionFaceSymbol]

@[simp] theorem routeOrderedFusionArmDart_exitOtherState
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) :
    routeOrderedFusionArmDart data lens hab hac
        (routeOrderedFusionExitOtherState
          graphData data lens hab hac position) =
      fusionExitOtherDart graphData data lens hab hac
        (lens.bFusionSiteAt position) := by
  rw [routeOrderedFusionExitOtherState,
    routeOrderedFusionArmDart_fusionArmReindexing]
  simp [bIndexedFusionArmDart, bOrderedFusionFaceSymbol]

@[simp] theorem routeOrderedFusionArmDart_entryTurnState
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) :
    routeOrderedFusionArmDart data lens hab hac
        (routeOrderedFusionEntryTurnState
          graphData data lens hab hac position) =
      fusionEntryTurnDart graphData data lens hab hac
        (lens.bFusionSiteAt position) := by
  rw [routeOrderedFusionEntryTurnState,
    routeOrderedFusionArmDart_fusionArmReindexing]
  simp [bIndexedFusionArmDart, bOrderedFusionFaceSymbol]

/-- The conjugated finite crossing sends the nonselected entry state to
the selected exit state. -/
@[simp] theorem routeOrderedFusionFaceCrossing_entryOtherState
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) :
    routeOrderedFusionFaceCrossing graphData data lens hab hac
        (routeOrderedFusionEntryOtherState
          graphData data lens hab hac position) =
      routeOrderedFusionExitTurnState
        graphData data lens hab hac position := by
  rw [routeOrderedFusionEntryOtherState,
    routeOrderedFusionExitTurnState,
    routeOrderedFusionFaceCrossing_fusionArmReindexing]
  rw [Equiv.apply_eq_iff_eq]
  unfold EvenKempeFusionLens.fusionSiteCount at *
  rw [indexedFusionFaceCrossing_apply]
  simp

/-- The other directed crossing sends the nonselected exit state to the
selected entry state. -/
@[simp] theorem routeOrderedFusionFaceCrossing_exitOtherState
    (graphData : Data G)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) :
    routeOrderedFusionFaceCrossing graphData data lens hab hac
        (routeOrderedFusionExitOtherState
          graphData data lens hab hac position) =
      routeOrderedFusionEntryTurnState
        graphData data lens hab hac position := by
  rw [routeOrderedFusionExitOtherState,
    routeOrderedFusionEntryTurnState,
    routeOrderedFusionFaceCrossing_fusionArmReindexing]
  rw [Equiv.apply_eq_iff_eq]
  unfold EvenKempeFusionLens.fusionSiteCount at *
  rw [indexedFusionFaceCrossing_apply]
  simp

/-- The directed entry-side face arc has no orientation disjunction. -/
theorem phi_sq_alpha_routeOrderedFusionEntryOtherState_eq_exitTurnState
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (position : Fin lens.fusionSiteCount) :
    graphData.toRotationSystem.phi
        (graphData.toRotationSystem.phi
          (graphData.toRotationSystem.alpha
            (routeOrderedFusionArmDart data lens hab hac
              (routeOrderedFusionEntryOtherState
                graphData data lens hab hac position)))) =
      routeOrderedFusionArmDart data lens hab hac
        (routeOrderedFusionExitTurnState
          graphData data lens hab hac position) := by
  rw [routeOrderedFusionArmDart_entryOtherState,
    routeOrderedFusionArmDart_exitTurnState]
  exact phi_sq_alpha_fusionEntryOtherDart_eq_fusionExitTurnDart
    graphData hcubic hrotation data lens hab hac hbc
      (lens.bFusionSiteAt position)

/-- The directed exit-side face arc likewise starts at its unique
nonselected arm. -/
theorem phi_sq_alpha_routeOrderedFusionExitOtherState_eq_entryTurnState
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (position : Fin lens.fusionSiteCount) :
    graphData.toRotationSystem.phi
        (graphData.toRotationSystem.phi
          (graphData.toRotationSystem.alpha
            (routeOrderedFusionArmDart data lens hab hac
              (routeOrderedFusionExitOtherState
                graphData data lens hab hac position)))) =
      routeOrderedFusionArmDart data lens hab hac
        (routeOrderedFusionEntryTurnState
          graphData data lens hab hac position) := by
  rw [routeOrderedFusionArmDart_exitOtherState,
    routeOrderedFusionArmDart_entryTurnState]
  exact phi_sq_alpha_fusionExitOtherDart_eq_fusionEntryTurnDart
    graphData hcubic hrotation data lens hab hac hbc
      (lens.bFusionSiteAt position)

/-- Exact-cut transport across the entry-side fusion face requires only
the actual nonselected entry arm to avoid the cut. -/
theorem routeOrderedFusionEntryOtherFaceLabels_eq_exitTurn_of_not_cut
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (position : Fin lens.fusionSiteCount)
    (hnot : ¬cut (graphData.toRotationSystem.edgeOf
      (routeOrderedFusionArmDart data lens hab hac
        (routeOrderedFusionEntryOtherState
          graphData data lens hab hac position)))) :
    labels (dartOrbitFace graphData.toRotationSystem
        (routeOrderedFusionArmDart data lens hab hac
          (routeOrderedFusionEntryOtherState
            graphData data lens hab hac position))) =
      labels (dartOrbitFace graphData.toRotationSystem
        (routeOrderedFusionArmDart data lens hab hac
          (routeOrderedFusionExitTurnState
            graphData data lens hab hac position))) := by
  apply labels_eq_of_phi_sq_alpha_eq_of_not_cut
    graphData.toRotationSystem labels cut hexact
  · exact phi_sq_alpha_routeOrderedFusionEntryOtherState_eq_exitTurnState
      graphData hcubic hrotation data lens hab hac hbc position
  · exact hnot

/-- Exact-cut transport across the exit-side face requires only the actual
nonselected exit arm. -/
theorem routeOrderedFusionExitOtherFaceLabels_eq_entryTurn_of_not_cut
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (position : Fin lens.fusionSiteCount)
    (hnot : ¬cut (graphData.toRotationSystem.edgeOf
      (routeOrderedFusionArmDart data lens hab hac
        (routeOrderedFusionExitOtherState
          graphData data lens hab hac position)))) :
    labels (dartOrbitFace graphData.toRotationSystem
        (routeOrderedFusionArmDart data lens hab hac
          (routeOrderedFusionExitOtherState
            graphData data lens hab hac position))) =
      labels (dartOrbitFace graphData.toRotationSystem
        (routeOrderedFusionArmDart data lens hab hac
          (routeOrderedFusionEntryTurnState
            graphData data lens hab hac position))) := by
  apply labels_eq_of_phi_sq_alpha_eq_of_not_cut
    graphData.toRotationSystem labels cut hexact
  · exact phi_sq_alpha_routeOrderedFusionExitOtherState_eq_entryTurnState
      graphData hcubic hrotation data lens hab hac hbc position
  · exact hnot

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
