import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionFaceCutTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionRouteSegmentFaceCutTransport

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open SimpleGraph
open SimpleGraphDartRotation

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- At a positively oriented fusion edge, the `c` companion based at the
`b` entry is the actual `c`-route entry dart. -/
theorem EvenKempeFusionLens.cDartAtBEntry_eq_cEntryNeighborDart_of_chirality_eq_true
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite)
    (hchirality : lens.fusionChirality hab hac site = true) :
    lens.cDartAtBEntry hab hac site =
      lens.cEntryNeighborDart hac site := by
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · exact
      ((lens.fusionChirality_eq_true_iff_endpoints_agree
        hab hac site).1 hchirality).1.symm
  · rw [lens.cDartAtBEntry_edge hab hac site,
      lens.cEntryNeighborDart_edge hac site,
      EvenKempeFusionLens.cEdgeAtBEntry, if_pos hchirality]

/-- At a positively oriented fusion edge, the `c` companion based at the
`b` exit is the actual `c`-route exit dart. -/
theorem EvenKempeFusionLens.cDartAtBExit_eq_cExitNeighborDart_of_chirality_eq_true
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite)
    (hchirality : lens.fusionChirality hab hac site = true) :
    lens.cDartAtBExit hab hac site =
      lens.cExitNeighborDart hac site := by
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · exact
      ((lens.fusionChirality_eq_true_iff_endpoints_agree
        hab hac site).1 hchirality).2.symm
  · rw [lens.cDartAtBExit_edge hab hac site,
      lens.cExitNeighborDart_edge hac site,
      EvenKempeFusionLens.cEdgeAtBExit, if_pos hchirality]

/-- At a negatively oriented fusion edge, the `c` route enters through
the `b` exit endpoint. -/
theorem EvenKempeFusionLens.cDartAtBExit_eq_cEntryNeighborDart_of_chirality_eq_false
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite)
    (hchirality : lens.fusionChirality hab hac site = false) :
    lens.cDartAtBExit hab hac site =
      lens.cEntryNeighborDart hac site := by
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · exact
      ((lens.fusionChirality_eq_false_iff_endpoints_reverse
        hab hac site).1 hchirality).1.symm
  · rw [lens.cDartAtBExit_edge hab hac site,
      lens.cEntryNeighborDart_edge hac site,
      EvenKempeFusionLens.cEdgeAtBExit]
    simp [hchirality]

/-- At a negatively oriented fusion edge, the `c` route exits through
the `b` entry endpoint. -/
theorem EvenKempeFusionLens.cDartAtBEntry_eq_cExitNeighborDart_of_chirality_eq_false
    {portCount : Nat}
    {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b c : Color}
    {left right : Fin portCount}
    (lens : data.EvenKempeFusionLens C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c) (site : lens.FusionSite)
    (hchirality : lens.fusionChirality hab hac site = false) :
    lens.cDartAtBEntry hab hac site =
      lens.cExitNeighborDart hac site := by
  apply SimpleGraph.Dart.eq_of_fst_eq_of_edge_eq
  · exact
      ((lens.fusionChirality_eq_false_iff_endpoints_reverse
        hab hac site).1 hchirality).2.symm
  · rw [lens.cDartAtBEntry_edge hab hac site,
      lens.cExitNeighborDart_edge hac site,
      EvenKempeFusionLens.cEdgeAtBEntry]
    simp [hchirality]

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

/-- Entry arm of a fusion site, expressed in first-route coordinates. -/
def bFusionEntryArmState
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (position : Fin lens.fusionSiteCount) :
    (Fin lens.fusionSiteCount × Bool) × Bool :=
  ((position, false), true)

/-- Exit arm of a fusion site, expressed in first-route coordinates. -/
def bFusionExitArmState
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (position : Fin lens.fusionSiteCount) :
    (Fin lens.fusionSiteCount × Bool) × Bool :=
  ((position, true), true)

/-- Entry arm of the same physical site in second-route coordinates. -/
def cFusionEntryArmState
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (position : Fin lens.fusionSiteCount) :
    (Fin lens.fusionSiteCount × Bool) × Bool :=
  ((lens.fusionMonodromy position, false), false)

/-- Exit arm of the same physical site in second-route coordinates. -/
def cFusionExitArmState
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (position : Fin lens.fusionSiteCount) :
    (Fin lens.fusionSiteCount × Bool) × Bool :=
  ((lens.fusionMonodromy position, true), false)

/-- First-route coordinates interpret directly as the physical fusion arm. -/
theorem routeOrderedFusionArmDart_b_eq_fusionRouteArmDart
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) (endpoint : Bool) :
    routeOrderedFusionArmDart data lens hab hac
        ((position, endpoint), true) =
      fusionRouteArmDart data lens hab hac
        (lens.bFusionSiteAt position) endpoint true := by
  rw [← lens.fusionArmReindexing_apply_b hab hac (position, endpoint)]
  simp only [routeOrderedFusionArmDart, bIndexedFusionArmDart,
    Equiv.symm_apply_apply]

/-- Pulling a second-route endpoint back through signed monodromy applies
the local chirality exactly once. -/
theorem routeOrderedFusionArmDart_c_eq_fusionRouteArmDart
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) (endpoint : Bool) :
    routeOrderedFusionArmDart data lens hab hac
        ((lens.fusionMonodromy position, endpoint), false) =
      fusionRouteArmDart data lens hab hac
        (lens.bFusionSiteAt position)
        (fusionEndpointTransport
          (lens.bOrderedFusionChirality hab hac position) endpoint)
        false := by
  have hstate :
      ((lens.fusionMonodromy position, endpoint), false) =
        lens.fusionArmReindexing hab hac
          ((position,
            fusionEndpointTransport
              (lens.bOrderedFusionChirality hab hac position) endpoint),
            false) := by
    rw [lens.fusionArmReindexing_apply_c]
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · exact (fusionEndpointTransport_involutive
          (lens.bOrderedFusionChirality hab hac position) endpoint).symm
    · rfl
  rw [hstate]
  simp only [routeOrderedFusionArmDart, bIndexedFusionArmDart,
    Equiv.symm_apply_apply]

@[simp] theorem routeOrderedFusionArmDart_bEntryArmState
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) :
    routeOrderedFusionArmDart data lens hab hac
        (bFusionEntryArmState data lens position) =
      ambientBEntryNeighborDart data lens hab
        (lens.bFusionSiteAt position) := by
  rw [bFusionEntryArmState,
    routeOrderedFusionArmDart_b_eq_fusionRouteArmDart]
  simp

@[simp] theorem routeOrderedFusionArmDart_bExitArmState
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) :
    routeOrderedFusionArmDart data lens hab hac
        (bFusionExitArmState data lens position) =
      ambientBExitNeighborDart data lens hab
        (lens.bFusionSiteAt position) := by
  rw [bFusionExitArmState,
    routeOrderedFusionArmDart_b_eq_fusionRouteArmDart]
  simp

@[simp] theorem routeOrderedFusionArmDart_cEntryArmState
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) :
    routeOrderedFusionArmDart data lens hab hac
        (cFusionEntryArmState data lens position) =
      ambientCEntryNeighborDart data lens hac
        (lens.bFusionSiteAt position) := by
  rw [cFusionEntryArmState,
    routeOrderedFusionArmDart_c_eq_fusionRouteArmDart]
  cases hchirality : lens.bOrderedFusionChirality hab hac position
  · have hsite : lens.fusionChirality hab hac
        (lens.bFusionSiteAt position) = false := by
      simpa only [EvenKempeFusionLens.bOrderedFusionChirality] using hchirality
    simpa only [fusionEndpointTransport_false, Bool.not_false,
      fusionRouteArmDart_exit_c, ambientCExitCompanionDart,
      ambientCEntryNeighborDart] using congrArg
        (retainedDartToAmbientDart data)
        (lens.cDartAtBExit_eq_cEntryNeighborDart_of_chirality_eq_false
          hab hac (lens.bFusionSiteAt position) hsite)
  · have hsite : lens.fusionChirality hab hac
        (lens.bFusionSiteAt position) = true := by
      simpa only [EvenKempeFusionLens.bOrderedFusionChirality] using hchirality
    simpa only [fusionEndpointTransport_true,
      fusionRouteArmDart_entry_c, ambientCEntryCompanionDart,
      ambientCEntryNeighborDart] using congrArg
        (retainedDartToAmbientDart data)
        (lens.cDartAtBEntry_eq_cEntryNeighborDart_of_chirality_eq_true
          hab hac (lens.bFusionSiteAt position) hsite)

@[simp] theorem routeOrderedFusionArmDart_cExitArmState
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (position : Fin lens.fusionSiteCount) :
    routeOrderedFusionArmDart data lens hab hac
        (cFusionExitArmState data lens position) =
      ambientCExitNeighborDart data lens hac
        (lens.bFusionSiteAt position) := by
  rw [cFusionExitArmState,
    routeOrderedFusionArmDart_c_eq_fusionRouteArmDart]
  cases hchirality : lens.bOrderedFusionChirality hab hac position
  · have hsite : lens.fusionChirality hab hac
        (lens.bFusionSiteAt position) = false := by
      simpa only [EvenKempeFusionLens.bOrderedFusionChirality] using hchirality
    simpa only [fusionEndpointTransport_false, Bool.not_true,
      fusionRouteArmDart_entry_c, ambientCEntryCompanionDart,
      ambientCExitNeighborDart] using congrArg
        (retainedDartToAmbientDart data)
        (lens.cDartAtBEntry_eq_cExitNeighborDart_of_chirality_eq_false
          hab hac (lens.bFusionSiteAt position) hsite)
  · have hsite : lens.fusionChirality hab hac
        (lens.bFusionSiteAt position) = true := by
      simpa only [EvenKempeFusionLens.bOrderedFusionChirality] using hchirality
    simpa only [fusionEndpointTransport_true,
      fusionRouteArmDart_exit_c, ambientCExitCompanionDart,
      ambientCExitNeighborDart] using congrArg
        (retainedDartToAmbientDart data)
        (lens.cDartAtBExit_eq_cExitNeighborDart_of_chirality_eq_true
          hab hac (lens.bFusionSiteAt position) hsite)

/-- A cut-avoiding first-route segment is exactly a label-preserving wire
between route-ordered finite transfer states. -/
theorem EvenKempeFusionLens.bRouteStateFaceLabels_eq_of_not_cut
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (first second : Fin lens.fusionSiteCount)
    (hbOrder : lens.bFusionSupportOrderEmbedding first <
      lens.bFusionSupportOrderEmbedding second)
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (hnot : ∀ edge ∈
      (lens.bFusionOrderInterval first second hbOrder).support.tail.dropLast,
      ¬cut (retainedEdgeToAmbientEdge data edge)) :
    labels (dartOrbitFace graphData.toRotationSystem
        (routeOrderedFusionArmDart data lens hab hac
          (bFusionExitArmState data lens first))) =
      labels (dartOrbitFace graphData.toRotationSystem
        (routeOrderedFusionArmDart data lens hab hac
          (bFusionEntryArmState data lens second))) := by
  simpa only [routeOrderedFusionArmDart_bExitArmState,
    routeOrderedFusionArmDart_bEntryArmState] using
      EvenKempeFusionLens.bAmbientRouteSegmentFaceLabels_eq_of_not_cut
        data lens hab first second hbOrder graphData hcubic hrotation
          labels cut hexact hnot

/-- The oppositely ordered second-route segment is the corresponding
label-preserving wire in signed monodromy coordinates. -/
theorem EvenKempeFusionLens.cRouteStateFaceLabels_eq_of_not_cut
    (data : AdjacentPairData G)
    {C : (DeletedAdjacentPairGraph G data.firstVertex
      data.secondVertex).EdgeColoring Color}
    {a b c : Color} {left right : Fin 4}
    (lens : data.degreeTwoBoundaryData.EvenKempeFusionLens
      C a b c left right)
    (hab : a ≠ b) (hac : a ≠ c)
    (first second : Fin lens.fusionSiteCount)
    (hcOrder : lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy second)) <
      lens.cFusionSupportOrderEmbedding
        (finCongr lens.fusionSites_length_eq
          (lens.fusionMonodromy first)))
    (graphData : Data G)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    {A : Type*}
    (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (hnot : ∀ edge ∈
      (lens.cFusionOrderInterval first second hcOrder).reverse.support.tail.dropLast,
      ¬cut (retainedEdgeToAmbientEdge data edge)) :
    labels (dartOrbitFace graphData.toRotationSystem
        (routeOrderedFusionArmDart data lens hab hac
          (cFusionExitArmState data lens second))) =
      labels (dartOrbitFace graphData.toRotationSystem
        (routeOrderedFusionArmDart data lens hab hac
          (cFusionEntryArmState data lens first))) := by
  simpa only [routeOrderedFusionArmDart_cExitArmState,
    routeOrderedFusionArmDart_cEntryArmState] using
      EvenKempeFusionLens.cAmbientRouteSegmentFaceLabels_eq_of_not_cut
        data lens hac first second hcOrder graphData hcubic hrotation
          labels cut hexact hnot

end

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
