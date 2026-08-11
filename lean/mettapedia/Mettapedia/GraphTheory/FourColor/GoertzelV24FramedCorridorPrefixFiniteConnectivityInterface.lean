import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileConnectivityUpdate
import Mettapedia.GraphTheory.FourColor.GoertzelV24RegionalBoundaryProfileFiniteState
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphThreeFactorContraction

/-!
# A finite connectivity interface for one source corridor Cell

The exact tracked graph after one source Cell has three factors: the old
cumulative prefix, the newly exposed hexagonal face boundary, and the two
residual seam turns.  All genuine switches between these factors occur on
the old two-edge cut or on that six-edge face boundary.  Consequently,
ambient reachability between the new cut edges contracts to component moves
on an interface of at most eight actual edges.

This is only a finite-interface contraction.  It does not identify the
whole hexagonal face boundary with the smaller complementary two-vertex
Cell, and it does not assert a deterministic profile update.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24SimpleGraphThreeFactorContraction
open GoertzelV24InterfaceSpliceConnectivity
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixFiniteConnectivityInterfaceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceCornerAlignedSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- The finite carrier on which one cumulative connectivity update can be
computed: the old two-edge cut together with the six edges of the newly
exposed source hexagon. -/
def localLayerFiniteConnectivityInterface
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) : Finset G.edgeSet :=
  indexedCrossingEdgeSet aligned.toInterface.localLayerPrefixCrossing ∪
    aligned.toInterface.localLayerCellBoundaryRegion

theorem localLayerPrefixCrossing_mem_finiteConnectivityInterface
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) :
    aligned.toInterface.localLayerPrefixCrossing step ∈
      aligned.localLayerFiniteConnectivityInterface := by
  apply Finset.mem_union_left
  exact (mem_indexedCrossingEdgeSet_iff
    aligned.toInterface.localLayerPrefixCrossing _).2 ⟨step, rfl⟩

theorem nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) (step : Fin 2) :
    aligned.toInterface.nextLocalLayerPrefixCrossing step ∈
      aligned.localLayerFiniteConnectivityInterface := by
  apply Finset.mem_union_right
  exact aligned.nextLocalLayerPrefixCrossing_mem_cellBoundaryRegion step

theorem localLayerCellBoundaryRegion_subset_finiteConnectivityInterface
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    aligned.toInterface.localLayerCellBoundaryRegion ⊆
      aligned.localLayerFiniteConnectivityInterface := by
  exact Finset.subset_union_right

/-- The selected connectivity carrier has at most two old cut edges plus
the six edges of the next source hexagon. -/
theorem localLayerFiniteConnectivityInterface_card_le_eight
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    aligned.localLayerFiniteConnectivityInterface.card ≤ 8 := by
  have hcell :
      aligned.toInterface.localLayerCellBoundaryRegion.card = 6 := by
    simpa [SourceConsecutiveSlabInterface.localLayerCellBoundaryRegion] using
      aligned.toInterface.nextCenterLayerFace_boundary_card_eq_six
  calc
    aligned.localLayerFiniteConnectivityInterface.card ≤
        (indexedCrossingEdgeSet
          aligned.toInterface.localLayerPrefixCrossing).card +
          aligned.toInterface.localLayerCellBoundaryRegion.card := by
      exact Finset.card_union_le _ _
    _ ≤ 2 + 6 := Nat.add_le_add
      (card_indexedCrossingEdgeSet_le
        aligned.toInterface.localLayerPrefixCrossing)
      (le_of_eq hcell)
    _ = 8 := rfl

/-- Every vertex used by the residual seam graph lies in the selected
eight-edge interface. -/
theorem localLayerTrackedSeamGraph_support_subset_finiteConnectivityInterface
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (C : G.edgeSet → Color) (a b : Color) :
    (aligned.toInterface.localLayerTrackedSeamGraph C a b).support ⊆
      aligned.localLayerFiniteConnectivityInterface := by
  intro edge hedge
  rcases (SimpleGraph.mem_support
      (aligned.toInterface.localLayerTrackedSeamGraph C a b)).1 hedge with
    ⟨neighbor, hadj⟩
  rcases (aligned.localLayerTrackedSeamGraph_adj_iff_exists_crossing_step
      hcubic hrotation C a b edge neighbor).1 hadj with
    ⟨step, _hleftColor, _hrightColor, horientation⟩
  rcases horientation with hforward | hbackward
  · rw [hforward.1]
    exact aligned.localLayerPrefixCrossing_mem_finiteConnectivityInterface step
  · rw [hbackward.1]
    exact aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
      step

/-- Exact finite-interface form of the one-Cell connectivity update.
Reachability between the new cut edges in the ambient enlarged prefix is
equivalent to the reflexive-transitive closure of the three factor-component
relations on a selected carrier of at most eight actual edges. -/
theorem localLayerRightPrefixTrackedGraph_reachable_iff_finiteInterfaceClosure
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (C : G.edgeSet → Color) (a b : Color) (left right : Fin 2) :
    (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        aligned.toInterface.localLayerRightPrefixRegion C a b).Reachable
      (aligned.toInterface.nextLocalLayerPrefixCrossing left)
      (aligned.toInterface.nextLocalLayerPrefixCrossing right) ↔
    Relation.ReflTransGen
      (SelectedThreeFactorComponentStep
        (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          aligned.toInterface.localLayerLeftPrefixRegion C a b)
        (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          aligned.toInterface.localLayerCellBoundaryRegion C a b)
        (aligned.toInterface.localLayerTrackedSeamGraph C a b)
        (fun edge => edge ∈ aligned.localLayerFiniteConnectivityInterface))
      ⟨aligned.toInterface.nextLocalLayerPrefixCrossing left,
        aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
          left⟩
      ⟨aligned.toInterface.nextLocalLayerPrefixCrossing right,
        aligned.nextLocalLayerPrefixCrossing_mem_finiteConnectivityInterface
          right⟩ := by
  rw [aligned.toInterface.localLayerRightPrefixTrackedGraph_eq_three_factor]
  apply reachable_sup_sup_iff_subtype_threeFactorComponentClosure
  · intro x middle y hx hy hleft hcell
    have hinter := regionalTrackedEdgeGraph_switch_mem_inter
      embedded.cellulation.rotation.toRotationSystem
      aligned.toInterface.localLayerLeftPrefixRegion
      aligned.toInterface.localLayerCellBoundaryRegion C a b hx hy hleft hcell
    exact aligned.localLayerCellBoundaryRegion_subset_finiteConnectivityInterface
      (Finset.mem_inter.1 hinter).2
  · intro x middle y _hx hy _hleft hseam
    apply aligned.localLayerTrackedSeamGraph_support_subset_finiteConnectivityInterface
      hcubic hrotation C a b
    exact SimpleGraph.mem_support_of_reachable hy hseam
  · intro x middle y _hx hy _hcell hseam
    apply aligned.localLayerTrackedSeamGraph_support_subset_finiteConnectivityInterface
      hcubic hrotation C a b
    exact SimpleGraph.mem_support_of_reachable hy hseam

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
