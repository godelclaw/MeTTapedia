import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileSeamSupport

/-!
# Relational connectivity update for one source Cell

The cumulative tracked-connectivity graph after one source Cell has three
exact factors: the old prefix, the new hexagonal Cell, and the two residual
corner turns at their common rung.  This file expresses outgoing
connectivity as the reflexive-transitive closure of those three observable
kinds of move.

The update is relational.  It does not assert that an incoming profile and a
Cell determine a unique outgoing profile.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CubicFaceBoundaryAdjacency
open GoertzelV24FaceDualConnectedness
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SimpleGraphSupResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileConnectivityUpdateEdgeSetDecidableEq :
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

/-- One observable connectivity move in a cumulative source-prefix update:
stay inside an old-prefix component, stay inside a Cell component, or cross
one literal residual seam turn. -/
def localLayerTrackedComponentStep
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (C : G.edgeSet → Color) (a b : Color) (x y : G.edgeSet) : Prop :=
  ThreeFactorComponentStep
    (regionalTrackedEdgeGraph
      embedded.cellulation.rotation.toRotationSystem
      aligned.toInterface.localLayerLeftPrefixRegion C a b)
    (regionalTrackedEdgeGraph
      embedded.cellulation.rotation.toRotationSystem
      aligned.toInterface.localLayerCellBoundaryRegion C a b)
    (aligned.toInterface.localLayerTrackedSeamGraph C a b) x y

/-- The third alternative in a component step is not abstract seam data: it
is exactly one of the two source-ordered turns at the shared rung, with both
edge colors in the tracked pair. -/
theorem localLayerTrackedComponentStep_iff
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (C : G.edgeSet → Color) (a b : Color) (x y : G.edgeSet) :
    aligned.localLayerTrackedComponentStep C a b x y ↔
      (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          aligned.toInterface.localLayerLeftPrefixRegion C a b).Reachable x y ∨
      (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          aligned.toInterface.localLayerCellBoundaryRegion C a b).Reachable x y ∨
      ∃ step : Fin 2,
        IsTrackedColor a b
            (C (aligned.toInterface.localLayerPrefixCrossing step)) ∧
          IsTrackedColor a b
            (C (aligned.toInterface.nextLocalLayerPrefixCrossing step)) ∧
          ((x = aligned.toInterface.localLayerPrefixCrossing step ∧
              y = aligned.toInterface.nextLocalLayerPrefixCrossing step) ∨
            (x = aligned.toInterface.nextLocalLayerPrefixCrossing step ∧
              y = aligned.toInterface.localLayerPrefixCrossing step)) := by
  unfold localLayerTrackedComponentStep ThreeFactorComponentStep
  rw [aligned.localLayerTrackedSeamGraph_adj_iff_exists_crossing_step
    hcubic hrotation C a b x y]

/-- Exact one-Cell connectivity update.  Reachability in the enlarged
cumulative prefix is the relational closure of the old profile components,
the local Cell components, and the two classified seam turns. -/
theorem localLayerRightPrefixTrackedGraph_reachable_iff_componentClosure
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (C : G.edgeSet → Color) (a b : Color) (x y : G.edgeSet) :
    (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        aligned.toInterface.localLayerRightPrefixRegion C a b).Reachable x y ↔
      Relation.ReflTransGen
        (aligned.localLayerTrackedComponentStep C a b) x y := by
  rw [aligned.toInterface.localLayerRightPrefixTrackedGraph_eq_three_factor]
  exact reachable_sup_sup_iff_threeFactorComponentClosure _ _ _ x y

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
