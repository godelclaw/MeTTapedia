import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileSeamSupport

/-!
# Relational face-progress update for one source Cell

Face progress is occurrence-sensitive: a bridge edge may occur twice on one
facial walk.  The common carrier is therefore the cyclic-position type of an
actual face, not the ambient edge type.  On that carrier, adjoining one source
Cell has the same three exact factors as tracked connectivity: old prefix,
Cell, and the residual turns at their shared rung.

This file identifies those residual facial turns and computes enlarged
fragment reachability as a relational closure.  The cap-at-five coordinate is
left to the existing overlap-corrected fragment arithmetic.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CubicFaceBoundaryAdjacency
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationFaceFragments
open GoertzelV24SimpleGraphSupResidual
open GoertzelV24TerminalProfileFaceUpdate
open GoertzelV24TerminalProfileRegionalCoverage
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileFaceUpdateEdgeSetDecidableEq :
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

/-- A residual facial step is exactly a cyclic turn whose underlying edges
are one of the two source-ordered prefix/Cell crossing pairs. -/
theorem localLayerFaceSeamGraph_adj_iff_exists_crossing_step
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    (x y : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card) :
    (aligned.toInterface.localLayerFaceSeamGraph root).Adj x y ↔
      (faceCyclePositionGraph
          embedded.cellulation.rotation.toRotationSystem root).Adj x y ∧
        ∃ step : Fin 2,
          ((faceCycleEdge embedded.cellulation.rotation.toRotationSystem root x =
                aligned.toInterface.localLayerPrefixCrossing step ∧
              faceCycleEdge embedded.cellulation.rotation.toRotationSystem root y =
                aligned.toInterface.nextLocalLayerPrefixCrossing step) ∨
            (faceCycleEdge embedded.cellulation.rotation.toRotationSystem root x =
                aligned.toInterface.nextLocalLayerPrefixCrossing step ∧
              faceCycleEdge embedded.cellulation.rotation.toRotationSystem root y =
                aligned.toInterface.localLayerPrefixCrossing step)) := by
  unfold SourceConsecutiveSlabInterface.localLayerFaceSeamGraph
  rw [faceRegionalSeamGraph_adj_iff]
  constructor
  · rintro ⟨hfaceAdj, hforward | hbackward⟩
    · have hedgeAdj := edgeAdjacencyGraph_adj_of_faceCyclePositionGraph_adj
        embedded.cellulation.rotation.toRotationSystem hcubic hrotation root
          hfaceAdj
      rcases aligned.exists_crossing_step_of_left_only_right_only_adj
          hcubic hrotation hforward.1 hforward.2.1 hforward.2.2.1
            hforward.2.2.2 hedgeAdj with ⟨step, hx, hy⟩
      exact ⟨hfaceAdj, step, Or.inl ⟨hx, hy⟩⟩
    · have hedgeAdj := edgeAdjacencyGraph_adj_of_faceCyclePositionGraph_adj
        embedded.cellulation.rotation.toRotationSystem hcubic hrotation root
          hfaceAdj
      rcases aligned.exists_crossing_step_of_left_only_right_only_adj
          hcubic hrotation hbackward.2.2.1 hbackward.2.2.2 hbackward.1
            hbackward.2.1 hedgeAdj.symm with ⟨step, hy, hx⟩
      exact ⟨hfaceAdj, step, Or.inr ⟨hx, hy⟩⟩
  · rintro ⟨hfaceAdj, step, hforward | hbackward⟩
    · refine ⟨hfaceAdj, Or.inl ?_⟩
      rw [hforward.1, hforward.2]
      exact ⟨
        aligned.localLayerPrefixCrossing_mem_leftPrefixRegion step,
        aligned.localLayerPrefixCrossing_not_mem_cellBoundaryRegion step,
        aligned.nextLocalLayerPrefixCrossing_mem_cellBoundaryRegion step,
        aligned.nextLocalLayerPrefixCrossing_not_mem_leftPrefixRegion step⟩
    · refine ⟨hfaceAdj, Or.inr ?_⟩
      rw [hbackward.1, hbackward.2]
      exact ⟨
        aligned.nextLocalLayerPrefixCrossing_mem_cellBoundaryRegion step,
        aligned.nextLocalLayerPrefixCrossing_not_mem_leftPrefixRegion step,
        aligned.localLayerPrefixCrossing_mem_leftPrefixRegion step,
        aligned.localLayerPrefixCrossing_not_mem_cellBoundaryRegion step⟩

/-- One observable occurrence-level move: stay inside an old-prefix face
fragment, stay inside a Cell face fragment, or take one residual facial turn. -/
def localLayerFaceComponentStep
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    (x y : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card) : Prop :=
  ThreeFactorComponentStep
    (faceRegionalAmbientPositionGraph
      embedded.cellulation.rotation.toRotationSystem root
      aligned.toInterface.localLayerLeftPrefixRegion)
    (faceRegionalAmbientPositionGraph
      embedded.cellulation.rotation.toRotationSystem root
      aligned.toInterface.localLayerCellBoundaryRegion)
    (aligned.toInterface.localLayerFaceSeamGraph root) x y

/-- Exact occurrence-sensitive face update.  Two occurrences belong to the
same enlarged prefix fragment exactly when they are joined by the relational
closure of the two factor-fragment relations and the classified seam turns. -/
theorem localLayerRightPrefixFaceGraph_reachable_iff_componentClosure
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    (x y : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card) :
    (faceRegionalAmbientPositionGraph
        embedded.cellulation.rotation.toRotationSystem root
        aligned.toInterface.localLayerRightPrefixRegion).Reachable x y ↔
      Relation.ReflTransGen
        (aligned.localLayerFaceComponentStep root) x y := by
  rw [aligned.toInterface.localLayerRightPrefixFaceGraph_eq_three_factor]
  exact reachable_sup_sup_iff_threeFactorComponentClosure _ _ _ x y

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
