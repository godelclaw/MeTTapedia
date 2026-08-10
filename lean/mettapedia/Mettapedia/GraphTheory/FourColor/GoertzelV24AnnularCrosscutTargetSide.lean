import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutConnectedSides
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutDualLoopBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualCycleTargetSide

/-!
# One-anchor orientation of a source annular crosscut

The dual-cycle face calculation shows that all target-side darts of a simple
facial-dual loop belong to one deletion component.  Thus a source corridor
formation need only establish one literal target-side anchor in the retained
component; the remaining boundary orientation is propagated around the loop.
This is geometric propagation, not a profile premise.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24DualCycleTargetSide
open GoertzelV24DualCycleBoundaryFaceOrientation
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- A single retained target-face dart fixes the orientation of the whole
source dual loop.  All later target darts lie in the same deletion component,
so the already-constructed boundary-order theorem applies without a separate
per-port face-side assumption. -/
theorem SourceCrosscutBoundaryData.dualLoopBoundaryFacesTarget_of_exists_targetFaceDart_kept
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (hseed : ∃ step,
      deletedRegionKeep (boundary.deletedVertices data pair)
        (data.toRotationSystem.vertOf
          (dualWalkTargetFaceDart hunique pair.dualLoop step))) :
    boundary.DualLoopBoundaryFacesTarget data pair := by
  rcases hseed with ⟨seed, hseed⟩
  have hseedComponent :
      data.toRotationSystem.vertOf
          (dualWalkTargetFaceDart hunique pair.dualLoop seed) ∈
        boundary.component.supp := by
    rw [SourceCrosscutBoundaryData.deletedRegionKeep_eq_componentSide
      data pair boundary] at hseed
    exact (pair.mem_componentSide_iff boundary.component _).1 hseed
  apply SourceCrosscutBoundaryData.dualLoopBoundaryFacesTarget_of_targetFaceDarts_kept
    data pair boundary
  intro step
  rw [SourceCrosscutBoundaryData.deletedRegionKeep_eq_componentSide
    data pair boundary]
  apply (pair.mem_componentSide_iff boundary.component _).2
  exact dualWalkTargetFaceDart_component_mem_iff data htwoSided hunique
    pair.dualLoop pair.dualLoop_isCycle boundary.component seed step |>.mp
      hseedComponent

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
