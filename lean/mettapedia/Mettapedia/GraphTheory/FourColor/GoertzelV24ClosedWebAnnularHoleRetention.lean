import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebAnnularEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutFaceRetention

/-!
# Retaining the named outer hole across a source crosscut

The source chooses the retained crosscut component from an outer facial dart.
This module makes the resulting elementary but essential conclusion explicit:
if the cut avoids the named outer-hole boundary, every vertex on that boundary
lies on the retained component side.  It deliberately uses the open facial-walk
argument, because a hole boundary in the Cell-3 tangle need not be two-sided.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAnnularEmbedding

open GoertzelV24AnnularCrosscut
open GoertzelV24AnnularCrosscut.SeparatedAlignedSimpleDualCrosscuts
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

local instance annularHoleRetentionEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace ClosedWebAnnularEmbedding

variable {data : AnnularBoundaryData G outerCount}
  (embedded : ClosedWebAnnularEmbedding data)

/-- If a source crosscut avoids the outer-hole boundary, the component chosen
from the distinguished outer dart retains every dart of that hole. -/
theorem outerHole_vertex_mem_componentSide_of_boundary_avoids_primalCut
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace embedded.RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.RS)
      (Finset.univ : Finset (OrbitFace embedded.RS))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary embedded.RS)
      (Finset.univ : Finset (OrbitFace embedded.RS))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData embedded.cellulation.rotation pair)
    (havoid : ∀ edge : G.edgeSet,
      edge ∈ orbitFaceBoundary embedded.RS embedded.cellulation.outerHole →
        edge.1 ∉ edgeFinsetValueSet
          (pair.primalCutEdges embedded.cellulation.rotation))
    (dart : G.Dart)
    (hdart : dartOrbitFace embedded.RS dart = embedded.cellulation.outerHole) :
    embedded.RS.vertOf dart ∈ pair.componentSide boundary.component := by
  apply SourceCrosscutBoundaryData.face_vertex_mem_componentSide_of_root_and_boundary_avoids_primalCut
    embedded.cellulation.rotation pair boundary embedded.RS.outer dart
  · exact (pair.mem_componentSide_iff boundary.component
      (embedded.RS.vertOf embedded.RS.outer)).1 boundary.outer_kept
  · intro edge hedge
    apply havoid edge
    rw [embedded.outer_dart_on_outerHole] at hedge
    exact hedge
  · exact hdart.trans embedded.outer_dart_on_outerHole.symm

end ClosedWebAnnularEmbedding

end

end GoertzelV24ClosedWebAnnularEmbedding

end Mettapedia.GraphTheory.FourColor
