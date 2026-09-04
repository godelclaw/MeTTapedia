import Mettapedia.GraphTheory.FourColor.Compositional.CoherentFullProfileSweep
import Mettapedia.GraphTheory.FourColor.Compositional.FixedColorConnectivityAlternative

/-!
# Complete-profile geometry with fixed-colour connectivity

The coherent deletion pair carries two independent pieces of information:
the complete-profile geometric alternatives at its selected endpoints, and
the fixed-colour connectivity comparison along the unchanged deletion path.
This file keeps those facts on one receipt.  It does not reselect a colouring,
matching, site, or path, and it does not identify raw sweep states with Count
profiles.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace FullProfileConnectivityAlternative

open AlternatingSiteGeometry
open CoherentFullProfileSweep
open CoherentResidualReturnConnectivity
open DeletionAtlasPath
open FixedColorConnectivityTransition
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation
open SparseNoncentralMeshAtlas

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a : Nat}

/-- A mesh row either exposes the existing branching/boundary horn, or one
unchanged coherent pair simultaneously carries complete-profile geometry at
both endpoints and the exact fixed-colour synchronization alternative. -/
theorem branchingOrBoundary_or_fullProfilePair_with_fixedColorAlternative
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G) (row : Fin a) :
    (∃ assignment : TaitAssignment
        (coloringFamily rotation minimal ordered minimizer row),
      HasBranchingOrBoundary
        (coloringFamily rotation minimal ordered minimizer row) assignment) ∨
      ∃ pair : CoherentFullProfileSweepPairReceipt rotation minimal
          (coloringFamily rotation minimal ordered minimizer row) minimizer,
        ConnectivitySynchronized rotation minimal
            (coloringFamily rotation minimal ordered minimizer row) minimizer
            pair.base ∨
          Nonempty (FixedColorLocalConnectivityTransitionReceipt
            rotation minimal
              (coloringFamily rotation minimal ordered minimizer row)
              minimizer pair.base) := by
  rcases branchingOrBoundary_or_hasCoherentFullProfileSweepPair rotation minimal
      ordered minimizer row with hhorn | hpair
  · exact Or.inl hhorn
  · rcases hpair with ⟨pair⟩
    exact Or.inr ⟨pair,
      synchronized_or_fixedColorLocalTransition rotation minimal
        (coloringFamily rotation minimal ordered minimizer row) minimizer
        pair.base⟩

end

end FullProfileConnectivityAlternative

end Mettapedia.GraphTheory.FourColor.Compositional
