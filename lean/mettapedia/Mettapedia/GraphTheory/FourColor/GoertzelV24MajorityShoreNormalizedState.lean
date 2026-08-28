import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedEdgeShoreStructuralData
import Mettapedia.GraphTheory.FourColor.GoertzelV24NormalizedSeamState

/-!
# The exact normalized state of a majority edge shore

This is the consumer adapter between the connected-shore construction and the
finite seam state.  The chosen outer dart roots the literal open tangle but is
not added to the receipt.  A proof that the literal boundary has width `k`
supplies coordinates on the common standard carrier `ULift (Fin k)`.

Consequently two shores of the same width can be compared by ordinary equality
of `NormalizedSeamState.State k`.  Such an equality simultaneously transports
the canonical boundary rotation and the exact Tait support; the two roles stay
separate in the conclusion.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MajorityShoreNormalizedState

open GoertzelV24CanonicalHubClosure
open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24NormalizedSeamState
open GoertzelV24NormalizedTaitSupport
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SeamExchange
open GoertzelV24VertexSideOpenTangle

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The literal number of boundary darts of the majority vertex shore. -/
def boundaryWidth (rotation : SimpleGraphDartRotation.Data G)
    (shore : Finset G.edgeSet) : Nat :=
  Fintype.card
    (BoundaryDart rotation.toRotationSystem (majorityRetainedKeep G shore))

/-- Coordinates on a majority shore whose literal boundary has cardinality
`k`.  The `ULift` keeps the standard carrier in the universe of the ambient
map. -/
noncomputable def boundaryCoordinate
    (rotation : SimpleGraphDartRotation.Data G)
    (shore : Finset G.edgeSet) (k : Nat)
    (hwidth : boundaryWidth rotation shore = k) :
    BoundaryDart rotation.toRotationSystem (majorityRetainedKeep G shore) ≃
      StandardPort.{u} k :=
  (Fintype.equivFin
      (BoundaryDart rotation.toRotationSystem
        (majorityRetainedKeep G shore))).trans
    ((finCongr hwidth).trans Equiv.ulift.symm)

/-- The literal open tangle carried by the majority vertex shore. -/
noncomputable abbrev innerTangle
    (rotation : SimpleGraphDartRotation.Data G)
    (shore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G shore)) :=
  ofVertexSide rotation.toRotationSystem
    (majorityRetainedKeep G shore) outer

/-- The canonical exact state of a rooted majority shore at a supplied common
width. -/
noncomputable def normalizedState
    (rotation : SimpleGraphDartRotation.Data G)
    (shore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G shore))
    (k : Nat) (hwidth : boundaryWidth rotation shore = k) : State k :=
  ofInnerTangle k (innerTangle rotation shore outer)
    (canonicalHubRotation rotation.toRotationSystem
      (majorityRetainedKeep G shore))
    (boundaryCoordinate rotation shore k hwidth)

@[simp]
theorem normalizedState_hubRotation
    (rotation : SimpleGraphDartRotation.Data G)
    (shore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G shore))
    (k : Nat) (hwidth : boundaryWidth rotation shore = k) :
    (normalizedState rotation shore outer k hwidth).hubRotation =
      (boundaryCoordinate rotation shore k hwidth).permCongr
        (canonicalHubRotation rotation.toRotationSystem
          (majorityRetainedKeep G shore)) := rfl

@[simp]
theorem normalizedState_support
    (rotation : SimpleGraphDartRotation.Data G)
    (shore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G shore))
    (k : Nat) (hwidth : boundaryWidth rotation shore = k) :
    (normalizedState rotation shore outer k hwidth).support =
      normalizedTaitInnerSupport k (innerTangle rotation shore outer)
        (boundaryCoordinate rotation shore k hwidth) := rfl

/-- Equality of the canonical normalized shore states is exactly the joint
receipt consumed by physical replacement: it preserves the
orientation-reversing seam equation and the exact finite Tait support. -/
theorem replacement_receipt_of_normalizedState_eq
    (rotation : SimpleGraphDartRotation.Data G)
    (oldShore newShore : Finset G.edgeSet)
    (oldOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G oldShore))
    (newOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G newShore))
    (k : Nat)
    (oldWidth : boundaryWidth rotation oldShore = k)
    (newWidth : boundaryWidth rotation newShore = k)
    {L : Type u}
    (matching : L ≃ BoundaryDart rotation.toRotationSystem
      (majorityRetainedKeep G oldShore))
    (leftRotation : Equiv.Perm L)
    (hrev : OrientationReversing matching leftRotation
      (canonicalHubRotation rotation.toRotationSystem
        (majorityRetainedKeep G oldShore)))
    (hstate : normalizedState rotation oldShore oldOuter k oldWidth =
      normalizedState rotation newShore newOuter k newWidth) :
    OrientationReversing
        (matching.trans
          ((boundaryCoordinate rotation oldShore k oldWidth).trans
            (boundaryCoordinate rotation newShore k newWidth).symm))
        leftRotation
        (canonicalHubRotation rotation.toRotationSystem
          (majorityRetainedKeep G newShore)) ∧
      normalizedTaitInnerSupport k
          (innerTangle rotation oldShore oldOuter)
          (boundaryCoordinate rotation oldShore k oldWidth) =
        normalizedTaitInnerSupport k
          (innerTangle rotation newShore newOuter)
          (boundaryCoordinate rotation newShore k newWidth) := by
  exact GoertzelV24NormalizedSeamState.replacement_receipt k matching
    leftRotation
    (canonicalHubRotation rotation.toRotationSystem
      (majorityRetainedKeep G oldShore))
    (canonicalHubRotation rotation.toRotationSystem
      (majorityRetainedKeep G newShore))
    (boundaryCoordinate rotation oldShore k oldWidth)
    (boundaryCoordinate rotation newShore k newWidth)
    (innerTangle rotation oldShore oldOuter)
    (innerTangle rotation newShore newOuter) hrev hstate

end

end GoertzelV24MajorityShoreNormalizedState

end Mettapedia.GraphTheory.FourColor
