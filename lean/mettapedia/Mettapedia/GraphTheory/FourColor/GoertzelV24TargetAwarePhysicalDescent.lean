import Mettapedia.GraphTheory.FourColor.GoertzelV24MajorityShorePhysicalReplacement
import Mettapedia.GraphTheory.FourColor.GoertzelV24TargetAwareSupportReplacement
import Mettapedia.GraphTheory.FourColor.StructuralCutCyclicMatching

/-!
# Target-aware obstruction to physical shortening

The equal-state replacement theorem uses more semantic information than its
minimality argument needs. For any *actual* structurally valid strict splice,
the replacement inner piece cannot have Tait-word support contained in that of
the removed inner piece: such an inclusion would preserve zero colourability
and contradict vertex minimality. This statement does not manufacture a
structurally valid matching or prove that a mesh supplies the two shores.
-/

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TargetAwarePhysicalDescent

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24MajorityShorePhysicalReplacement
open GoertzelV24TargetAwareSupportReplacement
open GoertzelV24PhysicalClosedCountBridge
open GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24MajorityShoreNormalizedState
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SimpleGraphTaitBridge
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24VertexSideReassembly
open GoertzelV24VertexSideOpenTangle
open GoertzelV24CanonicalHubClosure
open GoertzelV24SeamExchange
open StructuralCutCyclicMatching

noncomputable section

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- A minimal counterexample forces a genuine boundary word realized by the
new inner shore but not by the old one, for every strict spherical splice.
The matching is a physical matching of boundary darts; no normalized-state
equality is required. -/
theorem not_taitInnerSupport_subset_of_strict_splice
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (oldShore newShore : Finset G.edgeSet)
    (hshore : newShore ⊆ oldShore)
    (outsideOuter : RetainedDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore))
    (oldInnerOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G oldShore))
    (newInnerOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G newShore))
    (matching : BoundaryDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore) ≃
      BoundaryDart rotation.toRotationSystem
        (majorityRetainedKeep G newShore))
    (hstruct : BridgelessSphericalCubicMapData
      ((outsideTangle rotation oldShore outsideOuter).composeRotationSystem
        (innerTangle rotation newShore newInnerOuter) matching))
    (strictVertex : V)
    (hall : ∀ edge ∈ incidentEdgeFinset G strictVertex,
      edge ∈ oldShore \ newShore) :
    ¬ taitInnerSupport
        (rightClosedPortTangle
          (innerTangle rotation newShore newInnerOuter) matching) ⊆
      taitInnerSupport
        (rightClosedPortTangle
          (innerTangle rotation oldShore oldInnerOuter)
          (oldExteriorMatching rotation oldShore)) := by
  intro hsupport
  let oldMatching := oldExteriorMatching rotation oldShore
  let outside := outsideTangle rotation oldShore outsideOuter
  let oldInner := innerTangle rotation oldShore oldInnerOuter
  let newInner := innerTangle rotation newShore newInnerOuter
  have hzeroOld :
      ¬ RotationSystemTaitColorable
        (outside.composeRotationSystem oldInner oldMatching) := by
    intro hcolorable
    exact minimal.notColorable
      ((rotationSystemTaitColorable_swappedComplementaryComposite_iff
        rotation.toRotationSystem (majorityDeletedVertices G oldShore)
        outsideOuter oldInnerOuter).1 hcolorable)
  have hzeroNew :
      ¬ RotationSystemTaitColorable
        (outside.composeRotationSystem newInner matching) :=
    not_composeRotationSystem_taitColorable_of_taitInnerSupport_subset
      outside oldInner oldMatching newInner matching hsupport hzeroOld
  have hsmall := replacementVertexCount_lt_of_incident_sdiff
    rotation oldShore newShore hshore strictVertex hall
    minimal.spherical.cubic
  exact hzeroNew
    (minimal.smallerColorable
      (outside.composeRotationSystem newInner matching) hsmall hstruct)

/-- Equal-width connected physical bonds can always be sewn spherically, but
in a vertex-minimal counterexample every such strict shortening faces a
*semantic* obstruction: for the exhibited cyclic matching, some genuine Tait
boundary word of the new interior was not realizable by the old interior.

Unlike the older equal-normalized-state descent, this theorem assumes no
equality of boundary rotations or supports. Its conclusion pinpoints the
remaining obstruction rather than hiding it in a composite state. -/
theorem exists_unmatched_tait_word_of_equal_width_bonds
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (oldShore newShore : Finset G.edgeSet)
    (hshore : newShore ⊆ oldShore)
    (outsideOuter : RetainedDart rotation.toRotationSystem
      (majorityDeletedKeep G oldShore))
    (oldInnerOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G oldShore))
    (newInnerOuter : RetainedDart rotation.toRotationSystem
      (majorityRetainedKeep G newShore))
    (hOldInside :
      (G.induce {v | majorityRetainedKeep G oldShore v}).Connected)
    (hOldOutside :
      (G.induce {v | majorityDeletedKeep G oldShore v}).Connected)
    (hNewInside :
      (G.induce {v | majorityRetainedKeep G newShore v}).Connected)
    (hNewOutside :
      (G.induce {v | majorityDeletedKeep G newShore v}).Connected)
    (hwidth : boundaryWidth rotation oldShore =
      boundaryWidth rotation newShore)
    (strictVertex : V)
    (hall : ∀ edge ∈ incidentEdgeFinset G strictVertex,
      edge ∈ oldShore \ newShore) :
    ∃ matching : BoundaryDart rotation.toRotationSystem
        (majorityDeletedKeep G oldShore) ≃
        BoundaryDart rotation.toRotationSystem
          (majorityRetainedKeep G newShore),
      OrientationReversing matching
        (canonicalHubRotation rotation.toRotationSystem
          (majorityDeletedKeep G oldShore))
        (canonicalHubRotation rotation.toRotationSystem
          (majorityRetainedKeep G newShore)) ∧
      ∃ word,
        word ∈ taitInnerSupport
          (rightClosedPortTangle
            (innerTangle rotation newShore newInnerOuter) matching) ∧
        word ∉ taitInnerSupport
          (rightClosedPortTangle
            (innerTangle rotation oldShore oldInnerOuter)
            (oldExteriorMatching rotation oldShore)) := by
  obtain ⟨matching, hrev, hstruct⟩ :=
    exists_structural_majority_replacement rotation
      minimal.toBridgelessSphericalCubicMapData minimal.facesTwoSided
      oldShore newShore outsideOuter newInnerOuter
      hOldInside hOldOutside hNewInside hNewOutside hwidth
  have hnot := not_taitInnerSupport_subset_of_strict_splice
    rotation minimal oldShore newShore hshore
    outsideOuter oldInnerOuter newInnerOuter matching hstruct
    strictVertex hall
  obtain ⟨word, hnew, hold⟩ := Set.not_subset.mp hnot
  exact ⟨matching, hrev, word, hnew, hold⟩

end
end Mettapedia.GraphTheory.FourColor.GoertzelV24TargetAwarePhysicalDescent
