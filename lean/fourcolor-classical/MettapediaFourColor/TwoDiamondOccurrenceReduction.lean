import MettapediaFourColor.TwoDiamondHubColoring
import Mettapedia.GraphTheory.FourColor.OpenTangleVertexOccurrence

/-!
# Strict reduction of a shared-tip double diamond in its actual source

A supplied exact occurrence identifies the twenty-vertex piece with a
literal vertex shore. Its complementary shore supplies the actual exterior
and ordered seam. The eight-cycle replacement removes twelve vertices,
stays in the connected bridgeless spherical cubic class, and reconstructs
a colouring of the original source. The exterior need not be connected.

The occurrence hypothesis is geometric data, not a colouring assumption.
Deriving it from a source face pattern and proving coverage are separate
obligations. Reconstruction retains the configuration-6 repair certificate.
-/

namespace FourColor.TwoDiamondOccurrenceReduction

open Mettapedia.GraphTheory.FourColor
open SimpleGraphDartRotation GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition GoertzelV24DeletedRegionRotationSplice
open GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24TwoEdgeCutMinimality

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (deleted : Finset V)
  (root : RetainedDart rotation.toRotationSystem (deletedSideKeep deleted))
  (R : OpenTangleIsomorphism.Iso TwoDiamondTangle.piece
    (ofVertexSide rotation.toRotationSystem (deletedSideKeep deleted) root))

abbrev outside := OpenTangleVertexOccurrence.outside rotation.toRotationSystem
  deleted root TwoDiamondTangle.piece R 0

abbrev seam := (OpenTangleVertexOccurrence.ports rotation.toRotationSystem
  deleted root TwoDiamondTangle.piece R).symm

abbrev smaller := TwoDiamondCycleReplacement.reduced
  (outside rotation deleted root R) (seam rotation deleted root R)

include R

theorem source_vertex_count :
    Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 20) = Fintype.card V := by
  simpa only [Fintype.card_sum] using
    OpenTangleVertexOccurrence.vertex_count rotation.toRotationSystem
      deleted root TwoDiamondTangle.piece R

theorem vertex_loss :
    Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 8) + 12 = Fintype.card V := by
  rw [← source_vertex_count rotation deleted root R]
  exact TwoDiamondCycleReplacement.whole_vertex_loss

variable (h : BridgelessSphericalCubicMapData rotation.toRotationSystem)
include h

theorem assembled_class : BridgelessSphericalCubicMapData
    (TwoDiamondCycleReplacement.original
      (outside rotation deleted root R) (seam rotation deleted root R)) :=
  OpenTangleVertexOccurrence.assembled_class rotation.toRotationSystem
    deleted root TwoDiamondTangle.piece R 0 h

theorem smaller_class : BridgelessSphericalCubicMapData (smaller rotation deleted root R) :=
  TwoDiamondCycleReplacement.replacement_class _ _ (assembled_class rotation deleted root R h)

/-- Compatible choices from the supplied smaller colouring rebuild the actual
source, through exact reassembly of its original vertices and edge pairs. -/
theorem reconstruct (hc : RotationSystemTaitColorable (smaller rotation deleted root R)) :
    RotationSystemTaitColorable rotation.toRotationSystem := by
  apply (OpenTangleVertexOccurrence.colorable_iff rotation.toRotationSystem
    deleted root TwoDiamondTangle.piece R 0).mp
  exact TwoDiamondHubColoring.reconstruct _ _ (assembled_class rotation deleted root R h) hc

/-- All vertices of the replacement are counted; no source normal-form,
exterior connectivity or boundary-richness assumption is retained. -/
theorem strict_reduction_of_occurrence :
    Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 8) + 12 = Fintype.card V ∧
      Fintype.card ({v : V // deletedRegionKeep deleted v} ⊕ Fin 8) < Fintype.card V ∧
      BridgelessSphericalCubicMapData (smaller rotation deleted root R) ∧
      (RotationSystemTaitColorable (smaller rotation deleted root R) →
        RotationSystemTaitColorable rotation.toRotationSystem) := by
  have hv := vertex_loss rotation deleted root R
  exact ⟨hv, by omega, smaller_class rotation deleted root R h,
    reconstruct rotation deleted root R h⟩

omit h in
include R in
/-- Minimality supplies the smaller colouring. Recognition of this exact
piece therefore excludes a source from the minimal-counterexample class. -/
theorem not_in_minimal_counterexample_of_occurrence
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) : False := by
  obtain ⟨_, hlt, hs, hr⟩ := strict_reduction_of_occurrence rotation deleted root R
    minimal.toBridgelessSphericalCubicMapData
  exact minimal.notColorable (hr (minimal.smallerColorable _ hlt hs))

end
end FourColor.TwoDiamondOccurrenceReduction
