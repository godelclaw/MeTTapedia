import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputPort

/-!
# Exact outgoing face-cap support for one source Cell

The outgoing profile records the number of distinct primal edges in each
regional face fragment, capped at five.  The finite facial recurrence is
rooted at literal dart occurrences instead.  This file proves that the two
representations have exactly the same edge support: the fragment support is
the image of the full regional dart component of its canonical cut occurrence.

This identifies the exact quantity that a later finite cap decoder must
compute.  It does not yet compute that cardinality from the fixed transition
code, sum overlapping predecessor components, or claim a complete one-Cell
support letter.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputFragment
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputPort
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialCellFaceFiniteOutputCapEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Membership in the canonical distinct-edge component support is witnessed
by a literal dart occurrence connected to the chosen root. -/
theorem mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff
    (RS : RotationSystem V G.edgeSet) (region : Finset G.edgeSet)
    (start : RS.D) (edge : G.edgeSet) :
    edge ∈ sourceLocalLayerBoundaryRebaseFaceComponentEdges RS region start ↔
      edge ∈ region ∧
        ∃ dart : {dart : RS.D // dart ∈ RS.dartsOn edge},
          (faceRegionalDartGraph RS region).Reachable start dart.1 := by
  classical
  constructor
  · intro hedge
    rw [sourceLocalLayerBoundaryRebaseFaceComponentEdges] at hedge
    rcases Finset.mem_image.mp hedge with ⟨dart, hdart, hedgeOf⟩
    rw [Finset.mem_filter] at hdart
    exact ⟨hedgeOf ▸ hdart.2.1,
      ⟨⟨dart, (RS.mem_dartsOn).2 hedgeOf⟩, hdart.2.2⟩⟩
  · rintro ⟨hedgeRegion, dart, hreachable⟩
    rw [sourceLocalLayerBoundaryRebaseFaceComponentEdges]
    apply Finset.mem_image.mpr
    refine ⟨dart.1, ?_, (RS.mem_dartsOn).1 dart.2⟩
    rw [Finset.mem_filter]
    have hedgeOf : RS.edgeOf dart.1 = edge := (RS.mem_dartsOn).1 dart.2
    exact ⟨Finset.mem_univ _,
      ⟨by simpa only [hedgeOf] using hedgeRegion, hreachable⟩⟩

/-- An outgoing occurrence-sensitive fragment and the regional component of
its canonical cut dart have exactly the same distinct primal-edge support. -/
theorem boundaryRegionalFragmentEdges_eq_componentEdges
    (RS : RotationSystem V G.edgeSet) (cut region : Finset G.edgeSet)
    (fragment : BoundaryRegionalFragment RS cut region) :
    boundaryRegionalFragmentEdges RS cut region fragment =
      sourceLocalLayerBoundaryRebaseFaceComponentEdges RS region
        (boundaryRegionalFragmentDartOccurrence RS cut region fragment).1 := by
  classical
  ext edge
  rw [mem_sourceLocalLayerBoundaryRebaseFaceComponentEdges_iff]
  constructor
  · intro hedge
    have hedgeBoth :=
      GoertzelV24RotationFaceFragments.faceRegionalFragmentEdges_subset_boundary_inter_region RS
        (orbitFaceRoot RS fragment.1.1) region fragment.2.1 hedge
    have hedgeRegion : edge ∈ region := (Finset.mem_inter.mp hedgeBoth).2
    rcases (edge_mem_boundaryRegionalFragmentEdges_iff_exists_dart_reachable
      RS cut region fragment edge hedgeRegion).1 hedge with ⟨dart, hreach⟩
    exact ⟨hedgeRegion, dart, hreach.symm⟩
  · rintro ⟨hedgeRegion, dart, hreach⟩
    exact (edge_mem_boundaryRegionalFragmentEdges_iff_exists_dart_reachable
      RS cut region fragment edge hedgeRegion).2 ⟨dart, hreach.symm⟩

/-- Capping at any threshold commutes with the exact support identification.
For the corridor profile the threshold is five. -/
theorem min_card_boundaryRegionalFragmentEdges_eq_componentEdges
    (RS : RotationSystem V G.edgeSet) (cut region : Finset G.edgeSet)
    (fragment : BoundaryRegionalFragment RS cut region) (threshold : Nat) :
    min (boundaryRegionalFragmentEdges RS cut region fragment).card threshold =
      min (sourceLocalLayerBoundaryRebaseFaceComponentEdges RS region
        (boundaryRegionalFragmentDartOccurrence RS cut region fragment).1).card
        threshold := by
  rw [boundaryRegionalFragmentEdges_eq_componentEdges]

end

end GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteOutputCap

end Mettapedia.GraphTheory.FourColor
