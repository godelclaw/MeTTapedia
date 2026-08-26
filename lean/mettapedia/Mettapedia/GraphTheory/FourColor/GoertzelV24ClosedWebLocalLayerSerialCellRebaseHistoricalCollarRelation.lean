import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseBoundaryHistory

/-!
# Expose the primal-edge relation behind a historical facial-collar hit

The expanded facial receipt names a switch dart and its two immediate
face-orbit neighbours.  Consequently, if one of those coordinates aliases a
strict historical Cell, its primal edge either is the switch edge or is
adjacent to it.  This file records that exact reduction and exposes which of
the three switch roles is involved.

No corridor-separation conclusion is asserted here.  The remaining geometric
step is now an edge-local statement rather than a forty-eight-slot dart case
split.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance cellRebaseHistoricalCollarRelationEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- A collar coordinate lies over its root edge or over a primal edge
adjacent to the root edge.  The statement applies to arbitrary rotation
systems, including the opened carrier with degree-one boundary stubs. -/
theorem edgeOf_rebaseFaceCollarDartAt_eq_or_adj
    (RS : RotationSystem V G.edgeSet) (root : RS.D)
    (direction : SourceLocalLayerSerialCellRebaseFaceCollarDirection) :
    RS.edgeOf (sourceLocalLayerSerialCellRebaseFaceCollarDartAt RS root
        direction) = RS.edgeOf root ∨
      RS.edgeAdjacencyGraph.Adj
        (RS.edgeOf
          (sourceLocalLayerSerialCellRebaseFaceCollarDartAt RS root direction))
        (RS.edgeOf root) := by
  cases direction with
  | center => exact Or.inl rfl
  | forward =>
      simp only [sourceLocalLayerSerialCellRebaseFaceCollarDartAt]
      by_cases hedge : RS.edgeOf (RS.phi root) = RS.edgeOf root
      · exact Or.inl hedge
      · apply Or.inr
        apply RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges hedge
        · apply (RS.mem_incidentEdges_iff).2
          exact ⟨RS.phi root, rfl, rfl⟩
        · apply (RS.mem_incidentEdges_iff).2
          exact ⟨RS.alpha root, RS.edge_alpha root,
            (RS.vert_phi_eq_vert_alpha root).symm⟩
  | backward =>
      simp only [sourceLocalLayerSerialCellRebaseFaceCollarDartAt]
      by_cases hedge : RS.edgeOf (RS.phi.symm root) = RS.edgeOf root
      · exact Or.inl hedge
      · apply Or.inr
        apply RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges hedge
        · apply (RS.mem_incidentEdges_iff).2
          refine ⟨RS.alpha (RS.phi.symm root),
            RS.edge_alpha (RS.phi.symm root), ?_⟩
          simpa using (RS.vert_phi_eq_vert_alpha (RS.phi.symm root)).symm
        · apply (RS.mem_incidentEdges_iff).2
          exact ⟨root, rfl, rfl⟩

/-- A decoded strict-history occurrence comes from a literal switch
occurrence.  Its root is the consumed rung, a successor incoming crossing, or
the successor rung, and the historical edge is equal or adjacent to that
root. -/
theorem sourceLocalLayerSerialCellRebase_strictHistory_collar_relation
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (slot : SourceLocalLayerSerialCellRebaseExpandedFaceInterface)
    (dart : web.annular.RS.D)
    (hdecode : sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? corridor
      hunique offset hnext hcell slot = some dart)
    (prior : Fin (blockLength - 3))
    (_hprior : prior.val < offset.val)
    (_hhistory : web.annular.RS.edgeOf dart ∈
      sourceLocalLayerCellRegionAt corridor hunique prior)
    (hnew : dart ∉
      sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset) :
    ∃ occurrence : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt corridor
        hunique offset hnext,
      ∃ direction : SourceLocalLayerSerialCellRebaseFaceCollarDirection,
        dart = sourceLocalLayerSerialCellRebaseFaceCollarDartAt web.annular.RS
            occurrence.1 direction ∧
          (web.annular.RS.edgeOf occurrence.1 =
                sourceLocalLayerSharedRungAt corridor hunique offset ∨
            (∃ step : Fin 2,
              web.annular.RS.edgeOf occurrence.1 =
                sourceLocalLayerLeftCrossingAt corridor hunique
                  (sourceLocalLayerNextOffset offset hnext) step) ∨
            web.annular.RS.edgeOf occurrence.1 =
              sourceLocalLayerSharedRungAt corridor hunique
                (sourceLocalLayerNextOffset offset hnext)) ∧
          (web.annular.RS.edgeOf dart = web.annular.RS.edgeOf occurrence.1 ∨
            web.annular.RS.edgeAdjacencyGraph.Adj
              (web.annular.RS.edgeOf dart)
              (web.annular.RS.edgeOf occurrence.1)) := by
  rcases slot with oldSlot | ⟨occurrenceSlot, direction⟩
  · unfold sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? at hdecode
    cases hsource : sourceLocalLayerSerialFaceTransitionDartAtSlot? corridor
        hunique offset hcell oldSlot with
    | none => simp [hsource] at hdecode
    | some oldDart =>
        simp only [hsource, Option.map_some, Option.some.injEq] at hdecode
        subst dart
        exact (hnew oldDart.2).elim
  · unfold sourceLocalLayerSerialCellRebaseExpandedFaceDartAtSlot? at hdecode
    cases hsource : sourceLocalLayerBoundaryRebaseFaceOccurrenceAtSlot?
        corridor hunique offset hnext occurrenceSlot with
    | none => simp [hsource] at hdecode
    | some occurrence =>
        simp only [hsource, Option.map_some, Option.some.injEq] at hdecode
        subst dart
        refine ⟨occurrence, direction, rfl, ?_, ?_⟩
        · exact sourceLocalLayerBoundaryRebaseFaceOccurrence_edge_cases
            corridor hunique offset hnext occurrence
        · exact edgeOf_rebaseFaceCollarDartAt_eq_or_adj web.annular.RS
            occurrence.1 direction

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
