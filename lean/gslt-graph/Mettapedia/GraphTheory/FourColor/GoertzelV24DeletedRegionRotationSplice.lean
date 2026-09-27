import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutTaitSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationVertexCutProfile

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DeletedRegionRotationSplice

open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24RotationVertexCutProfile

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The vertices retained after deleting a finite corridor region. -/
def deletedRegionKeep (deleted : Finset V) (vertex : V) : Prop :=
  vertex ∉ deleted

/-- Every endpoint-computed crossing edge has a uniquely directed retained
half-edge pointing into the deleted region. Existence is derived from the
two-dart edge fiber and the crossing predicate. -/
theorem exists_outward_dart_of_mem_vertexSetCrossingEdges
    (RS : RotationSystem V E) (deleted : Finset V) {edge : E}
    (hedge : edge ∈ vertexSetCrossingEdges RS deleted) :
    ∃ dart : RS.D,
      RS.edgeOf dart = edge ∧
      deletedRegionKeep deleted (RS.vertOf dart) ∧
      ¬ deletedRegionKeep deleted (RS.vertOf (RS.alpha dart)) := by
  rcases (mem_vertexSetCrossingEdges_iff RS deleted edge).1 hedge with
    ⟨inner, hinnerEndpoint, hinnerDeleted,
      outer, houterEndpoint, houterRetained⟩
  rcases (RS.mem_endpoints_iff).1 hinnerEndpoint with
    ⟨innerDart, hinnerDartOn, hinnerDartVertex⟩
  have hpairs := RS.endpoints_eq_pair_of_mem hinnerDartOn
  have houterCases :
      outer = RS.vertOf innerDart ∨
        outer = RS.vertOf (RS.alpha innerDart) := by
    rw [hpairs] at houterEndpoint
    simpa using houterEndpoint
  have houterAlpha : RS.vertOf (RS.alpha innerDart) = outer := by
    rcases houterCases with houterInner | houterAlpha
    · exfalso
      apply houterRetained
      rw [houterInner, hinnerDartVertex]
      exact hinnerDeleted
    · exact houterAlpha.symm
  refine ⟨RS.alpha innerDart, ?_, ?_, ?_⟩
  · rw [RS.edge_alpha]
    exact (RS.mem_dartsOn).1 hinnerDartOn
  · exact houterAlpha ▸ houterRetained
  · intro hkept
    apply hkept
    rw [RS.alpha_involutive, hinnerDartVertex]
    exact hinnerDeleted

/-- Conversely, every exposed retained dart is supported on the actual
endpoint-computed boundary of the deleted region. -/
theorem boundaryDart_edge_mem_vertexSetCrossingEdges
    (RS : RotationSystem V E) (deleted : Finset V)
    (dart : BoundaryDart RS (deletedRegionKeep deleted)) :
    RS.edgeOf dart.1.1 ∈ vertexSetCrossingEdges RS deleted := by
  rw [mem_vertexSetCrossingEdges_iff]
  have hdartOn : dart.1.1 ∈ RS.dartsOn (RS.edgeOf dart.1.1) := by
    simp
  have hpairs := RS.endpoints_eq_pair_of_mem hdartOn
  refine ⟨RS.vertOf (RS.alpha dart.1.1), ?_, ?_,
    RS.vertOf dart.1.1, ?_, ?_⟩
  · rw [hpairs]
    simp
  · by_contra hnotDeleted
    exact dart.2 hnotDeleted
  · rw [hpairs]
    simp
  · exact dart.1.2

/-- If two ordered cuts partition the endpoint boundary, they cover every
exposed retained dart. -/
theorem deletedRegionBoundaryCover
    (RS : RotationSystem V E) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → E)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges RS deleted)
    (dart : BoundaryDart RS (deletedRegionKeep deleted)) :
    RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
      RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing := by
  rw [← Finset.mem_union]
  rw [hboundary]
  exact boundaryDart_edge_mem_vertexSetCrossingEdges RS deleted dart

/-- Each position of the left ordered cut has the outward orientation needed
by the splice constructor. -/
theorem leftCrossing_outward
    (RS : RotationSystem V E) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → E)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges RS deleted)
    (step : Fin n) :
    ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      deletedRegionKeep deleted (RS.vertOf dart) ∧
      ¬ deletedRegionKeep deleted (RS.vertOf (RS.alpha dart)) := by
  apply exists_outward_dart_of_mem_vertexSetCrossingEdges RS deleted
  rw [← hboundary]
  exact Finset.mem_union_left _
    (Finset.mem_image.2 ⟨step, Finset.mem_univ _, rfl⟩)

/-- Each position of the right ordered cut has the outward orientation needed
by the splice constructor. -/
theorem rightCrossing_outward
    (RS : RotationSystem V E) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → E)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges RS deleted)
    (step : Fin n) :
    ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      deletedRegionKeep deleted (RS.vertOf dart) ∧
      ¬ deletedRegionKeep deleted (RS.vertOf (RS.alpha dart)) := by
  apply exists_outward_dart_of_mem_vertexSetCrossingEdges RS deleted
  rw [← hboundary]
  exact Finset.mem_union_right _
    (Finset.mem_image.2 ⟨step, Finset.mem_univ _, rfl⟩)

/-- Concrete deleted-region rotation splice. The retained side, both cut
orientations, and boundary coverage are all derived from endpoint incidence. -/
def deletedRegionRewiredDartSystem
    (RS : RotationSystem V E) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → E)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges RS deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : RS.vertOf RS.outer ∉ deleted)
    (hseamEndpoints : ∀ step,
      RS.vertOf
          (orderedBoundaryDart RS (deletedRegionKeep deleted) leftCrossing
            (leftCrossing_outward RS deleted leftCrossing rightCrossing
              hboundary) step).1.1.1 ≠
        RS.vertOf
          (orderedBoundaryDart RS (deletedRegionKeep deleted) rightCrossing
            (rightCrossing_outward RS deleted leftCrossing rightCrossing
              hboundary) step).1.1.1) :
    RewiredDartSystem V
      (MatchedSeam.Dart (InternalDart RS (deletedRegionKeep deleted))
        (BoundaryDartOn RS (deletedRegionKeep deleted)
          (orderedCut leftCrossing))
        (BoundaryDartOn RS (deletedRegionKeep deleted)
          (orderedCut rightCrossing))) :=
  orderedCutRewiredDartSystem RS (deletedRegionKeep deleted)
    leftCrossing rightCrossing
    (leftCrossing_outward RS deleted leftCrossing rightCrossing hboundary)
    (rightCrossing_outward RS deleted leftCrossing rightCrossing hboundary)
    hleftInjective hrightInjective
    (deletedRegionBoundaryCover RS deleted leftCrossing rightCrossing hboundary)
    hdisjoint houter hseamEndpoints

/-- The corresponding complete shortened rotation system. -/
def deletedRegionRotationSystem
    (RS : RotationSystem V E) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → E)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges RS deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : RS.vertOf RS.outer ∉ deleted)
    (hseamEndpoints : ∀ step,
      RS.vertOf
          (orderedBoundaryDart RS (deletedRegionKeep deleted) leftCrossing
            (leftCrossing_outward RS deleted leftCrossing rightCrossing
              hboundary) step).1.1.1 ≠
        RS.vertOf
          (orderedBoundaryDart RS (deletedRegionKeep deleted) rightCrossing
            (rightCrossing_outward RS deleted leftCrossing rightCrossing
              hboundary) step).1.1.1) :
    RotationSystem V
      (deletedRegionRewiredDartSystem RS deleted leftCrossing rightCrossing
        hboundary hleftInjective hrightInjective hdisjoint houter
        hseamEndpoints).Edge :=
  (deletedRegionRewiredDartSystem RS deleted leftCrossing rightCrossing
    hboundary hleftInjective hrightInjective hdisjoint houter
    hseamEndpoints).toRotationSystem

end

end GoertzelV24DeletedRegionRotationSplice

end Mettapedia.GraphTheory.FourColor
