import Mettapedia.GraphTheory.FourColor.Compositional.CyclePushOffCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24ResidualReturnSectorNoncrossing

/-!
# Bounded physical transversals from residual-return separators

A physical residual return and the carrier interval between its endpoints
form a simple primal separator.  Sphericity supplies its exact binary face
cut.  Pushing either face label to a filled vertex side then produces a
literal finite edge interface supported at the separator, with a uniform
cubic width bound.

This module is the route adapter from residual-return geometry to a bounded
physical interface.  It does not assert that both complementary vertex sides
already contain cycles; that is the remaining cyclic-cut obligation for a
nested family.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnTransversal

open CyclePushOffCut
open AlternatingSiteGeometry
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory.Embedding
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-! The theorem below names its separator once in the result type.  Besides
matching the mathematics, this keeps elaboration from repeatedly reducing the
large residual-return construction while comparing dependent cut types. -/

/-- Every physical residual-return separator admits an exact face cut whose
two pushed-off vertex sides have bounded physical edge interfaces.  The
factor three is the robust cubic incidence bound; no chosen enumeration of
ports is involved. -/
theorem exists_exactFaceCut_with_bounded_pushOff_edges
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    (chord : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (hlong : 1 < chord.right.val - chord.left.val) :
    let separator := orderedReturnSeparator hG sigma hSigma site chord
    ∃ cut : ExactFaceCut rotation.toRotationSystem
        (fun edge : G.edgeSet => edge.1 ∈ separator.edges) F2,
      ∀ selected : F2,
        (CyclePushOffCut.edges rotation separator cut selected).card ≤
          separator.support.toFinset.card * 3 := by
  dsimp only
  rcases exactFaceCut_orderedReturnSeparator_of_minimal
      rotation minimal hG sigma hSigma site chord hlong with
    ⟨cut, _hboundary⟩
  refine ⟨cut, ?_⟩
  intro selected
  apply card_edges_le_support_mul_degreeBound
    rotation minimal.vertexRotationCyclic
      (orderedReturnSeparator hG sigma hSigma site chord) cut selected 3
  intro vertex _hvertex
  exact (incidentEdgeFinset_card_eq_three_of_hasCubicIncidentEdgeTriples
    hG vertex).le

end

end Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnTransversal
