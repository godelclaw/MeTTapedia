import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacement
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceImpossibility

/-!
# Audit consequences for replacement positive geometry

This module keeps the inconsistency lemmas for canonical/source-preserving
one-collar repairs out of the live replacement-geometry API.  The live API
states the reusable positive geometry surfaces; this audit layer imports the
heavier impossibility material when those negative consequences are needed.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- A nonempty carrier rules out adding closed-walk source data plus canonical witness choice on
the same embedding. -/
theorem not_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_of_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    ¬ ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData) := by
  rintro ⟨source, hchoice⟩
  exact
    not_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb ⟨source, hchoice, hCarrier⟩

/-- A nonempty carrier also rules out closed-walk source data plus source-preserving one-collar
geometry on the same embedding. -/
theorem not_exists_closedWalkAnnulusBoundarySource_and_oneCollarGeometry_of_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    ¬ ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ collar : PlanarBoundaryAnnulusCollarGeometry emb,
        collar.numCollars = 1 ∧
          collar.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
            source.toPlanarBoundaryAnnulusBoundaryData := by
  rintro ⟨source, collar, hnum, hboundary⟩
  exact
    not_exists_closedWalkAnnulusBoundarySource_and_oneCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
      emb ⟨source, collar, hnum, hboundary, hCarrier⟩

end Mettapedia.GraphTheory.FourColor
