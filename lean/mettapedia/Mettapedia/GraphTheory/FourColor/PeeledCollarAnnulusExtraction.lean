import Mettapedia.GraphTheory.FourColor.PeeledCollarCutLiftLocalConstancy
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusGeometry

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V W : Type*} [DecidableEq V]

/--
Named annulus-extraction foundation target for the peeled-collar regime route.
The current annulus API supplies face layers and boundary edge sets; the still
missing extraction theorem must turn that geometry, together with an embedded
collar graph, into the equivalent local/off-boundary side condition for every
small cyclic collar cut.

This definition is deliberately a target, not a theorem from annulus geometry.
-/
def PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (_data : PlanarBoundaryAnnulusCollarGeometry emb)
    {H : SimpleGraph W} (φ : H ↪g G) : Prop :=
  PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ

/--
The repaired previous-boundary annulus geometry uses the same extraction
target, but keeps the stronger geometry package in the statement for callers
that have already discharged the witness-placement seam.
-/
def PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (_data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    {H : SimpleGraph W} (φ : H ↪g G) : Prop :=
  PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ

/-- The annulus-extraction target is exactly the local-constancy bridge input. -/
theorem peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_annulusExtractionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G}
    (h :
      PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget data φ) :
    PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ :=
  h

/-- The previous-boundary annulus-extraction target is exactly the local-constancy bridge input. -/
theorem
    peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_previousBoundaryAnnulusExtractionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget data φ) :
    PeeledCollarCutAmbientSideLocalConstanciesToAmbient φ :=
  h

/-- Annulus extraction supplies the graph-facing small-cut lift. -/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_annulusExtractionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G}
    (h :
      PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget data φ) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G H :=
  peeledCollarSmallCyclicCutLiftsToAmbient_of_localConstancies
    (peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_annulusExtractionTarget h)

/-- Previous-boundary annulus extraction supplies the graph-facing small-cut lift. -/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_previousBoundaryAnnulusExtractionTarget
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G}
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget data φ) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G H :=
  peeledCollarSmallCyclicCutLiftsToAmbient_of_localConstancies
    (peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_previousBoundaryAnnulusExtractionTarget h)

/--
Regime-facing inheritance theorem from the named annulus-extraction target.
The ambient minimal-counterexample regime supplies the no-small-cut obstruction;
the annulus extraction target supplies the collar-to-ambient cut lift.
-/
theorem peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_annulusExtractionTarget
    [DecidableEq W]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusCollarGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (h :
      PlanarBoundaryAnnulusPeeledCollarLocalConstancyTarget data φ) :
    CyclicallyFiveEdgeConnected H :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_localConstancies
    regime
    (peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_annulusExtractionTarget h)

/--
Regime-facing inheritance theorem from the repaired previous-boundary
annulus-extraction target.
-/
theorem
    peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_previousBoundaryAnnulusExtractionTarget
    [DecidableEq W]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb}
    {H : SimpleGraph W} {φ : H ↪g G}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (h :
      PlanarBoundaryPreviousBoundaryPeeledCollarLocalConstancyTarget data φ) :
    CyclicallyFiveEdgeConnected H :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_localConstancies
    regime
    (peeledCollarCutAmbientSideLocalConstanciesToAmbient_of_previousBoundaryAnnulusExtractionTarget h)

end Mettapedia.GraphTheory.FourColor
