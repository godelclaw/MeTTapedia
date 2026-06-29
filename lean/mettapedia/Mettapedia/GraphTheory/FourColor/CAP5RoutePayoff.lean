import Mettapedia.GraphTheory.FourColor.CAP5RouteVerdict
import Mettapedia.GraphTheory.FourColor.Goal
import Mettapedia.GraphTheory.FourColor.Theorem49WheelWithInnerTriangleBenchmark

/-!
# CAP5 route payoff as a real coloring statement

This module records the coloring object obtained from the closed CAP5/F2 route
surface.  The route is still about the Theorem 4.9 synthesis layer; it does
not by itself supply the nonzero-color condition needed for Tait colorability.
That extra bridge is named explicitly below.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem color_card : Fintype.card Color = 4 := by
  decide

/- Any proper edge coloring by the four-element `Color` type is real line-graph 4-colorability. -/
omit [DecidableEq V] in
theorem edgeColorable_four_of_color_edgeColoring (C : G.EdgeColoring Color) :
    G.EdgeColorable 4 := by
  simpa [SimpleGraph.EdgeColorable, color_card] using
    (SimpleGraph.Coloring.colorable C)

variable [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]

/--
The real coloring payoff currently justified by a closed CAP5/F2 route certificate.
The theorem-4.9 part comes from `CAP5F2RouteClosed`; the `Colorable 4` object is
the line-graph coloring already carried by the route root `C₀`.
-/
structure CAP5RouteClosedColoringPayoff
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side) :
    Prop where
  routeClosed : CAP5F2RouteClosed cert
  synthesis : Theorem49BoundaryRootSynthesis emb C₀
  edgeColorable_four : G.EdgeColorable 4

theorem cap5RouteClosedColoringPayoff_of_routeClosed
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    {cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side}
    (hclosed : CAP5F2RouteClosed cert) :
    CAP5RouteClosedColoringPayoff cert where
  routeClosed := hclosed
  synthesis := hclosed.1
  edgeColorable_four := edgeColorable_four_of_color_edgeColoring C₀

/--
The exact additional bridge needed to upgrade a closed route to Tait colorability
from the route data alone: the root `Color` edge-coloring must be nonzero on
every edge.
-/
def CAP5RouteClosedRootTaitBridge
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side) :
    Prop :=
  CAP5F2RouteClosed cert → IsTaitEdgeColoring G C₀

theorem taitColorable_of_routeClosedRootTaitBridge
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    {cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side}
    (hbridge : CAP5RouteClosedRootTaitBridge cert)
    (hclosed : CAP5F2RouteClosed cert) :
    TaitColorable G :=
  ⟨C₀, hbridge hclosed⟩

/-- Decidable ingredients for the executable CAP5 primitive-checker report. -/
structure CAP5DecidableCheckerEvidence
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop) : Type _ where
  portal :
    ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).PortalCrosses)
  cycles :
    ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).SideCycles)
  realized :
    ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).RealizedSeparator)

namespace CAP5DecidableCheckerEvidence

noncomputable def report
    {boundaryEdge : Fin 5 → G.edgeSet} {side : V → Prop}
    (checks : CAP5DecidableCheckerEvidence (G := G) boundaryEdge side) :
    CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side := by
  classical
  letI := checks.portal
  letI := checks.cycles
  letI := checks.realized
  exact CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks boundaryEdge side

def noPrimitiveGapByFiniteCheck
    {boundaryEdge : Fin 5 → G.edgeSet} {side : V → Prop}
    (checks : CAP5DecidableCheckerEvidence (G := G) boundaryEdge side) : Prop :=
  checks.report.missingCheckerEvidenceLatents = []

end CAP5DecidableCheckerEvidence

/--
A finite checked route-closed certificate: executable primitive checker evidence is complete, and
the route endpoint itself is closed.  Supplying one of these for a concrete graph is the exact
canary obligation left by the current route surface.
-/
structure CAP5FiniteRouteClosedWitness
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color)) (p0Inside p4Inside : Bool)
    (side : V → Prop) : Type _ where
  checks : CAP5DecidableCheckerEvidence (G := G) boundaryEdge side
  cert : CAP5F2RouteCertificate data emb C₀ colorings p0Inside p4Inside side
  checkerClosed : checks.noPrimitiveGapByFiniteCheck
  routeClosed : CAP5F2RouteClosed cert

theorem CAP5FiniteRouteClosedWitness.coloringPayoff
    {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)} {p0Inside p4Inside : Bool}
    {side : V → Prop}
    (w :
      CAP5FiniteRouteClosedWitness data emb C₀ colorings p0Inside p4Inside side) :
    CAP5RouteClosedColoringPayoff w.cert :=
  cap5RouteClosedColoringPayoff_of_routeClosed w.routeClosed

namespace WheelCAP5RoutePayoff

open Theorem49PlanarBoundaryAnnulusWheelWitnessRegression

/-!
The wheel-with-inner-triangle benchmark is the concrete coloring canary currently available
from the maintained benchmark module.  The stronger CAP5 finite route-closed canary is the
existential `WheelCAP5FiniteRouteClosedCanary` below.
-/

structure WheelColoringCanary : Prop where
  edgeColorable_four : wheelWithInnerTriangleGraph.EdgeColorable 4
  taitColorable : TaitColorable wheelWithInnerTriangleGraph

theorem wheelColoringCanary : WheelColoringCanary where
  edgeColorable_four :=
    edgeColorable_four_of_color_edgeColoring wheelWithInnerTriangleTaitEdgeColoring
  taitColorable :=
    exists_taitEdgeColoring_wheelWithInnerTriangleGraph

/--
The exact missing positive canary requested at the CAP5 route layer: a concrete finite checker
and closed CAP5/F2 route certificate for the wheel benchmark.
-/
def WheelCAP5FiniteRouteClosedCanary : Prop :=
  ∃ (boundaryEdge : Fin 5 → wheelWithInnerTriangleGraph.edgeSet) (n : Nat)
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (colorings : Set (wheelWithInnerTriangleGraph.EdgeColoring Color))
    (p0Inside p4Inside : Bool) (side : Fin 7 → Prop),
      Nonempty
        (CAP5FiniteRouteClosedWitness data wheelWithInnerTriangleEmbedding
          wheelWithInnerTriangleTaitEdgeColoring colorings p0Inside p4Inside side)

theorem wheelColoringPayoff_of_CAP5FiniteRouteClosedCanary
    (hcanary : WheelCAP5FiniteRouteClosedCanary) :
    wheelWithInnerTriangleGraph.EdgeColorable 4 ∧
      TaitColorable wheelWithInnerTriangleGraph := by
  rcases hcanary with
    ⟨_boundaryEdge, _n, _data, _colorings, _p0Inside, _p4Inside, _side, hwitness⟩
  rcases hwitness with ⟨witness⟩
  exact
    ⟨(CAP5FiniteRouteClosedWitness.coloringPayoff witness).edgeColorable_four,
      exists_taitEdgeColoring_wheelWithInnerTriangleGraph⟩

end WheelCAP5RoutePayoff

end Mettapedia.GraphTheory.FourColor
