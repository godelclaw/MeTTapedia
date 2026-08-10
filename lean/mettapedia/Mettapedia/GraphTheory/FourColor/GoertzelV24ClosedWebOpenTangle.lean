import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebAtGoodWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# The Cell-3 carrier is an open tangle

The source's closed-web-at-good-word cell is an annular tangle: its named
inner and outer interface vertices have degree one.  It must therefore not be
identified with the closed cubic graph used by the global minimal-counterexample
normal form.  Any later use of closed ambient normality has to pass through an
explicit cap-deletion or closure construction.

This small guard theorem makes that type distinction kernel-visible, so a
vacuous closed-cubic-minimal hypothesis cannot silently enter the Cell-3
splice.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebBoundaryData
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebOpenTangleEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance

/-- A Cell-3 open tangle cannot itself carry the closed cubic
minimal-counterexample structure: its first inner stub has degree one, while
that structure makes every vertex cubic. -/
theorem graphBackedVertexMinimalTaitCounterexample_elim
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    (minimal : GraphBackedVertexMinimalTaitCounterexample
      web.annular.cellulation.rotation) : False := by
  have hregular : G.IsRegularOfDegree 3 :=
    web.annular.cellulation.rotation.toRotationSystem_isCubic_iff.mp
      minimal.spherical.cubic
  have hone : G.degree (data.innerStub 0) = 1 := by
    rw [← GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree
      (G := G)]
    exact web.boundary_wellFormed.inner_stub_degree_one 0
  have hthree : G.degree (data.innerStub 0) = 3 :=
    hregular (data.innerStub 0)
  omega

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
