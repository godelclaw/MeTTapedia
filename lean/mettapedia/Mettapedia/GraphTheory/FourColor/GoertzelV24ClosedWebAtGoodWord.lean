import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierWeightedCorridor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialLength

/-!
# Closed-web-at-good-word instances

Addendum XXVII's shrinking argument is about a *closed web at a good word*,
not an arbitrary Tait coloring of a closed graph.  This file gives that source
object one Lean carrier.  Its fields are the concrete annular interface,
rotation-level hole realization, girth-five/dual geometry, proper coloring,
total closure, and the `(3,1,1)` inner word.

The two exported consequences deliberately follow the manuscript's order:
the weighted L1 corridor alternative comes from the annular geometry, while
the L8 radial-sector witness comes from total closure at the good word.  A
later splice must preserve this same object condition by condition; this file
does not replace that proof by a bare colorability statement.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open SimpleGraph
open GoertzelV24AnnularFrontierWeightedCorridor
open GoertzelV24AnnularFrontierWeightedCurvature.AnnularFrontier
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebRadialLength
open GoertzelV24ClosedWebTotalClosure

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The Cell-3 source instance consumed by the shrinking argument.  The
five-stub outer boundary is the sharp closed-web regime in Addenda XXI--XXVII:
it is where total closure and a good inner word force the two radial paths
used to form the finite profile corridor. -/
structure Instance
    (data : AnnularBoundaryData G 5) (coloring : G.EdgeColoring Color) where
  boundary_wellFormed : data.WellFormed
  connected : G.Connected
  annular : ClosedWebAnnularEmbedding data
  geometry : AnnularFrontierGeometry annular
  tait : IsTaitEdgeColoring G coloring
  totallyClosed : TotallyClosedWeb data coloring
  goodWord : CAP5BoundaryWordHasColoredBlock311
    (data.innerBoundaryWord coloring)

namespace Instance

/-- The annular L1 alternative for one source closed-web instance.  The
negative-curvature branch is retained explicitly: removing it would hide the
source's defect-budget obligation behind a supposed universal corridor. -/
theorem weight_exceeds_bound_or_hasCleanHexagonalGeodesicBlock
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    (weightBound blockLength : Nat) (hpositive : 0 < blockLength)
    (hlarge : boundedWeightCleanHexBlockThreshold web.annular
      weightBound blockLength < web.annular.cellulation.interiorFaces.card) :
    weightBound < interiorNegativeCurvatureWeight web.annular ∨
      HasCleanHexagonalGeodesicBlock web.annular blockLength := by
  exact _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierWeightedCorridor.weight_exceeds_bound_or_hasCleanHexagonalGeodesicBlock
      web.annular web.boundary_wellFormed web.geometry
      weightBound blockLength hpositive hlarge

/-- The constructed L8 package for a large closed web at a good word.  This
is the source's two radial paths, their disjoint facial anchors, and the
sector-alternation certificate; no path or sector datum is caller supplied. -/
theorem exists_longRadialSectorWitness
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    (bound : Nat)
    (hlarge : 2 * (bound + 1) < data.interiorVertices.card) :
    ∃ majority first second : Color,
      ∃ htriple : IsTaitColorTriple majority first second,
        Nonempty (LongRadialSectorWitness
          web.annular web.boundary_wellFormed coloring
          majority first second htriple bound) := by
  exact _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialLength.exists_longRadialSectorWitness_at_five
      web.annular web.boundary_wellFormed web.connected
      coloring web.tait web.totallyClosed web.goodWord
      bound hlarge

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
