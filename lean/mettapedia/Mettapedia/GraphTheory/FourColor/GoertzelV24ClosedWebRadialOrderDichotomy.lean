import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSourceLengthDepth

/-!
# Curvature-free radial-order entrance to L6

Addendum XXVII needs a large closed web to be large in one of two
coordinates: consecutive radial length or laminar chord depth.  The
manuscript derives that alternative using a fixed nonhexagonal-defect budget.
That premise is not available when faces longer than six occur: weighted
curvature gives `pentagons = fixed boundary credit + negative weight`, so the
negative weight is not uniformly bounded.

This file removes that premise from the numerical L6 entrance.  Total closure
already places every interior vertex on one of two radial paths.  On a long
path, apply the proved cut-load dichotomy with the empty marked set.  The
result is unconditional in the curvature weight:

* a consecutive block whose actual chord load is bounded at every cut; or
* a rotation sector containing a large pairwise-laminar chord family.

This is **L6**, not the completed shrinking lemma.  The length branch still
has to be realized by source-local simple layer boundaries, and the depth
branch still has to be realized by deletion transversals before either equal
profile can feed the splice.  No hexagonal corridor, fixed defect budget, or
conditional reduction supplier is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebRadialOrderDichotomy

open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebChordRotationNoncrossing
open GoertzelV24ClosedWebChordRotationSector
open GoertzelV24ClosedWebLaminarDepth
open GoertzelV24ClosedWebLengthDepthDichotomy
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialLength
open GoertzelV24ClosedWebRadialPathSectorAnchors
open GoertzelV24ClosedWebSectorAlternation
open GoertzelV24ClosedWebSourceLengthDepth
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- Uniform vertex threshold for obtaining `blockLength` cuts on one of the
two source radial paths.  Unlike the earlier clean-hex threshold, this number
does not mention face curvature. -/
def radialOrderLengthDepthVertexThreshold (blockLength : Nat) : Nat :=
  2 * blockLength

/-- The two source coordinates with no curvature-dependent contamination
parameter.  The first branch is literal radial length with bounded actual
chord load; the second is literal laminar depth in one rotation sector. -/
def RadialOrderLengthDepthOutcome
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (htriple : IsTaitColorTriple majority first second)
    (depthBound blockLength : Nat) : Prop :=
  RadialLengthDepthOutcome embedded hdata pair htriple ∅ 0
    depthBound blockLength

/-- A radial path of at least `blockLength` cuts has the curvature-free L6
length/depth outcome.  The proof is the existing rotation-sector theorem
specialized to the empty marked set and zero defect budget. -/
theorem radialOrderLengthDepthOutcome_of_length
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (htriple : IsTaitColorTriple majority first second)
    (depthBound blockLength : Nat)
    (hblockLength : 0 < blockLength)
    (hlength : blockLength ≤ pair.firstPath.path.length) :
    RadialOrderLengthDepthOutcome embedded hdata pair htriple
      depthBound blockLength := by
  apply radialLengthDepthOutcome_of_prefix embedded hdata pair htriple
    ∅ 0 depthBound blockLength hblockLength
  · simp
  · simpa using hlength

/-- **L6 curvature repair.** Every sufficiently large source closed web at a
good word constructs a long radial witness and, on whichever of its two paths
is long, the curvature-free length/depth outcome.

The size premise is now the uniform arithmetic condition
`2 * blockLength < interiorVertices.card`; it contains no negative-curvature
weight. -/
theorem Instance.exists_radialWitness_with_orderLengthDepthOutcome
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    (depthBound blockLength : Nat)
    (hblockLength : 0 < blockLength)
    (hlarge : 2 * blockLength < data.interiorVertices.card) :
    ∃ majority first second : Color,
      ∃ htriple : IsTaitColorTriple majority first second,
        ∃ witness : LongRadialSectorWitness web.annular
            web.boundary_wellFormed coloring majority first second htriple
            (blockLength - 1),
          RadialOrderLengthDepthOutcome web.annular
                web.boundary_wellFormed witness.pair htriple
                depthBound blockLength ∨
            RadialOrderLengthDepthOutcome web.annular
              web.boundary_wellFormed (swapRadialPathPair witness.pair)
                htriple depthBound blockLength := by
  obtain ⟨majority, first, second, htriple, ⟨witness⟩⟩ :=
    web.exists_longRadialSectorWitness (blockLength - 1) (by omega)
  refine ⟨majority, first, second, htriple, witness, ?_⟩
  rcases witness.one_path_long with hfirst | hsecond
  · left
    apply radialOrderLengthDepthOutcome_of_length
      web.annular web.boundary_wellFormed witness.pair htriple
        depthBound blockLength hblockLength
    omega
  · right
    apply radialOrderLengthDepthOutcome_of_length
      web.annular web.boundary_wellFormed
        (swapRadialPathPair witness.pair) htriple
        depthBound blockLength hblockLength
    change blockLength ≤ witness.pair.secondPath.path.length
    omega

/-- Threshold-spelled form of the curvature-free L6 entrance, ready for a
future strict-reduction supplier to instantiate after both geometric outcome
branches have been connected to the splice. -/
theorem Instance.exists_radialWitness_with_orderLengthDepthOutcome_of_threshold
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    (depthBound blockLength : Nat)
    (hblockLength : 0 < blockLength)
    (hlarge : radialOrderLengthDepthVertexThreshold blockLength <
      data.interiorVertices.card) :
    ∃ majority first second : Color,
      ∃ htriple : IsTaitColorTriple majority first second,
        ∃ witness : LongRadialSectorWitness web.annular
            web.boundary_wellFormed coloring majority first second htriple
            (blockLength - 1),
          RadialOrderLengthDepthOutcome web.annular
                web.boundary_wellFormed witness.pair htriple
                depthBound blockLength ∨
            RadialOrderLengthDepthOutcome web.annular
              web.boundary_wellFormed (swapRadialPathPair witness.pair)
                htriple depthBound blockLength := by
  apply Instance.exists_radialWitness_with_orderLengthDepthOutcome
    web depthBound blockLength hblockLength
  simpa [radialOrderLengthDepthVertexThreshold] using hlarge

end

end GoertzelV24ClosedWebRadialOrderDichotomy

end Mettapedia.GraphTheory.FourColor
