import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebAtGoodWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebChordRotationNoncrossing

/-!
# Source-facing L8-to-L6 length/depth handoff

Addendum XXVII starts L6 from the two radial paths supplied by L8.  The
quantitative L8 witness proves that at least one of those paths is long, but
the rotation-sector L6 theorem is stated on the first path of a chosen pair.
This module performs that case split explicitly: if the second path is the
long one, it applies the same theorem to `swapRadialPathPair`.

The result is deliberately parameterized by actual contaminated-position
sets and proofs of their cardinality bounds.  It does not restore the
manuscript's false claim that an ambient minimal counterexample has exactly
twelve pentagons.  Constructing those position sets from nonhexagonal faces,
and discharging the high negative-curvature branch, remain the numerical
content needed for a uniform `V₀`.

This is the source-facing L6 handoff, not a conditional replacement for the
missing curvature argument.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebSourceLengthDepth

open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebChordRotationNoncrossing
open GoertzelV24ClosedWebChordRotationSector
open GoertzelV24ClosedWebLaminarDepth
open GoertzelV24ClosedWebLengthDepthDichotomy
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialLength
open GoertzelV24ClosedWebRadialPathChordDiagram
open GoertzelV24ClosedWebRadialPathSectorAnchors
open GoertzelV24ClosedWebSectorAlternation
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- The complete L6 alternative on one actual radial path: either a declared
clean shallow block exists, or one rotation sector contains more than the
requested number of pairwise-laminar spanning chords. -/
def RadialLengthDepthOutcome
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (htriple : IsTaitColorTriple majority first second)
    (badPositions : Finset (Fin pair.firstPath.path.length))
    (defectBudget depthBound blockLength : Nat) : Prop :=
  HasShallowRadialCorridor C majority first second pair.firstPath
      badPositions defectBudget (2 * depthBound) blockLength ∨
    ∃ (cut : Fin pair.firstPath.path.length) (side : Bool),
      depthBound <
        (sectorSpanningChords C majority first second pair.firstPath
          (positionRotationSector embedded hdata pair.firstPath htriple)
          side cut).card ∧
      PairwiseLaminar
        (sectorSpanningChords C majority first second pair.firstPath
          (positionRotationSector embedded hdata pair.firstPath htriple)
          side cut)

/-- The proved rotation-sector theorem supplies the complete one-path L6
outcome once the finite contamination and length premises are available. -/
theorem radialLengthDepthOutcome_of_prefix
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (htriple : IsTaitColorTriple majority first second)
    (badPositions : Finset (Fin pair.firstPath.path.length))
    (defectBudget depthBound blockLength : Nat)
    (hblockLength : 0 < blockLength)
    (hbad : badPositions.card ≤ defectBudget)
    (hprefix :
      (defectBudget + 1) * blockLength ≤ pair.firstPath.path.length) :
    RadialLengthDepthOutcome embedded hdata pair htriple badPositions
      defectBudget depthBound blockLength := by
  exact hasShallowRadialCorridor_or_exists_large_laminar_rotationSector
    embedded hdata pair htriple badPositions defectBudget depthBound
      blockLength hblockLength hbad hprefix

/-- **L6.** The quantitative L8 witness feeds L6 on whichever of its two
radial paths is long.  No choice of the long path and no sector datum is left
to the caller.

The two contamination sets remain explicit because their geometric
construction, rather than the already-proved length/sector case split, is the
live weighted-curvature obligation. -/
theorem LongRadialSectorWitness.lengthDepthOutcome
    {data : AnnularBoundaryData G 5}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color)
    (majority first second : Color)
    (htriple : IsTaitColorTriple majority first second)
    (bound : Nat)
    (witness : LongRadialSectorWitness
      embedded hdata C majority first second htriple bound)
    (badFirst : Finset (Fin witness.pair.firstPath.path.length))
    (badSecond : Finset
      (Fin (swapRadialPathPair witness.pair).firstPath.path.length))
    (defectBudget depthBound blockLength : Nat)
    (hblockLength : 0 < blockLength)
    (hbound : (defectBudget + 1) * blockLength ≤ bound + 1)
    (hbadFirst : badFirst.card ≤ defectBudget)
    (hbadSecond : badSecond.card ≤ defectBudget) :
    RadialLengthDepthOutcome embedded hdata witness.pair htriple badFirst
        defectBudget depthBound blockLength ∨
      RadialLengthDepthOutcome embedded hdata
        (swapRadialPathPair witness.pair) htriple badSecond
          defectBudget depthBound blockLength := by
  rcases witness.one_path_long with hfirst | hsecond
  · left
    apply radialLengthDepthOutcome_of_prefix
      embedded hdata witness.pair htriple badFirst defectBudget depthBound
        blockLength hblockLength hbadFirst
    omega
  · right
    apply radialLengthDepthOutcome_of_prefix
      embedded hdata (swapRadialPathPair witness.pair) htriple badSecond
        defectBudget depthBound blockLength hblockLength hbadSecond
    change (defectBudget + 1) * blockLength ≤
      witness.pair.secondPath.path.length
    omega

/-- **L6/L8 source assembly.** A sufficiently large closed web at a good word
constructs the two radial paths and packages the L6 length/depth conclusion
for every pair of genuinely bounded contamination sets.

This theorem is quantitative but not a uniform `V₀`: the caller must still
construct the two source contamination sets and prove their common bound. -/
theorem Instance.exists_radialWitness_with_lengthDepthOutcome
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    (bound defectBudget depthBound blockLength : Nat)
    (hblockLength : 0 < blockLength)
    (hbound : (defectBudget + 1) * blockLength ≤ bound + 1)
    (hlarge : 2 * (bound + 1) < data.interiorVertices.card) :
    ∃ majority first second : Color,
      ∃ htriple : IsTaitColorTriple majority first second,
        ∃ witness : LongRadialSectorWitness web.annular
            web.boundary_wellFormed coloring majority first second htriple
            bound,
          ∀ (badFirst : Finset (Fin witness.pair.firstPath.path.length))
            (badSecond : Finset
              (Fin (swapRadialPathPair witness.pair).firstPath.path.length)),
            badFirst.card ≤ defectBudget →
            badSecond.card ≤ defectBudget →
              RadialLengthDepthOutcome web.annular web.boundary_wellFormed
                    witness.pair htriple badFirst defectBudget depthBound
                    blockLength ∨
                RadialLengthDepthOutcome web.annular
                  web.boundary_wellFormed
                  (swapRadialPathPair witness.pair) htriple badSecond
                    defectBudget depthBound blockLength := by
  obtain ⟨majority, first, second, htriple, ⟨witness⟩⟩ :=
    web.exists_longRadialSectorWitness bound hlarge
  refine ⟨majority, first, second, htriple, witness, ?_⟩
  intro badFirst badSecond hbadFirst hbadSecond
  exact LongRadialSectorWitness.lengthDepthOutcome
    web.annular web.boundary_wellFormed coloring majority first second
      htriple bound witness badFirst badSecond defectBudget depthBound
      blockLength hblockLength hbound hbadFirst hbadSecond

end

end GoertzelV24ClosedWebSourceLengthDepth

end Mettapedia.GraphTheory.FourColor
