import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebFragmentReindexRadialThreshold
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebReductiveAssembly
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceOutputInstance

/-!
# From the calibrated radial alternative to the reductive supplier

The fragment-reindexed L6/L7 arithmetic gives every sufficiently large
closed web one of two concrete geometric outcomes: a shallow radial block or
a deep laminar sector, on one of the two ordered radial paths.  The public
reductive system consumes a complete carrier-changing strict-reduction
certificate.

This module records the exact joint between those layers.  An adapter has one
field for each geometric branch of the proved alternative: shallow serial
cuts and deep laminar cuts.  Either field must return the already-defined
strict-reduction certificate, including the complete reconstructed output
web.  Once both fields are supplied, the
checked threshold `845970` becomes a genuine `StrictReductionSupplier`.

No geometric adapter is constructed here.  In particular, this file does not
turn shallow cuts into literal serial boundaries, turn laminar chords into
deletion transversals, or verify the finite base.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebFragmentReindexReductionSupplier

open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebChordRotationSector
open GoertzelV24ClosedWebFragmentReindexRadialThreshold
open GoertzelV24ClosedWebLaminarDepth
open GoertzelV24ClosedWebLengthDepthDichotomy
open GoertzelV24ClosedWebProfileFiniteness
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialLength
open GoertzelV24ClosedWebRadialOrderDichotomy
open GoertzelV24ClosedWebRadialPathSectorAnchors
open GoertzelV24ClosedWebReductiveAssembly
open GoertzelV24ClosedWebSectorAlternation

universe u

noncomputable section

/-- The two source-geometric adapters still required after the uniform
radial-order theorem.  They are separated by the actual mathematical branch,
not by the bookkeeping choice of the first or swapped radial path. -/
structure FragmentReindexRadialReductionAdapters (widthBound : Nat) where
  shallow :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj]
      {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
      (web : Instance data coloring)
      (majority first second : Color)
      (_htriple : IsTaitColorTriple majority first second)
      (pair : RadialPathPair data coloring first second),
      HasShallowRadialCorridor coloring majority first second pair.firstPath
          ∅ 0 (2 * closedWebCutProfileCount widthBound)
          fragmentReindexRadialBlockLength →
        Nonempty (PackedInstance.StrictReductionCertificate
          (Instance.toPackedInstance (web := web)))
  deep :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj]
      {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
      (web : Instance data coloring)
      (majority first second : Color)
      (htriple : IsTaitColorTriple majority first second)
      (pair : RadialPathPair data coloring first second)
      (cut : Fin pair.firstPath.path.length) (side : Bool),
      closedWebCutProfileCount widthBound <
          (sectorSpanningChords coloring majority first second pair.firstPath
            (positionRotationSector web.annular web.boundary_wellFormed
              pair.firstPath htriple) side cut).card →
      PairwiseLaminar
          (sectorSpanningChords coloring majority first second pair.firstPath
            (positionRotationSector web.annular web.boundary_wellFormed
              pair.firstPath htriple) side cut) →
        Nonempty (PackedInstance.StrictReductionCertificate
          (Instance.toPackedInstance (web := web)))

/-- **C/D/E assembly joint.**  Complete adapters for the two proved radial
branches instantiate the public carrier-changing reduction supplier at the
checked fragment-reindexed threshold.  No base claim is involved. -/
theorem strictReductionSupplier_of_fragmentReindexRadialAdapters
    (widthBound : Nat)
    (adapters : FragmentReindexRadialReductionAdapters.{u} widthBound) :
    PackedInstance.StrictReductionSupplier.{u}
      fragmentReindexClosedWebVertexThreshold := by
  intro input hlarge
  letI : Fintype input.Vertex := input.vertexFintype
  letI : DecidableEq input.Vertex := input.vertexDecidableEq
  letI : DecidableRel input.graph.Adj := input.adjDecidable
  have hlarge' : fragmentReindexClosedWebVertexThreshold <
      Fintype.card input.Vertex := by
    simpa [PackedInstance.size] using hlarge
  obtain ⟨majority, first, second, htriple, witness, houtcome⟩ :=
    Instance.exists_radialWitness_with_fragmentReindexOutcome_of_card
      input.web widthBound hlarge'
  have consume :
      ∀ (pair : RadialPathPair input.boundary input.coloring first second),
        RadialOrderLengthDepthOutcome input.web.annular
            input.web.boundary_wellFormed pair htriple
            (closedWebCutProfileCount widthBound)
            fragmentReindexRadialBlockLength →
          Nonempty (PackedInstance.StrictReductionCertificate input) := by
    intro pair hout
    rcases hout with hshallow | ⟨cut, side, hlargeChords, hlaminar⟩
    · have certificate := adapters.shallow input.web majority first second
        htriple pair hshallow
      simpa [Instance.toPackedInstance] using certificate
    · have certificate := adapters.deep input.web majority first second
        htriple pair cut side hlargeChords hlaminar
      simpa [Instance.toPackedInstance] using certificate
  rcases houtcome with hforward | hswapped
  · exact consume witness.pair hforward
  · exact consume (swapRadialPathPair witness.pair) hswapped

/-- Numeral-spelled form of the same supplier, useful at the final reductive
assembly without reopening threshold arithmetic. -/
theorem strictReductionSupplier_845970_of_fragmentReindexRadialAdapters
    (widthBound : Nat)
    (adapters : FragmentReindexRadialReductionAdapters.{u} widthBound) :
    PackedInstance.StrictReductionSupplier.{u} 845970 := by
  simpa [fragmentReindexClosedWebVertexThreshold_eq] using
    strictReductionSupplier_of_fragmentReindexRadialAdapters widthBound adapters

end

end GoertzelV24ClosedWebFragmentReindexReductionSupplier

end Mettapedia.GraphTheory.FourColor
