import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierWeightedCorridor
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialLength
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebComputedDepthProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24SpliceUnification

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
open GoertzelV24ClosedWebComputedDepthProfile
open GoertzelV24ClosedWebRadialLength
open GoertzelV24ClosedWebTotalClosure
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SpliceUnification
open GoertzelV24SpliceUnification.OrderedCutSpliceData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq
attribute [-instance] GoertzelV24SeamFaceArcPartition.hitPointFintype

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

/-- The source's good word is protected by a splice precisely when each of
its five named interface edges is represented by an old internal dart on the
retained side.  This is a geometric certificate to be constructed from the
chosen pumped region, not an assumption that follows from profile equality. -/
structure ProtectedInnerInterface
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring)
    {n terminalCount faceFragmentCount : Nat}
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount) where
  dart : Fin 5 → InternalDart web.annular.RS splice.keep
  edge_eq : ∀ port,
    web.annular.RS.edgeOf (dart port).1.1 = data.innerBoundaryEdge port

namespace ProtectedInnerInterface

/-- The concrete form of the source statement that the inner hole is outside
the pumped region: both endpoints of every one of its five boundary edges
remain on the retained side. -/
def InnerBoundaryKept
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {n terminalCount faceFragmentCount : Nat}
    {web : Instance data coloring}
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount) : Prop :=
  ∀ port dart,
    dart ∈ web.annular.RS.dartsOn (data.innerBoundaryEdge port) →
      splice.keep (web.annular.RS.vertOf dart)

/-- The analogous geometric condition for the outer container.  The source
splice checklist keeps both named holes and all their feet outside the pumped
region; this condition records the outer half separately from the inner-word
condition. -/
def OuterBoundaryKept
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {n terminalCount faceFragmentCount : Nat}
    {web : Instance data coloring}
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount) : Prop :=
  ∀ port dart,
    dart ∈ web.annular.RS.dartsOn (data.outerBoundaryEdge port) →
      splice.keep (web.annular.RS.vertOf dart)

/-- A retained inner boundary constructs the protected interface certificate
used by the good-word transport.  This selects a real dart on each named
source edge and proves that its opposite is retained too; no arbitrary
boundary enumeration is introduced. -/
noncomputable def of_innerBoundaryKept
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {n terminalCount faceFragmentCount : Nat}
    {web : Instance data coloring}
    {splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount}
    (hkept : InnerBoundaryKept splice) :
    ProtectedInnerInterface web splice := by
  have hexists : ∀ port : Fin 5, ∃ dart : web.annular.RS.D,
      dart ∈ web.annular.RS.dartsOn (data.innerBoundaryEdge port) := by
    intro port
    have hcard := web.annular.RS.dartsOn_card_two (data.innerBoundaryEdge port)
    have hpositive : 0 < (web.annular.RS.dartsOn
        (data.innerBoundaryEdge port)).card := by
      omega
    rcases Finset.card_pos.mp hpositive with ⟨dart, hdart⟩
    exact ⟨dart, hdart⟩
  let selected : Fin 5 → web.annular.RS.D :=
    fun port => Classical.choose (hexists port)
  have hselected : ∀ port,
      selected port ∈ web.annular.RS.dartsOn (data.innerBoundaryEdge port) :=
    fun port => Classical.choose_spec (hexists port)
  have hselectedEdge : ∀ port,
      web.annular.RS.edgeOf (selected port) = data.innerBoundaryEdge port :=
    fun port => (web.annular.RS.mem_dartsOn).1 (hselected port)
  have halphaSelected : ∀ port,
      web.annular.RS.alpha (selected port) ∈
        web.annular.RS.dartsOn (data.innerBoundaryEdge port) := by
    intro port
    apply (web.annular.RS.mem_dartsOn).2
    rw [web.annular.RS.edge_alpha]
    exact hselectedEdge port
  refine {
    dart := fun port =>
      ⟨⟨selected port, hkept port (selected port) (hselected port)⟩,
        hkept port (web.annular.RS.alpha (selected port))
          (halphaSelected port)⟩
    edge_eq := fun port => hselectedEdge port }

/-- Read the five protected source-interface colors from the canonical
forward splice coloring.  The output need not yet be packaged as an annular
tangle for this word-level preservation theorem to be meaningful. -/
def splicedInnerWord
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {n terminalCount faceFragmentCount : Nat}
    {web : Instance data coloring}
    {splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount}
    (interface : ProtectedInnerInterface web splice)
    (profile : splice.EqualProfile) : CAP5BoundaryWord :=
  fun port => splice.splicedColoring profile
    (splice.output.edgeOf (Sum.inl (interface.dart port)))

/-- The protected five-edge word is unchanged by the canonical forward
splice.  Thus the `(3,1,1)` good-word predicate survives once the concrete
layer construction certifies that the inner interface is outside the pumped
region. -/
theorem splicedInnerWord_eq_source
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {n terminalCount faceFragmentCount : Nat}
    {web : Instance data coloring}
    {splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount}
    (interface : ProtectedInnerInterface web splice)
    (profile : splice.EqualProfile)
    (hcoloring : profile.coloring =
      rotationColoringOfGraph web.annular coloring) :
    interface.splicedInnerWord profile = data.innerBoundaryWord coloring := by
  funext port
  change splice.splicedColoring profile
      (splice.output.edgeOf (Sum.inl (interface.dart port))) =
    coloring (data.innerBoundaryEdge port)
  calc
    splice.splicedColoring profile
        (splice.output.edgeOf (Sum.inl (interface.dart port))) =
      profile.coloring (web.annular.RS.edgeOf (interface.dart port).1.1) :=
        splice.splicedColoring_internal_edgeOf profile (interface.dart port)
    _ = (rotationColoringOfGraph web.annular coloring)
        (web.annular.RS.edgeOf (interface.dart port).1.1) := by
      rw [hcoloring]
    _ = coloring (data.innerBoundaryEdge port) := by
      change coloring (web.annular.RS.edgeOf (interface.dart port).1.1) =
        coloring (data.innerBoundaryEdge port)
      rw [interface.edge_eq]

/-- A source good word remains good in the protected output word.  This
closes the good-word part of Addendum XXVII's splice checklist at the exact
point where its geometric ``outside the pumped region'' premise is supplied. -/
theorem splicedInnerWord_good
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {n terminalCount faceFragmentCount : Nat}
    {web : Instance data coloring}
    {splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount}
    (interface : ProtectedInnerInterface web splice)
    (profile : splice.EqualProfile)
    (hcoloring : profile.coloring =
      rotationColoringOfGraph web.annular coloring) :
    CAP5BoundaryWordHasColoredBlock311 (interface.splicedInnerWord profile) := by
  rw [interface.splicedInnerWord_eq_source profile hcoloring]
  exact web.goodWord

end ProtectedInnerInterface

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
