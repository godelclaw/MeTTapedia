import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceSeamArcAmbientSimplicity

/-!
# Closed-web seam-arc closure criterion

For the actual closed-web annulus, preservation of the two named hole faces
already makes every canonical seam arc internally simple.  Consequently the
remaining L1 seam receipt is exactly local two-sidedness of the completed
seam faces: distinct canonical arcs on one output face must not traverse the
two opposite darts of one edge.

This is an exact criterion, not a construction of the remaining topological
fact.  In particular, spherical Euler data for the splice output does not by
itself supply local two-sidedness.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebSpliceSeamArcAmbientSimplicity
open GoertzelV24FramedAnnularExcess
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24SpliceUnification.OrderedCutSpliceData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
  {n terminalCount faceFragmentCount : Nat}
  {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}

noncomputable section


attribute [local instance]
  retainedVertexFintype retainedVertexDecidableEq

local instance sourceEdgeSetDecidableEqSeamArcClosureCriterion : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace GoertzelV24ClosedWebSpliceSeamArcClosureCriterion

/-- **L1.** Once the two protected hole faces survive the literal splice,
pairwise edge-disjointness of distinct canonical seam arcs is equivalent to
the source-topological statement that every seam-root output face is locally
two-sided.  Internal arc simplicity contributes no further premise here: it
is already derived from the closed-web annular geometry. -/
theorem seamArcsPairwiseEdgeDisjoint_iff_seamFacesTwoSided
    (splice : GoertzelV24SpliceUnification.OrderedCutSpliceData
      web.annular.RS n terminalCount faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole) :
    splice.SeamArcsPairwiseEdgeDisjoint ↔ splice.SeamFacesTwoSided := by
  have hinternal : splice.SeamArcsInternallySimple :=
    seamArcsInternallySimple splice hinner houter
  constructor
  · intro hpairwise
    exact (splice.seamArcNoncollision_iff_twoSided).1
      ⟨hinternal, hpairwise⟩
  · intro htwoSided
    exact ((splice.seamArcNoncollision_iff_twoSided).2 htwoSided).2

end GoertzelV24ClosedWebSpliceSeamArcClosureCriterion

end

end Mettapedia.GraphTheory.FourColor
