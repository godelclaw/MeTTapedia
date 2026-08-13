import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebChordCycleFaceSideTransport

/-!
# Parity guard for chord walls used as primal cuts

A same-path chord and its radial subarc form a useful facial wall, but that
wall is not automatically a primal transversal.  An exact vertex-side cut
alternates its side at every wall edge, hence its closed wall walk must have
even length.  The source's profile construction therefore keeps a genuine
transversal/layer boundary separate from the chord that indexes it.

This file packages that elementary obstruction at the exact
`CyclicEdgeCutRealization` interface.  It does not assert that a chord wall
is a cut; it records the necessary parity condition whenever one is supplied.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebChordCutParity

open SimpleGraph
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebChordCycleFaceSideTransport

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- An exact primal cut supported by a closed walk forces the walk to have
even length.  The proof uses the side assignment already carried by the cut
realization; no planarity assumption is hidden here. -/
theorem cyclicEdgeCutRealization_walk_length_even
    {start : V} {cycle : G.Walk start start}
    (realization : CyclicEdgeCutRealization G (walkEdgeFinset cycle)) :
    Even cycle.length :=
  CycleSideCertificate.length_even
    (CycleSideCertificate.ofCyclicEdgeCutRealization realization)

/-- Specialization to a same-path chord wall.  It is a necessary condition,
not a construction: the separate transversal in the source route is still
responsible for supplying a cut when this parity condition holds. -/
theorem chord_cycle_length_even_of_cyclicEdgeCutRealization
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (realization : CyclicEdgeCutRealization G (chord.boundary htriple).wall) :
    Even chord.cycleWalk.length := by
  have hwall : (chord.boundary htriple).wall =
      walkEdgeFinset chord.cycleWalk := by
    ext edge
    exact (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple edge).trans
      (mem_walkEdgeFinset_iff chord.cycleWalk edge).symm
  rw [hwall] at realization
  exact cyclicEdgeCutRealization_walk_length_even realization

/-- An odd chord cycle cannot itself be the support of an exact primal cut.
This is the kernel-checked rejection of the tempting identification of the
facial chord wall with the source's separate transversal. -/
theorem not_nonempty_chord_cyclicEdgeCutRealization_of_odd_length
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (hodd : Odd chord.cycleWalk.length) :
    ¬ Nonempty (CyclicEdgeCutRealization G (chord.boundary htriple).wall) := by
  rintro ⟨realization⟩
  exact (Nat.not_odd_iff_even.mpr
    (chord_cycle_length_even_of_cyclicEdgeCutRealization
      chord htriple realization)) hodd

end

end GoertzelV24ClosedWebChordCutParity

end Mettapedia.GraphTheory.FourColor
