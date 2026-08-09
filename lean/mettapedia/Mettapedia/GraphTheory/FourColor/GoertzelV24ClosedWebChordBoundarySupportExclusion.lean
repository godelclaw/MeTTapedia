import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebTrimmedRadialPath

/-!
# Boundary stubs are outside a same-path chord cycle

The chord interval lies strictly inside its carrier radial path.  A boundary
stub is the first (or last) path vertex, so path injectivity rules out its
occurrence in the chord cycle.  This is a small but useful Jordan-side input:
the hole-boundary darts are genuinely wall-free at their primal vertices.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebChordBoundarySupportExclusion

open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebTrimmedRadialPath
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

local instance chordBoundarySupportExclusionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

theorem innerStub_not_mem_cycleWalk_support
    {data : AnnularBoundaryData G outerCount}
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second) :
    data.innerStub radial.inner ∉ chord.cycleWalk.support := by
  intro hsupport
  have hcycle : chord.cycleWalk.IsCycle :=
    chord.cycleWalk_isCycle htriple
  rcases (chord.cycleWalk.mem_support_iff_exists_mem_edges_of_not_nil
      hcycle.not_nil).1 hsupport with ⟨edge, hedge, hvertex⟩
  let edge' : G.edgeSet :=
    ⟨edge, chord.cycleWalk.edges_subset_edgeSet hedge⟩
  have hvertex' : data.innerStub radial.inner ∈
      (edge'.1 : Sym2 V) := by
    simpa [edge'] using hvertex
  rcases chord.exists_position_between_of_mem_cycleWalk_edges
      htriple edge' (by simpa [edge'] using hedge) hvertex' with
    ⟨position, hleft, hright, hposition⟩
  have hpathBound : position ≤ (ambientRadialPath radial).length := by
    have hrightLength : chord.right.val <
        (ambientRadialPath radial).length := by
      simpa [ambientRadialPath_length] using
        chord.right_lt_length hdata htriple
    omega
  have hzero : (ambientRadialPath radial).getVert 0 =
      data.innerStub radial.inner := by
    rw [SimpleGraph.Walk.getVert_zero]
    exact radial.start_eq_innerStub
  have hpositionZero : position = 0 := by
    apply (ambientRadialPath_isPath radial).getVert_injOn
      hpathBound (by simp)
    exact hposition.trans hzero.symm
  have hleftPositive := chord.left_pos hdata htriple
  omega

theorem outerStub_not_mem_cycleWalk_support
    {data : AnnularBoundaryData G outerCount}
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second) :
    data.outerStub radial.outer ∉ chord.cycleWalk.support := by
  intro hsupport
  have hcycle : chord.cycleWalk.IsCycle :=
    chord.cycleWalk_isCycle htriple
  rcases (chord.cycleWalk.mem_support_iff_exists_mem_edges_of_not_nil
      hcycle.not_nil).1 hsupport with ⟨edge, hedge, hvertex⟩
  let edge' : G.edgeSet :=
    ⟨edge, chord.cycleWalk.edges_subset_edgeSet hedge⟩
  have hvertex' : data.outerStub radial.outer ∈
      (edge'.1 : Sym2 V) := by
    simpa [edge'] using hvertex
  rcases chord.exists_position_between_of_mem_cycleWalk_edges
      htriple edge' (by simpa [edge'] using hedge) hvertex' with
    ⟨position, hleft, hright, hposition⟩
  have hpathBound : position ≤ (ambientRadialPath radial).length := by
    exact le_trans hright (Nat.le_of_lt (by
      simpa [ambientRadialPath_length] using
        chord.right_lt_length hdata htriple))
  have hfinish : (ambientRadialPath radial).getVert
      (ambientRadialPath radial).length =
      data.outerStub radial.outer := by
    rw [SimpleGraph.Walk.getVert_length]
    exact radial.finish_eq_outerStub
  have hpositionFinish : position = (ambientRadialPath radial).length := by
    apply (ambientRadialPath_isPath radial).getVert_injOn
      hpathBound (by simp)
    exact hposition.trans hfinish.symm
  have hrightLength : chord.right.val <
      (ambientRadialPath radial).length := by
    simpa [ambientRadialPath_length] using
      chord.right_lt_length hdata htriple
  omega

end

end GoertzelV24ClosedWebChordBoundarySupportExclusion

end Mettapedia.GraphTheory.FourColor
