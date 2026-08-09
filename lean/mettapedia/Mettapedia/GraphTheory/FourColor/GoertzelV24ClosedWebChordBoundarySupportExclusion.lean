import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebTrimmedRadialPath
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebInnerTouching

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

/-! The radial component has exactly the named inner and outer boundary
stubs.  The two endpoint lemmas above are enough for the selected endpoints;
the next lemma records the stronger fact needed when a complementary side is
forced to carry the whole annular interface. -/

theorem any_innerStub_not_mem_cycleWalk_support
    {data : AnnularBoundaryData G outerCount}
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (hpair : ValidColorPair first second)
    (inner : Fin 5) :
    data.innerStub inner ∉ chord.cycleWalk.support := by
  intro hsupport
  have hcycle : chord.cycleWalk.IsCycle :=
    chord.cycleWalk_isCycle htriple
  rcases (chord.cycleWalk.mem_support_iff_exists_mem_edges_of_not_nil
      hcycle.not_nil).1 hsupport with ⟨edge, hedge, hvertex⟩
  let edge' : G.edgeSet :=
    ⟨edge, chord.cycleWalk.edges_subset_edgeSet hedge⟩
  have hvertex' : data.innerStub inner ∈ (edge'.1 : Sym2 V) := by
    simpa [edge'] using hvertex
  have hradialSupport :
      data.innerStub inner ∈ (ambientRadialPath radial).support :=
    chord.mem_ambientRadialPath_support_of_mem_cycleWalk_edges
      htriple edge' (by simpa [edge'] using hedge) hvertex'
  have hmapSupport :
      (ambientRadialPath radial).support =
        radial.path.support.map
          (colorPairSupportToAmbientHom C first second) := by
    change (radial.path.map
        (colorPairSupportToAmbientHom C first second)).support = _
    rw [SimpleGraph.Walk.support_map]
  have hmapped :
      data.innerStub inner ∈
        radial.path.support.map
          (colorPairSupportToAmbientHom C first second) := by
    rw [← hmapSupport]
    exact hradialSupport
  rcases List.mem_map.mp hmapped with ⟨candidate, hcandidate, hcandidateVal⟩
  have hcandidateComponent : candidate ∈ component.supp := by
    rw [← radial.path_vertices]
    exact radial.path.mem_verts_toSubgraph.mpr hcandidate
  have hcandidateBoundary :
      GoertzelV24ClosedWebInnerTouching.IsBoundaryStub data candidate := by
    left
    exact ⟨inner, by simpa [colorPairSupportToAmbientHom] using hcandidateVal⟩
  have hstartBoundary :
      GoertzelV24ClosedWebInnerTouching.IsBoundaryStub data radial.start := by
    left
    exact ⟨radial.inner, radial.start_eq_innerStub⟩
  have hfinishBoundary :
      GoertzelV24ClosedWebInnerTouching.IsBoundaryStub data radial.finish := by
    right
    exact ⟨radial.outer, radial.finish_eq_outerStub⟩
  have hstartFinish : radial.start ≠ radial.finish := by
    intro heq
    apply hdata.inner_outer_stub_disjoint radial.inner radial.outer
    calc
      data.innerStub radial.inner = radial.start.1 :=
        radial.start_eq_innerStub.symm
      _ = radial.finish.1 := congrArg Subtype.val heq
      _ = data.outerStub radial.outer := radial.finish_eq_outerStub
  have hendpoints :=
    GoertzelV24ClosedWebInnerTouching.boundaryStub_eq_start_or_finish_of_mem_component
      data hdata C hC hpair component radial.start radial.finish candidate
      radial.start_mem radial.finish_mem hcandidateComponent hstartFinish
      hstartBoundary hfinishBoundary hcandidateBoundary
  rcases hendpoints with hstart | hfinish
  · have hinnerEq : inner = radial.inner := by
      apply data.innerStub.injective
      calc
        data.innerStub inner = candidate.1 := by
          simpa [colorPairSupportToAmbientHom] using hcandidateVal.symm
        _ = radial.start.1 := congrArg Subtype.val hstart
        _ = data.innerStub radial.inner := radial.start_eq_innerStub
    exact innerStub_not_mem_cycleWalk_support hdata chord htriple
      (hinnerEq ▸ hsupport)
  · apply hdata.inner_outer_stub_disjoint inner radial.outer
    calc
      data.innerStub inner = candidate.1 := by
        simpa [colorPairSupportToAmbientHom] using hcandidateVal.symm
      _ = radial.finish.1 := congrArg Subtype.val hfinish
      _ = data.outerStub radial.outer := radial.finish_eq_outerStub

theorem any_outerStub_not_mem_cycleWalk_support
    {data : AnnularBoundaryData G outerCount}
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (hpair : ValidColorPair first second)
    (outer : Fin outerCount) :
    data.outerStub outer ∉ chord.cycleWalk.support := by
  intro hsupport
  have hcycle : chord.cycleWalk.IsCycle :=
    chord.cycleWalk_isCycle htriple
  rcases (chord.cycleWalk.mem_support_iff_exists_mem_edges_of_not_nil
      hcycle.not_nil).1 hsupport with ⟨edge, hedge, hvertex⟩
  let edge' : G.edgeSet :=
    ⟨edge, chord.cycleWalk.edges_subset_edgeSet hedge⟩
  have hvertex' : data.outerStub outer ∈ (edge'.1 : Sym2 V) := by
    simpa [edge'] using hvertex
  have hradialSupport :
      data.outerStub outer ∈ (ambientRadialPath radial).support :=
    chord.mem_ambientRadialPath_support_of_mem_cycleWalk_edges
      htriple edge' (by simpa [edge'] using hedge) hvertex'
  have hmapSupport :
      (ambientRadialPath radial).support =
        radial.path.support.map
          (colorPairSupportToAmbientHom C first second) := by
    change (radial.path.map
        (colorPairSupportToAmbientHom C first second)).support = _
    rw [SimpleGraph.Walk.support_map]
  have hmapped :
      data.outerStub outer ∈
        radial.path.support.map
          (colorPairSupportToAmbientHom C first second) := by
    rw [← hmapSupport]
    exact hradialSupport
  rcases List.mem_map.mp hmapped with ⟨candidate, hcandidate, hcandidateVal⟩
  have hcandidateComponent : candidate ∈ component.supp := by
    rw [← radial.path_vertices]
    exact radial.path.mem_verts_toSubgraph.mpr hcandidate
  have hcandidateBoundary :
      GoertzelV24ClosedWebInnerTouching.IsBoundaryStub data candidate := by
    right
    exact ⟨outer, by simpa [colorPairSupportToAmbientHom] using hcandidateVal⟩
  have hstartBoundary :
      GoertzelV24ClosedWebInnerTouching.IsBoundaryStub data radial.start := by
    left
    exact ⟨radial.inner, radial.start_eq_innerStub⟩
  have hfinishBoundary :
      GoertzelV24ClosedWebInnerTouching.IsBoundaryStub data radial.finish := by
    right
    exact ⟨radial.outer, radial.finish_eq_outerStub⟩
  have hstartFinish : radial.start ≠ radial.finish := by
    intro heq
    apply hdata.inner_outer_stub_disjoint radial.inner radial.outer
    calc
      data.innerStub radial.inner = radial.start.1 :=
        radial.start_eq_innerStub.symm
      _ = radial.finish.1 := congrArg Subtype.val heq
      _ = data.outerStub radial.outer := radial.finish_eq_outerStub
  have hendpoints :=
    GoertzelV24ClosedWebInnerTouching.boundaryStub_eq_start_or_finish_of_mem_component
      data hdata C hC hpair component radial.start radial.finish candidate
      radial.start_mem radial.finish_mem hcandidateComponent hstartFinish
      hstartBoundary hfinishBoundary hcandidateBoundary
  rcases hendpoints with hstart | hfinish
  · apply hdata.inner_outer_stub_disjoint radial.inner outer
    calc
      data.innerStub radial.inner = radial.start.1 :=
        radial.start_eq_innerStub.symm
      _ = candidate.1 := congrArg Subtype.val hstart.symm
      _ = data.outerStub outer := by
        simpa [colorPairSupportToAmbientHom] using hcandidateVal
  · have houterEq : outer = radial.outer := by
      apply data.outerStub.injective
      calc
        data.outerStub outer = candidate.1 := by
          simpa [colorPairSupportToAmbientHom] using hcandidateVal.symm
        _ = radial.finish.1 := congrArg Subtype.val hfinish
        _ = data.outerStub radial.outer := radial.finish_eq_outerStub
    exact outerStub_not_mem_cycleWalk_support hdata chord htriple
      (houterEq ▸ hsupport)

end

end GoertzelV24ClosedWebChordBoundarySupportExclusion

end Mettapedia.GraphTheory.FourColor
