import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebHoleCoreArcWalk
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialPathChords

/-!
# Radial paths with their boundary spikes trimmed

The sector wall uses the internal part of each radial support path.  This
module removes its first and last boundary edges and identifies the resulting
endpoints with the neighbours of the corresponding inner and outer stubs.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebTrimmedRadialPath

open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebHoleBoundaryOrder
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChords
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem dart_eq_of_fst_eq_of_edge_eq
    (first second : G.Dart) (hfst : first.fst = second.fst)
    (hedge : first.edge = second.edge) : first = second := by
  rcases (SimpleGraph.dart_edge_eq_iff first second).1 hedge with heq | heq
  · exact heq
  · exfalso
    have hsnd := congrArg (fun dart : G.Dart => dart.fst) heq
    have : second.fst = second.snd := by
      calc
        second.fst = first.fst := hfst.symm
        _ = second.snd := by simpa using hsnd
    exact second.fst_ne_snd this

/-- A radial path cannot consist of only one boundary edge: its two named
boundary edges belong to disjoint inner and outer interfaces. -/
theorem two_le_ambientRadialPath_length
    {data : AnnularBoundaryData G outerCount} (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component) :
    2 ≤ (ambientRadialPath radial).length := by
  let path := ambientRadialPath radial
  change 2 ≤ path.length
  have hendpoints : radial.start.1 ≠ radial.finish.1 := by
    rw [radial.start_eq_innerStub, radial.finish_eq_outerStub]
    exact hdata.inner_outer_stub_disjoint radial.inner radial.outer
  have hpositive : 0 < path.length :=
    (Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hendpoints))
  by_contra hnot
  have hlength : path.length = 1 := by omega
  have hadj : G.Adj radial.start.1 radial.finish.1 :=
    Walk.adj_of_length_eq_one hlength
  let edge : G.edgeSet := ⟨s(radial.start.1, radial.finish.1), hadj⟩
  have hedgeInner : edge ∈
      incidentEdgeFinset G (data.innerStub radial.inner) := by
    simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    change data.innerStub radial.inner ∈
      s(radial.start.1, radial.finish.1)
    rw [← radial.start_eq_innerStub]
    exact Sym2.mem_iff.mpr (Or.inl rfl)
  have hedgeOuter : edge ∈
      incidentEdgeFinset G (data.outerStub radial.outer) := by
    simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    change data.outerStub radial.outer ∈
      s(radial.start.1, radial.finish.1)
    rw [← radial.finish_eq_outerStub]
    exact Sym2.mem_iff.mpr (Or.inr rfl)
  rw [data.innerStub_incidentEdgeFinset_eq_singleton hdata radial.inner] at hedgeInner
  rw [data.outerStub_incidentEdgeFinset_eq_singleton hdata radial.outer] at hedgeOuter
  have hedges : data.innerBoundaryEdge radial.inner =
      data.outerBoundaryEdge radial.outer :=
    (Finset.mem_singleton.mp hedgeInner).symm.trans
      (Finset.mem_singleton.mp hedgeOuter)
  exact hdata.inner_outer_edge_disjoint radial.inner radial.outer hedges

/-- The first radial dart is exactly the outward dart of its named inner
boundary edge. -/
theorem ambientRadialPath_firstDart_eq_innerBoundaryDart
    {data : AnnularBoundaryData G outerCount} (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component) :
    (ambientRadialPath radial).firstDart
        (by rw [Walk.not_nil_iff_lt_length];
            exact lt_of_lt_of_le (by omega)
              (two_le_ambientRadialPath_length hdata radial)) =
      innerBoundaryDart data hdata radial.inner := by
  let path := ambientRadialPath radial
  have hnil : ¬path.Nil := by
    rw [Walk.not_nil_iff_lt_length]
    exact lt_of_lt_of_le (by omega)
      (two_le_ambientRadialPath_length hdata radial)
  apply dart_eq_of_fst_eq_of_edge_eq
  · change radial.start.1 = data.innerStub radial.inner
    exact radial.start_eq_innerStub
  · rw [innerBoundaryDart_edge]
    exact ambientRadialPath_firstDart_edgeOf_eq_innerBoundaryEdge
      hdata radial hnil

/-- Reversing the last radial dart gives exactly the outward dart of its
named outer boundary edge. -/
theorem ambientRadialPath_lastDart_symm_eq_outerBoundaryDart
    {data : AnnularBoundaryData G outerCount} (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component) :
    ((ambientRadialPath radial).lastDart
        (by rw [Walk.not_nil_iff_lt_length];
            exact lt_of_lt_of_le (by omega)
              (two_le_ambientRadialPath_length hdata radial))).symm =
      outerBoundaryDart data hdata radial.outer := by
  let path := ambientRadialPath radial
  have hnil : ¬path.Nil := by
    rw [Walk.not_nil_iff_lt_length]
    exact lt_of_lt_of_le (by omega)
      (two_le_ambientRadialPath_length hdata radial)
  apply dart_eq_of_fst_eq_of_edge_eq
  · change radial.finish.1 = data.outerStub radial.outer
    exact radial.finish_eq_outerStub
  · simpa using ambientRadialPath_lastDart_edgeOf_eq_outerBoundaryEdge
      hdata radial hnil

/-- The internal radial path after deleting its two boundary edges. -/
structure RadialCorePath
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (hdata : data.WellFormed) where
  path : G.Walk
    (innerBoundaryDart data hdata radial.inner).snd
    (outerBoundaryDart data hdata radial.outer).snd
  path_isPath : path.IsPath
  edges_eq : path.edges = (ambientRadialPath radial).edges.tail.dropLast

/-- Every radial support path has the canonical trimmed internal core. -/
theorem exists_radialCorePath
    {data : AnnularBoundaryData G outerCount} (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component) :
    Nonempty (RadialCorePath data C first second radial hdata) := by
  let ambient := ambientRadialPath radial
  have htwo : 2 ≤ ambient.length :=
    two_le_ambientRadialPath_length hdata radial
  have hnil : ¬ambient.Nil := by
    rw [Walk.not_nil_iff_lt_length]
    omega
  have htailNil : ¬ambient.tail.Nil := by
    rw [Walk.not_nil_iff_lt_length]
    simp [Walk.tail]
    omega
  have hstart : ambient.snd =
      (innerBoundaryDart data hdata radial.inner).snd := by
    have hdart := ambientRadialPath_firstDart_eq_innerBoundaryDart hdata radial
    exact congrArg (fun dart : G.Dart => dart.snd) hdart
  have hfinish : ambient.penultimate =
      (outerBoundaryDart data hdata radial.outer).snd := by
    have hdart := ambientRadialPath_lastDart_symm_eq_outerBoundaryDart
      hdata radial
    exact congrArg (fun dart : G.Dart => dart.snd) hdart
  have hpenultimate : ambient.tail.penultimate = ambient.penultimate := by
    symm
    calc
      ambient.penultimate =
          (Walk.cons (ambient.adj_snd hnil) ambient.tail).penultimate :=
        congrArg Walk.penultimate (ambient.cons_tail_eq hnil).symm
      _ = ambient.tail.penultimate :=
        Walk.penultimate_cons_of_not_nil _ _ htailNil
  let raw := ambient.tail.dropLast
  let core : G.Walk
      (innerBoundaryDart data hdata radial.inner).snd
      (outerBoundaryDart data hdata radial.outer).snd :=
    raw.copy hstart (hpenultimate.trans hfinish)
  have hrawPath : raw.IsPath := by
    rw [Walk.isPath_def]
    rw [Walk.support_dropLast htailNil]
    rw [List.dropLast_eq_take]
    exact List.Nodup.sublist (List.take_sublist _ _)
      (ambientRadialPath_isPath radial).tail.support_nodup
  refine ⟨⟨core, ?_, ?_⟩⟩
  · simpa [core] using hrawPath
  · simp [core, raw, ambient, Walk.dropLast, Walk.tail, Walk.edges_take,
      Walk.edges_drop, List.dropLast_eq_take]

end GoertzelV24ClosedWebTrimmedRadialPath

end Mettapedia.GraphTheory.FourColor
