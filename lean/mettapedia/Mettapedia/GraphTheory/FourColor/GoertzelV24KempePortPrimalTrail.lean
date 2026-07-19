import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionSites
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeTerminalProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24LineGraphOpenPrimalLift

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance primalTrailGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Every simple bicolored port route is internally primal-coherent. -/
theorem EvenKempePortPath.ambientPath_isPrimalCoherentForLift
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b : Color}
    {left right : Fin portCount}
    (route : data.EvenKempePortPath C a b left right) :
    route.ambientPath.IsPrimalCoherent := by
  intro position hposition
  apply SimpleGraph.Walk.lineGraphJunctionAt_ne_succ_of_bicolored
    (C := C) (a := a) (b := b)
    (walk := route.ambientPath)
    (hpath := route.ambientPath_isPath)
    (hcolors := by
      intro edge hedge
      exact (route.mem_ambientPath_support_iff edge).1 hedge |>.1)
    (position := position) hposition

/-- A positive port route cannot use the boundary defect as its first
line-graph junction. -/
theorem EvenKempePortPath.leftDefect_ne_firstJunction
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b : Color}
    {left right : Fin portCount}
    (route : data.EvenKempePortPath C a b left right)
    (hdata : data.WellFormed) (hab : ValidColorPair a b)
    (hleftSelected : data.colorWord C left = a ∨
      data.colorWord C left = b)
    (hpositive : 0 < route.ambientPath.length) :
    data.defectVertex left ≠
      route.ambientPath.lineGraphJunctionAt ⟨0, hpositive⟩ := by
  intro hjunction
  have hnextMem := route.ambientPath.lineGraphJunctionAt_mem_right
    ⟨0, hpositive⟩
  have hdefectMem : data.defectVertex left ∈
      ((route.ambientPath.getVert 1).1 : Sym2 V) := by
    rw [hjunction]
    exact hnextMem
  have hnextIncident : route.ambientPath.getVert 1 ∈
      incidentEdgeFinset G (data.defectVertex left) := by
    simpa [incidentEdgeFinset] using hdefectMem
  have hnextSupport : route.ambientPath.getVert 1 ∈
      route.ambientPath.support :=
    route.ambientPath.getVert_mem_support 1
  have hnextSelected :
      C (route.ambientPath.getVert 1) = a ∨
        C (route.ambientPath.getVert 1) = b :=
    (route.mem_ambientPath_support_iff
      (route.ambientPath.getVert 1)).1 hnextSupport |>.1
  rcases data.existsUnique_incident_bicolored_edge_of_colorWord_selected
      hdata C hab left hleftSelected with
    ⟨selectedEdge, _hselectedEdge, hunique⟩
  have hnextEq : route.ambientPath.getVert 1 = route.leftEdge.1 :=
    (hunique _ ⟨hnextIncident, hnextSelected⟩).trans
      (hunique _ ⟨route.leftIncident, route.leftEdge.2⟩).symm
  have hadj := route.ambientPath.adj_getVert_succ
    (i := 0) hpositive
  exact hadj.ne (by
    simpa only [route.ambientPath.getVert_zero] using hnextEq.symm)

/-- The symmetric no-bounce fact at the final boundary defect. -/
theorem EvenKempePortPath.lastJunction_ne_rightDefect
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b : Color}
    {left right : Fin portCount}
    (route : data.EvenKempePortPath C a b left right)
    (hdata : data.WellFormed) (hab : ValidColorPair a b)
    (hrightSelected : data.colorWord C right = a ∨
      data.colorWord C right = b)
    (hpositive : 0 < route.ambientPath.length) :
    route.ambientPath.lineGraphJunctionAt
        ⟨route.ambientPath.length - 1,
          Nat.sub_lt hpositive Nat.zero_lt_one⟩ ≠
      data.defectVertex right := by
  intro hjunction
  let finalPosition : Fin route.ambientPath.length :=
    ⟨route.ambientPath.length - 1,
      Nat.sub_lt hpositive Nat.zero_lt_one⟩
  have hpreviousMem := route.ambientPath.lineGraphJunctionAt_mem_left
    finalPosition
  have hdefectMem : data.defectVertex right ∈
      ((route.ambientPath.getVert
        (route.ambientPath.length - 1)).1 : Sym2 V) := by
    rw [← hjunction]
    exact hpreviousMem
  have hpreviousIncident :
      route.ambientPath.getVert (route.ambientPath.length - 1) ∈
        incidentEdgeFinset G (data.defectVertex right) := by
    simpa [incidentEdgeFinset] using hdefectMem
  have hpreviousSupport :
      route.ambientPath.getVert (route.ambientPath.length - 1) ∈
        route.ambientPath.support :=
    route.ambientPath.getVert_mem_support _
  have hpreviousSelected :
      C (route.ambientPath.getVert
          (route.ambientPath.length - 1)) = a ∨
        C (route.ambientPath.getVert
          (route.ambientPath.length - 1)) = b :=
    (route.mem_ambientPath_support_iff
      (route.ambientPath.getVert
        (route.ambientPath.length - 1))).1 hpreviousSupport |>.1
  rcases data.existsUnique_incident_bicolored_edge_of_colorWord_selected
      hdata C hab right hrightSelected with
    ⟨selectedEdge, _hselectedEdge, hunique⟩
  have hpreviousEq :
      route.ambientPath.getVert (route.ambientPath.length - 1) =
        route.rightEdge.1 :=
    (hunique _ ⟨hpreviousIncident, hpreviousSelected⟩).trans
      (hunique _ ⟨route.rightIncident, route.rightEdge.2⟩).symm
  have hadj := route.ambientPath.adj_getVert_succ
    (i := route.ambientPath.length - 1) (by omega)
  exact hadj.ne (by
    have hlast : route.ambientPath.length - 1 + 1 =
        route.ambientPath.length := by omega
    simpa only [hlast, route.ambientPath.getVert_length] using hpreviousEq)

/-- A simple Kempe route between distinct boundary ports has a primal
trail using exactly the primal edges represented by its line-graph support.
The zero-length line route is the single primal edge joining the ports. -/
theorem EvenKempePortPath.exists_primalTrail
    {portCount : Nat} {data : DegreeTwoBoundaryData G portCount}
    {C : G.EdgeColoring Color} {a b : Color}
    {left right : Fin portCount}
    (route : data.EvenKempePortPath C a b left right)
    (hdata : data.WellFormed) (hab : ValidColorPair a b)
    (hleftSelected : data.colorWord C left = a ∨
      data.colorWord C left = b)
    (hrightSelected : data.colorWord C right = a ∨
      data.colorWord C right = b)
    (hleftRight : left ≠ right) :
    ∃ trail : G.Walk (data.defectVertex left) (data.defectVertex right),
      trail.IsTrail ∧
        trail.edges = route.ambientPath.support.map Subtype.val := by
  by_cases hzero : route.ambientPath.length = 0
  · have hedgeEq : route.leftEdge.1 = route.rightEdge.1 :=
      SimpleGraph.Walk.eq_of_length_eq_zero hzero
    have hleftMem : data.defectVertex left ∈
        (route.leftEdge.1.1 : Sym2 V) := by
      simpa [incidentEdgeFinset] using route.leftIncident
    have hrightMem : data.defectVertex right ∈
        (route.leftEdge.1.1 : Sym2 V) := by
      simpa [hedgeEq, incidentEdgeFinset] using route.rightIncident
    have hverticesNe :
        data.defectVertex left ≠ data.defectVertex right := by
      intro hvertices
      exact hleftRight (hdata.1 hvertices)
    have hedgePair : route.leftEdge.1.1 =
        s(data.defectVertex left, data.defectVertex right) :=
      sym2_eq_mk_of_mem_of_mem_of_ne hleftMem hrightMem hverticesNe
    have hadj : G.Adj (data.defectVertex left)
        (data.defectVertex right) := by
      have := route.leftEdge.1.2
      rw [hedgePair] at this
      exact this
    let trail := hadj.toWalk
    refine ⟨trail, (SimpleGraph.Walk.IsPath.of_adj hadj).isTrail, ?_⟩
    have hnil : route.ambientPath.Nil :=
      SimpleGraph.Walk.length_eq_zero_iff.mp hzero
    have hsupport : route.ambientPath.support = [route.leftEdge.1] :=
      SimpleGraph.Walk.nil_iff_support_eq.mp hnil
    simp [trail, hsupport, ← hedgePair]
  · have hpositive : 0 < route.ambientPath.length := Nat.pos_of_ne_zero hzero
    have hcoherent := route.ambientPath_isPrimalCoherentForLift
    have hstartMem : data.defectVertex left ∈
        (route.leftEdge.1.1 : Sym2 V) := by
      simpa [incidentEdgeFinset] using route.leftIncident
    have hendMem : data.defectVertex right ∈
        (route.rightEdge.1.1 : Sym2 V) := by
      simpa [incidentEdgeFinset] using route.rightIncident
    have hstartNe := route.leftDefect_ne_firstJunction
      hdata hab hleftSelected hpositive
    have hendNe := route.lastJunction_ne_rightDefect
      hdata hab hrightSelected hpositive
    let trail := route.ambientPath.cappedPrimalLift
      hpositive hcoherent (data.defectVertex left)
        (data.defectVertex right) hstartMem hendMem hstartNe hendNe
    refine ⟨trail, ?_, ?_⟩
    · exact route.ambientPath.cappedPrimalLift_isTrail_of_isPath
        hpositive hcoherent route.ambientPath_isPath
        (data.defectVertex left) (data.defectVertex right)
        hstartMem hendMem hstartNe hendNe
    · exact route.ambientPath.cappedPrimalLift_edges_eq_map_support
        hpositive hcoherent (data.defectVertex left)
        (data.defectVertex right) hstartMem hendMem hstartNe hendNe

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

end Mettapedia.GraphTheory.FourColor
