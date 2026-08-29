import Mettapedia.GraphTheory.FourColor.GoertzelV24CyclicBondBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutAlternatingTrail

/-!
# Alternating trails at an arbitrary cyclic bond boundary

The four-edge-cut theorem already proves the face-label separation argument
when the four relevant ports are consecutive.  A physical Kempe component at
a wider interface can have unused ports between its endpoints.  This file
isolates the missing generalization: face labels propagate along every arc of
the cyclic boundary whose primal edges avoid the separating trail.

No topological predicate is postulated here.  The cyclic order is the actual
retained facial first-return order of `CyclicBondBoundaryData`, and separation
is witnessed by the exact face labeling of a closed trail in a spherical
combinatorial map.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CyclicBoundaryAlternatingTrail

open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24CyclicBondBoundary
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourEdgeCutAlternatingTrail
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24WalkFaceCut
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The recorded cyclic coordinate order computes the retained facial
successor pointwise. -/
theorem retainedRegionBoundarySuccessor_order
    (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (port : Fin data.length) :
    retainedRegionBoundarySuccessor graphData.toRotationSystem keep
        (data.order port) =
      data.order (finRotate data.length port) := by
  have happly := DFunLike.congr_fun data.successor_eq (data.order port)
  rw [Equiv.permCongr_apply, data.order.symm_apply_apply] at happly
  exact happly.symm

/-- Consecutive ports in retained first-return order expose two darts of one
ambient face: the outside half of the current boundary edge and the inside
half of the next one. -/
theorem boundaryOrder_alpha_sameFace_next
    (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (port : Fin data.length) :
    dartOrbitFace graphData.toRotationSystem
        (graphData.toRotationSystem.alpha (data.order port).1.1) =
      dartOrbitFace graphData.toRotationSystem
        (data.order (finRotate data.length port)).1.1 := by
  apply Quotient.sound
  have hface := retainedRegionBoundarySuccessor_sameAmbientFace_alpha
    graphData.toRotationSystem keep (data.order port)
  rw [retainedRegionBoundarySuccessor_order graphData keep data port] at hface
  exact hface

/-- If one boundary edge avoids a face cut, the face label propagates to the
next boundary coordinate. -/
theorem labels_eq_next_of_boundaryEdge_not_cut
    (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (port : Fin data.length)
    (hnot : ¬cut (graphData.toRotationSystem.edgeOf
      (data.order port).1.1)) :
    labels (dartOrbitFace graphData.toRotationSystem
        (data.order port).1.1) =
      labels (dartOrbitFace graphData.toRotationSystem
        (data.order (finRotate data.length port)).1.1) := by
  have hsameAcross :
      labels (dartOrbitFace graphData.toRotationSystem
          (data.order port).1.1) =
        labels (dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha (data.order port).1.1)) := by
    apply not_ne_iff.mp
    exact fun hne => hnot ((hexact (data.order port).1.1).1 hne)
  exact hsameAcross.trans
    (congrArg labels (boundaryOrder_alpha_sameFace_next
      graphData keep data port))

/-- Face labels propagate through any finite run of boundary coordinates
whose primal edges all avoid the cut. -/
theorem labels_eq_iterate_of_boundaryEdges_not_cut
    (graphData : Data G) (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    {A : Type*} (labels : OrbitFace graphData.toRotationSystem → A)
    (cut : G.edgeSet → Prop)
    (hexact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        cut (graphData.toRotationSystem.edgeOf dart))
    (start : Fin data.length) (steps : Nat)
    (havoid : ∀ index, index < steps →
      ¬cut (graphData.toRotationSystem.edgeOf
        (data.order ((finRotate data.length)^[index] start)).1.1)) :
    labels (dartOrbitFace graphData.toRotationSystem
        (data.order start).1.1) =
      labels (dartOrbitFace graphData.toRotationSystem
        (data.order ((finRotate data.length)^[steps] start)).1.1) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hprefix : ∀ index, index < steps →
          ¬cut (graphData.toRotationSystem.edgeOf
            (data.order ((finRotate data.length)^[index] start)).1.1) := by
        intro index hindex
        exact havoid index (Nat.lt_succ_of_lt hindex)
      have hlast := labels_eq_next_of_boundaryEdge_not_cut
        graphData keep data labels cut hexact
        ((finRotate data.length)^[steps] start)
        (havoid steps (Nat.lt_succ_self steps))
      exact (ih hprefix).trans (by
        simpa only [Function.iterate_succ_apply'] using hlast)

/-- A closed trail which crosses one boundary edge separates the two cyclic
boundary arcs adjacent to it.  Hence an edge-disjoint trail cannot join a
port reached along the forward arc to a port whose forward arc returns to
the crossed edge.

The explicit iteration witnesses avoid any hidden appeal to a drawing.  In
the six-port application they are discharged by the finite cyclic order of
four alternating endpoints. -/
theorem no_disjoint_trail_between_boundary_arcs
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (cutPort leftPort rightPort : Fin data.length)
    (leftSteps rightSteps : Nat)
    (hleftPort :
      (finRotate data.length)^[leftSteps]
          (finRotate data.length cutPort) = leftPort)
    (hrightPort :
      (finRotate data.length)^[rightSteps] rightPort = cutPort)
    {base : V} (separator : G.Walk base base)
    (hseparator : separator.IsTrail)
    (hcut : (graphData.toRotationSystem.edgeOf
      (data.order cutPort).1.1).1 ∈ separator.edges)
    (hleftBoundary : (graphData.toRotationSystem.edgeOf
      (data.order leftPort).1.1).1 ∉ separator.edges)
    (hrightBoundary : (graphData.toRotationSystem.edgeOf
      (data.order rightPort).1.1).1 ∉ separator.edges)
    (hleftArc : ∀ index, index < leftSteps →
      (graphData.toRotationSystem.edgeOf
        (data.order ((finRotate data.length)^[index]
          (finRotate data.length cutPort))).1.1).1 ∉ separator.edges)
    (hrightArc : ∀ index, index < rightSteps →
      (graphData.toRotationSystem.edgeOf
        (data.order ((finRotate data.length)^[index] rightPort)).1.1).1 ∉
          separator.edges)
    (route : G.Walk
      (graphData.toRotationSystem.vertOf (data.order leftPort).1.1)
      (graphData.toRotationSystem.vertOf (data.order rightPort).1.1))
    (hrouteNil : ¬route.Nil) (hrouteTrail : route.IsTrail)
    (hrouteDisjoint : ∀ edge : G.edgeSet,
      edge.1 ∈ route.edges → edge.1 ∉ separator.edges)
    (hfirstNe : route.firstDart hrouteNil ≠ (data.order leftPort).1.1)
    (hlastNe : graphData.toRotationSystem.alpha
        (route.lastDart hrouteNil) ≠ (data.order rightPort).1.1) :
    False := by
  rcases exists_orbitFaceLabeling_ne_alpha_iff_mem_edges_of_isTrail
      graphData htwoSided hdual hconnected hsphere separator hseparator with
    ⟨labels, _hlabels, hexact⟩
  let dCut := (data.order cutPort).1.1
  let dNext := (data.order (finRotate data.length cutPort)).1.1
  let dLeft := (data.order leftPort).1.1
  let dRight := (data.order rightPort).1.1
  have hcutNe :
      labels (dartOrbitFace graphData.toRotationSystem dCut) ≠
        labels (dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha dCut)) :=
    (hexact dCut).2 hcut
  have hcutNext :
      dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha dCut) =
        dartOrbitFace graphData.toRotationSystem dNext := by
    simpa [dCut, dNext] using boundaryOrder_alpha_sameFace_next
      graphData keep data cutPort
  have hnextLeft :
      labels (dartOrbitFace graphData.toRotationSystem dNext) =
        labels (dartOrbitFace graphData.toRotationSystem dLeft) := by
    have hpropagate := labels_eq_iterate_of_boundaryEdges_not_cut
      graphData keep data labels
      (fun edge : G.edgeSet => edge.1 ∈ separator.edges) hexact
      (finRotate data.length cutPort) leftSteps hleftArc
    rw [hleftPort] at hpropagate
    exact hpropagate
  have hrightCut :
      labels (dartOrbitFace graphData.toRotationSystem dRight) =
        labels (dartOrbitFace graphData.toRotationSystem dCut) := by
    have hpropagate := labels_eq_iterate_of_boundaryEdges_not_cut
      graphData keep data labels
      (fun edge : G.edgeSet => edge.1 ∈ separator.edges) hexact
      rightPort rightSteps hrightArc
    rw [hrightPort] at hpropagate
    exact hpropagate
  have hleftRightNe :
      labels (dartOrbitFace graphData.toRotationSystem dLeft) ≠
        labels (dartOrbitFace graphData.toRotationSystem dRight) := by
    intro heq
    apply hcutNe
    calc
      labels (dartOrbitFace graphData.toRotationSystem dCut) =
          labels (dartOrbitFace graphData.toRotationSystem dRight) :=
        hrightCut.symm
      _ = labels (dartOrbitFace graphData.toRotationSystem dLeft) := heq.symm
      _ = labels (dartOrbitFace graphData.toRotationSystem dNext) :=
        hnextLeft.symm
      _ = labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dCut)) :=
        congrArg labels hcutNext.symm
  have hrouteExact : ∀ dart : graphData.toRotationSystem.D,
      labels (dartOrbitFace graphData.toRotationSystem dart) ≠
          labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dart)) ↔
        (graphData.toRotationSystem.edgeOf dart).1 ∈ separator.edges :=
    hexact
  have hfirstNot :
      (graphData.toRotationSystem.edgeOf (route.firstDart hrouteNil)).1 ∉
        separator.edges := by
    apply hrouteDisjoint
    change (route.firstDart hrouteNil).edge ∈ route.edges
    rw [route.edge_firstDart hrouteNil]
    exact route.mk_start_snd_mem_edges hrouteNil
  have hlastNot :
      (graphData.toRotationSystem.edgeOf
        (graphData.toRotationSystem.alpha
          (route.lastDart hrouteNil))).1 ∉ separator.edges := by
    rw [graphData.toRotationSystem.edge_alpha]
    apply hrouteDisjoint
    change (route.lastDart hrouteNil).edge ∈ route.edges
    rw [route.edge_lastDart hrouteNil]
    exact route.mk_penultimate_end_mem_edges hrouteNil
  have hfirstLabels :
      labels (dartOrbitFace graphData.toRotationSystem dLeft) =
        labels (dartOrbitFace graphData.toRotationSystem
          (route.firstDart hrouteNil)) := by
    apply graphData.toRotationSystem.labels_eq_of_distinct_dartsAt_of_edges_not_cut
      hcubic hrotation labels
        (fun edge : G.edgeSet => edge.1 ∈ separator.edges)
        hrouteExact dLeft (route.firstDart hrouteNil)
    · simp [dLeft]
    · exact hfirstNe.symm
    · exact hleftBoundary
    · exact hfirstNot
  have hlastLabels :
      labels (dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha (route.lastDart hrouteNil))) =
        labels (dartOrbitFace graphData.toRotationSystem dRight) := by
    apply graphData.toRotationSystem.labels_eq_of_distinct_dartsAt_of_edges_not_cut
      hcubic hrotation labels
        (fun edge : G.edgeSet => edge.1 ∈ separator.edges)
        hrouteExact
        (graphData.toRotationSystem.alpha (route.lastDart hrouteNil)) dRight
    · simp [dRight]
    · exact hlastNe
    · exact hlastNot
    · exact hrightBoundary
  have htransport :=
    graphData.trail_labels_eq_firstDart_alpha_lastDart_of_walk_edges_not_cut
      hcubic hrotation labels
        (fun edge : G.edgeSet => edge.1 ∈ separator.edges)
        hrouteExact route hrouteNil hrouteTrail hrouteDisjoint
  apply hleftRightNe
  exact hfirstLabels.trans (htransport.trans hlastLabels)

/-- A separating closed trail cannot put two distinct boundary darts based at
one cubic vertex on opposite cyclic boundary arcs when neither of their
boundary edges belongs to the trail.

This is the zero-primal-edge endpoint case omitted by
`no_disjoint_trail_between_boundary_arcs`.  The cyclic-arc propagation gives
opposite face labels at the two ports.  Cubic cyclic rotation gives equal
labels at two distinct darts based at one vertex whose incident edges both
avoid the exact cut. -/
theorem no_distinct_same_vertex_ports_between_boundary_arcs
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (keep : V → Prop)
    (data : CyclicBondBoundaryData graphData.toRotationSystem keep)
    (cutPort leftPort rightPort : Fin data.length)
    (hleftRight : leftPort ≠ rightPort)
    (leftSteps rightSteps : Nat)
    (hleftPort :
      (finRotate data.length)^[leftSteps]
          (finRotate data.length cutPort) = leftPort)
    (hrightPort :
      (finRotate data.length)^[rightSteps] rightPort = cutPort)
    {base : V} (separator : G.Walk base base)
    (hseparator : separator.IsTrail)
    (hcut : (graphData.toRotationSystem.edgeOf
      (data.order cutPort).1.1).1 ∈ separator.edges)
    (hleftBoundary : (graphData.toRotationSystem.edgeOf
      (data.order leftPort).1.1).1 ∉ separator.edges)
    (hrightBoundary : (graphData.toRotationSystem.edgeOf
      (data.order rightPort).1.1).1 ∉ separator.edges)
    (hleftArc : ∀ index, index < leftSteps →
      (graphData.toRotationSystem.edgeOf
        (data.order ((finRotate data.length)^[index]
          (finRotate data.length cutPort))).1.1).1 ∉ separator.edges)
    (hrightArc : ∀ index, index < rightSteps →
      (graphData.toRotationSystem.edgeOf
        (data.order ((finRotate data.length)^[index] rightPort)).1.1).1 ∉
          separator.edges)
    (hbase : graphData.toRotationSystem.vertOf
        (data.order rightPort).1.1 =
      graphData.toRotationSystem.vertOf (data.order leftPort).1.1) :
    False := by
  rcases exists_orbitFaceLabeling_ne_alpha_iff_mem_edges_of_isTrail
      graphData htwoSided hdual hconnected hsphere separator hseparator with
    ⟨labels, _hlabels, hexact⟩
  let dCut := (data.order cutPort).1.1
  let dNext := (data.order (finRotate data.length cutPort)).1.1
  let dLeft := (data.order leftPort).1.1
  let dRight := (data.order rightPort).1.1
  have hcutNe :
      labels (dartOrbitFace graphData.toRotationSystem dCut) ≠
        labels (dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha dCut)) :=
    (hexact dCut).2 hcut
  have hcutNext :
      dartOrbitFace graphData.toRotationSystem
          (graphData.toRotationSystem.alpha dCut) =
        dartOrbitFace graphData.toRotationSystem dNext := by
    simpa [dCut, dNext] using boundaryOrder_alpha_sameFace_next
      graphData keep data cutPort
  have hnextLeft :
      labels (dartOrbitFace graphData.toRotationSystem dNext) =
        labels (dartOrbitFace graphData.toRotationSystem dLeft) := by
    have hpropagate := labels_eq_iterate_of_boundaryEdges_not_cut
      graphData keep data labels
      (fun edge : G.edgeSet => edge.1 ∈ separator.edges) hexact
      (finRotate data.length cutPort) leftSteps hleftArc
    rw [hleftPort] at hpropagate
    exact hpropagate
  have hrightCut :
      labels (dartOrbitFace graphData.toRotationSystem dRight) =
        labels (dartOrbitFace graphData.toRotationSystem dCut) := by
    have hpropagate := labels_eq_iterate_of_boundaryEdges_not_cut
      graphData keep data labels
      (fun edge : G.edgeSet => edge.1 ∈ separator.edges) hexact
      rightPort rightSteps hrightArc
    rw [hrightPort] at hpropagate
    exact hpropagate
  have hleftRightNe :
      labels (dartOrbitFace graphData.toRotationSystem dLeft) ≠
        labels (dartOrbitFace graphData.toRotationSystem dRight) := by
    intro heq
    apply hcutNe
    calc
      labels (dartOrbitFace graphData.toRotationSystem dCut) =
          labels (dartOrbitFace graphData.toRotationSystem dRight) :=
        hrightCut.symm
      _ = labels (dartOrbitFace graphData.toRotationSystem dLeft) := heq.symm
      _ = labels (dartOrbitFace graphData.toRotationSystem dNext) :=
        hnextLeft.symm
      _ = labels (dartOrbitFace graphData.toRotationSystem
            (graphData.toRotationSystem.alpha dCut)) :=
        congrArg labels hcutNext.symm
  have hdartsNe : dLeft ≠ dRight := by
    intro hdarts
    apply hleftRight
    apply data.order.injective
    apply Subtype.ext
    apply Subtype.ext
    exact hdarts
  apply hleftRightNe
  apply graphData.toRotationSystem.labels_eq_of_distinct_dartsAt_of_edges_not_cut
    hcubic hrotation labels
      (fun edge : G.edgeSet => edge.1 ∈ separator.edges)
      hexact dLeft dRight
  · simpa [dLeft, dRight] using hbase
  · exact hdartsNe
  · exact hleftBoundary
  · exact hrightBoundary

end

end GoertzelV24CyclicBoundaryAlternatingTrail

end Mettapedia.GraphTheory.FourColor
