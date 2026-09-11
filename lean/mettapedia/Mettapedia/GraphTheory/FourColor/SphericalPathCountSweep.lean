import Mettapedia.GraphTheory.FourColor.SphericalPathBondSweep
import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedEdgeTrail

/-!
# Path cuts reach the exact Count descent after an endpoint buffer

A connected cubic side with at least as many vertices as crossing edges
contains a cycle. Thus sufficiently long terminal blocks turn the actual
canonical path cuts into connected Count nodes. The endpoints cannot be
ignored: an optimal bond may isolate a single vertex.

The resulting bound concerns a real simple path and its constructed minimum
cuts, not an assumed sequence of nodes. It does not assert that their widths
are uniformly bounded or that a large width itself yields a reduction.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalPathCountSweep

open SimpleGraph SimpleGraphDartRotation CanonicalTerminalCuts SphericalPathBondSweep
open SphericalCanonicalTerminalBonds GoertzelV24RotationMultigraphAdapter
open GoertzelV24CubicSmallBoundaryCycle GoertzelV24TwoEdgeCutMinimality
open GoertzelV24SimpleGraphTaitBridge GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24ConnectedShoreLiteralNode GoertzelV24MajorityShoreStateDescent
open GoertzelV24MeshIsoperimetry

noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite] {u v : V}

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G

/-- All original edges crossing a vertex side, without a chosen sub-boundary. -/
def cut (S : Finset V) : Finset G.edgeSet :=
  Finset.univ.filter (EdgeCrossesVertexSide G (· ∈ S))

omit [DecidableEq V] [G.LocallyFinite] in
theorem mem_cut (S : Finset V) (e : G.edgeSet) :
    e ∈ cut (G := G) S ↔ EdgeCrossesVertexSide G (· ∈ S) e := by simp [cut]

omit [G.LocallyFinite] in
theorem cut_compl (S : Finset V) : cut (G := G) Sᶜ = cut (G := G) S := by
  ext e
  simpa only [mem_cut, Finset.mem_compl] using edgeCrossesVertexSide_compl G (· ∈ S) e

omit [G.LocallyFinite] in
/-- The graph cut is exactly the edge set minimized by the rotation adapter. -/
theorem cut_eq_boundaryEdges (data : Data G) (S : Finset V) :
    cut (G := G) S = boundaryEdges (toMultigraph data.toRotationSystem) S := by
  ext e
  let d : G.Dart := someDart data.toRotationSystem e
  have he : (e : Sym2 V) = s(d.fst, d.snd) := by
    have h := congrArg Subtype.val (edgeOf_someDart data.toRotationSystem e)
    exact h.symm
  simp only [mem_cut, boundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  change EdgeCrossesVertexSide G (· ∈ S) e ↔
    (d.fst ∈ S ∧ d.snd ∉ S) ∨ (d.fst ∉ S ∧ d.snd ∈ S)
  constructor
  · intro h
    have hn := not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq he h
    tauto
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact ⟨d.fst, d.snd, he ▸ Sym2.mem_mk_left _ _, he ▸ Sym2.mem_mk_right _ _, ha, hb⟩
    · exact ⟨d.snd, d.fst, he ▸ Sym2.mem_mk_right _ _, he ▸ Sym2.mem_mk_left _ _, hb, ha⟩

/-- Degree counting rules out an acyclic connected side above its tree budget. -/
theorem cycle_of_card (hcubic : G.IsRegularOfDegree 3) (S : Finset V)
    (hconn : (G.induce (↑S : Set V)).Connected)
    (hcard : (cut (G := G) S).card ≤ S.card) : HasCycleOnSide G (· ∈ S) := by
  have h := hasCycleOnSide_or_card_le_two_mul_exception_add_removed_sub_two
    (G := G) (· ∈ S) (fun _ => False) (by simp) (fun x _ _ => hcubic x)
    hconn (cut S) (by
      intro d
      exact (mem_cut S _).mpr ⟨d.1.fst, d.1.snd,
        Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _, d.2.1, d.2.2⟩)
  rcases h with h | h
  · exact h
  · have hn : 0 < S.card := by
      obtain ⟨x⟩ := hconn.nonempty
      exact Finset.card_pos.mpr ⟨x, x.property⟩
    simp only [Finset.filter_false, Finset.card_empty, mul_zero, zero_add,
      Fintype.card_coe] at h
    omega

omit [Fintype V] [DecidableRel G.Adj] [G.LocallyFinite] in
theorem prefix_card (p : G.Walk u v) (hp : p.IsPath) {t : Nat} (ht : t < p.length) :
    (prefixSide p t).card = t + 1 := by
  rw [prefixSide, List.toFinset_card_of_nodup hp.support_nodup.take]
  simp only [List.length_take, Walk.length_support]
  omega

omit [Fintype V] [DecidableRel G.Adj] [G.LocallyFinite] in
theorem suffix_card (p : G.Walk u v) (hp : p.IsPath) (t : Nat) :
    (suffix p t).card = p.length - t := by
  rw [suffix, List.toFinset_card_of_nodup hp.support_nodup.drop]
  simp [Walk.length_support]

/-- Endpoint blocks large enough for the actual cut supply both cycles. -/
def realization (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (hcubic : G.IsRegularOfDegree 3) (p : G.Walk u v) (hp : p.IsPath)
    (t : Fin p.length) (w : Nat) (hw : (cut (G := G) (side data p hp t)).card ≤ w)
    (ha : w ≤ t.val + 1) (hb : w ≤ p.length - t.val) :
    CyclicEdgeCutRealization G (cut (side data p hp t)) := by
  let S := side data p hp t
  have hc := connected_sides data ambient _ _ (prefix_connected p t)
    (suffix_connected p t.isLt) (terminals_disjoint p hp t)
  have hf := (canonical_spec (toMultigraph data.toRotationSystem)
    (prefixSide p t) (suffix p t) (terminals_disjoint p hp t)).feasible
  have hAs : w ≤ S.card := by
    have hsize : (prefixSide p t).card ≤ S.card := Finset.card_le_card hf.1
    rw [prefix_card p hp t.isLt] at hsize
    omega
  have hBs : w ≤ Sᶜ.card := by
    have hsub : suffix p t ⊆ Sᶜ := by
      intro x hx
      exact Finset.mem_compl.mpr (fun hs => Finset.disjoint_left.mp hf.2 hs hx)
    have := Finset.card_le_card hsub
    rw [suffix_card p hp] at this
    omega
  refine ⟨(· ∈ S), mem_cut S, cycle_of_card hcubic S hc.1 (hw.trans hAs), ?_⟩
  have hi := cycle_of_card hcubic Sᶜ hc.2 (by rw [cut_compl]; exact hw.trans hBs)
  simpa only [Finset.mem_compl] using hi

/-- A concrete Count node, with no supplied cycle or majority-side receipt. -/
def node (data : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.length) (w : Nat)
    (hw : (cut (G := G) (side data p hp t)).card ≤ w)
    (ha : w ≤ t.val + 1) (hb : w ≤ p.length - t.val) :
    ConnectedShoreNode (G := G) w w := by
  have hi := incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
    data minimal.spherical.cubic
  have hd : G.IsRegularOfDegree 3 := fun x => by
    have hdeg := GoertzelV24DeletedEdgeTrail.incidentEdgeFinset_card_eq_degree (H := G) x
    exact (degree_instance_independent x _ _).trans (hdeg.symm.trans (hi x))
  let r := realization data minimal.toBridgelessSphericalCubicMapData hd p hp t w hw ha hb
  have hc := connected_sides data minimal.toBridgelessSphericalCubicMapData _ _
    (prefix_connected p t) (suffix_connected p t.isLt) (terminals_disjoint p hp t)
  exact r.toConnectedShoreNodeOfConnectedSides hi hc.1
    (by
      change (G.induce {x | x ∉ side data p hp t}).Connected
      have heq : {x | x ∉ side data p hp t} = (↑((side data p hp t)ᶜ) : Set V) := by
        ext x
        simp
      rw [heq]
      exact hc.2) w hw

@[simp] theorem node_shore (data : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.length) (w : Nat)
    (hw : (cut (G := G) (side data p hp t)).card ≤ w)
    (ha : w ≤ t.val + 1) (hb : w ≤ p.length - t.val) :
    (node data minimal p hp t w hw ha hb).shore = incidentEdgeShore G (· ∈ side data p hp t) := rfl

/-- The existing exact phased-state carrier, with boundary and middle bound `w`. -/
def stateBound (w : Nat) : Nat :=
  (6 * w + 1) * (∑ j : Fin (w + 1), Nat.factorial (j : Nat) * 2 ^ (3 ^ (j : Nat)))

/-- An interior segment of the actual path supplies all nodes to pumping.
No cycle, node, exact-state, or strict-nesting supplier is assumed. -/
theorem buffered_length_le (data : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (p : G.Walk u v) (hp : p.IsPath) (w n : Nat) (hn : n + 2 * w ≤ p.length)
    (hwidth : ∀ t : Fin p.length, (cut (G := G) (side data p hp t)).card ≤ w) :
    n ≤ stateBound w := by
  let idx (i : Fin n) : Fin p.length := ⟨w + i.rev.val, by have := i.rev.isLt; omega⟩
  have ha (i : Fin n) : w ≤ (idx i).val + 1 := by dsimp [idx]; omega
  have hb (i : Fin n) : w ≤ p.length - (idx i).val := by
    have := i.rev.isLt
    dsimp [idx]
    omega
  let nodes (i : Fin n) :=
    (node data minimal p hp (idx i) w (hwidth _) (ha i) (hb i)).toLiteral data minimal
  apply length_le_of_literalShoreChain data minimal w w n nodes
  intro i j hij
  have hr : j.rev < i.rev := by simpa using hij
  have hidx : idx j < idx i := by change w + j.rev.val < w + i.rev.val; omega
  have hs := (side_strict data minimal.toBridgelessSphericalCubicMapData p hp hidx).2
  simpa only [nodes, ConnectedShoreNode.toLiteral_shore, node_shore] using hs

/-- Long simple paths cannot have uniformly narrow canonical full cuts in a
least counterexample. The additive buffer discards potentially acyclic ends. -/
theorem length_le (data : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (p : G.Walk u v) (hp : p.IsPath) (w : Nat)
    (hwidth : ∀ t : Fin p.length, (cut (G := G) (side data p hp t)).card ≤ w) :
    p.length ≤ stateBound w + 2 * w := by
  by_cases h : 2 * w ≤ p.length
  · have hn := buffered_length_le data minimal p hp w (p.length - 2 * w) (by omega) hwidth
    omega
  · omega

/-- The wide-cut alternative is proved for the constructed optimum, not
merely for one badly chosen sweep. It is not yet a wide-cut reduction. -/
theorem exists_wide_cut (data : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (p : G.Walk u v) (hp : p.IsPath) (w : Nat)
    (hlong : stateBound w + 2 * w < p.length) :
    ∃ t : Fin p.length, w < (cut (G := G) (side data p hp t)).card := by
  by_contra h
  push Not at h
  have := length_le data minimal p hp w h
  omega

/-- A long path forces a terminal split for which EVERY complete separating
cut is wide. This removes arbitrary choices of off-path cap ownership. -/
theorem exists_wide_separation (data : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (p : G.Walk u v) (hp : p.IsPath) (w : Nat)
    (hlong : stateBound w + 2 * w < p.length) :
    ∃ t : Fin p.length, ∀ S : Finset V, Feasible (prefixSide p t) (suffix p t) S →
      w < (cut (G := G) S).card := by
  obtain ⟨t, ht⟩ := exists_wide_cut data minimal p hp w hlong
  refine ⟨t, fun S hS => ?_⟩
  have hm := (canonical_spec (toMultigraph data.toRotationSystem)
    (prefixSide p t) (suffix p t) (terminals_disjoint p hp t)).width_min S hS
  rw [cut_eq_boundaryEdges data] at ht ⊢
  exact ht.trans_le hm

end
end Mettapedia.GraphTheory.FourColor.SphericalPathCountSweep
