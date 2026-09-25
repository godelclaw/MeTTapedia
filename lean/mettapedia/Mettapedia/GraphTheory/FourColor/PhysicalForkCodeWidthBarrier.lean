import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalFaceSize
import Mettapedia.GraphTheory.FourColor.GoertzelV24SphericalReductiveAssembly

/-!
# No least counterexample has a decomposition of width four

A graph-backed vertex-minimal Tait counterexample is cyclically
five-edge-connected, and each of its faces has length at least five; both
facts are proved in this directory.  From them:

* the map has at least thirty edges (a spherical cubic map with no face
  shorter than five has at least twelve pentagons);
* in a cubic cyclically five-edge-connected graph, an edge shore and its
  complement with at least seven edges each have at least five middle
  vertices: otherwise the vertices carrying at least two shore edges and the
  others form a cut of at most four edges with a cycle on each side;
* every rooted branch decomposition has such a balanced cut.

Hence every rooted branch decomposition of a least counterexample has width
at least five.  A width supply at width at most four therefore excludes least
counterexamples by itself, and the audit of the finite fork-code closure at
those widths is never applied to a least counterexample.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeWidthBarrier

open Mettapedia.GraphTheory.FourColor.SimpleGraph SimpleGraphDartRotation
open GoertzelV24CubicSmallBoundaryCycle GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24SphereCutMaterial GoertzelV24MinimalFaceSize GoertzelV24MinimalTriangleFree
open GoertzelV24RotationVertexCutProfile GoertzelV24FourEdgeCutGluing
open GoertzelV24TwoEdgeCutMinimality GoertzelV24ConnectedBranchDecompositionForest
open GoertzelV24ConnectedBranchDecompositionAdapter GoertzelV24SphericalReductiveAssembly
open GoertzelV24WeightedOrbitFaceCorridor GoertzelV24FaceOrbitIncidence

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

local instance widthBarrierEdgeDecEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

local instance widthBarrierLocallyFinite : G.LocallyFinite :=
  fun vertex =>
    @Subtype.fintype V (Membership.mem (G.neighborSet vertex))
      (inferInstance : DecidablePred (Membership.mem (G.neighborSet vertex)))
      inferInstance

local instance widthBarrierMajorityDecidable (S : Finset G.edgeSet) :
    DecidablePred (majorityVertexSide G S) :=
  fun v => inferInstanceAs (Decidable (2 ≤ (shoreIncidentEdges G S v).card))

/-! ## Shore degrees in a cubic graph -/

theorem card_incidentEdgeFinset_of_regular (hregular : G.IsRegularOfDegree 3) (v : V) :
    (incidentEdgeFinset G v).card = 3 := by
  have hmap :
      (incidentEdgeFinset G v).map
          (Function.Embedding.subtype (fun edge : Sym2 V => edge ∈ G.edgeSet)) =
        G.incidenceFinset v := by
    rw [SimpleGraph.incidenceFinset_eq_filter]
    ext edge
    simp [incidentEdgeFinset, and_comm]
  calc
    (incidentEdgeFinset G v).card =
        ((incidentEdgeFinset G v).map
          (Function.Embedding.subtype (fun edge : Sym2 V => edge ∈ G.edgeSet))).card := by simp
    _ = (G.incidenceFinset v).card := by rw [hmap]
    _ = G.degree v := by simp
    _ = 3 := hregular v

omit [DecidableRel G.Adj] in
theorem card_endpoints (e : G.edgeSet) :
    (Finset.univ.filter fun v : V => v ∈ (e : Sym2 V)).card = 2 := by
  obtain ⟨e, he⟩ := e
  revert he
  refine Sym2.ind (fun a b => ?_) e
  intro he
  have hab : a ≠ b := G.ne_of_adj ((SimpleGraph.mem_edgeSet G).mp he)
  have : (Finset.univ.filter fun v : V => v ∈ s(a, b)) = {a, b} := by
    ext v
    simp
  simp only [this]
  exact Finset.card_pair hab

/-- Every edge of a shore has two ends. -/
theorem sum_card_shoreIncidentEdges (S : Finset G.edgeSet) :
    ∑ v : V, (shoreIncidentEdges G S v).card = 2 * S.card := by
  have h1 : ∀ v, (shoreIncidentEdges G S v).card =
      ∑ e ∈ S, if v ∈ (e : Sym2 V) then 1 else 0 := by
    intro v
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1
    ext e
    simp only [mem_shoreIncidentEdges_iff, Finset.mem_filter]
    tauto
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ e : G.edgeSet, (∑ v : V, if v ∈ (e : Sym2 V) then 1 else 0) = 2 := by
    intro e
    rw [Finset.sum_boole, Nat.cast_id]
    exact card_endpoints e
  rw [Finset.sum_congr rfl (fun e _ => h2 e), Finset.sum_const, smul_eq_mul, mul_comm]

theorem card_shoreIncidentEdges_le (hregular : G.IsRegularOfDegree 3) (S : Finset G.edgeSet)
    (v : V) : (shoreIncidentEdges G S v).card ≤ 3 := by
  rw [← card_incidentEdgeFinset_of_regular hregular v]
  apply Finset.card_le_card
  intro e he
  rw [mem_shoreIncidentEdges_iff] at he
  simp [incidentEdgeFinset, he.1]

/-- A vertex carrying exactly one shore edge is a middle vertex. -/
theorem mem_middle_of_card_eq_one (hregular : G.IsRegularOfDegree 3) (S : Finset G.edgeSet)
    {v : V} (hv : (shoreIncidentEdges G S v).card = 1) : v ∈ edgeShoreMiddleVertices G S := by
  have hsum := card_shoreIncidentEdges_add_complement (G := G) S v
  rw [card_incidentEdgeFinset_of_regular hregular v, hv] at hsum
  rw [mem_middleVertices_iff]
  obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < (shoreIncidentEdges G S v).card by omega)
  obtain ⟨f, hf⟩ := Finset.card_pos.mp
    (show 0 < (shoreIncidentEdges G (Finset.univ \ S) v).card by omega)
  rw [mem_shoreIncidentEdges_iff] at he hf
  exact ⟨⟨e, he.2, he.1⟩, ⟨f, (Finset.mem_sdiff.mp hf.2).2, hf.1⟩⟩

/-- The middle set of the complementary shore is the same. -/
theorem middle_compl (S : Finset G.edgeSet) :
    edgeShoreMiddleVertices G (Finset.univ \ S) = edgeShoreMiddleVertices G S := by
  ext v
  rw [mem_middleVertices_iff, mem_middleVertices_iff]
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
  tauto

/-- A shore of at least seven edges with at most four middle vertices has at
least four vertices carrying two of its edges. -/
theorem four_le_card_majority (hregular : G.IsRegularOfDegree 3) (S : Finset G.edgeSet)
    (hS : 7 ≤ S.card) (hmid : (edgeShoreMiddleVertices G S).card ≤ 4) :
    4 ≤ (Finset.univ.filter (majorityVertexSide G S)).card := by
  have hsplit :
      ∑ v ∈ Finset.univ.filter (majorityVertexSide G S), (shoreIncidentEdges G S v).card +
          ∑ v ∈ Finset.univ.filter (fun v => ¬ majorityVertexSide G S v),
            (shoreIncidentEdges G S v).card =
        ∑ v : V, (shoreIncidentEdges G S v).card :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hA : ∑ v ∈ Finset.univ.filter (majorityVertexSide G S), (shoreIncidentEdges G S v).card ≤
      3 * (Finset.univ.filter (majorityVertexSide G S)).card := by
    calc ∑ v ∈ Finset.univ.filter (majorityVertexSide G S), (shoreIncidentEdges G S v).card
        ≤ ∑ _v ∈ Finset.univ.filter (majorityVertexSide G S), 3 :=
          Finset.sum_le_sum fun v _ => card_shoreIncidentEdges_le hregular S v
      _ = 3 * (Finset.univ.filter (majorityVertexSide G S)).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hB : ∑ v ∈ Finset.univ.filter (fun v => ¬ majorityVertexSide G S v),
      (shoreIncidentEdges G S v).card ≤ (edgeShoreMiddleVertices G S).card := by
    calc ∑ v ∈ Finset.univ.filter (fun v => ¬ majorityVertexSide G S v),
          (shoreIncidentEdges G S v).card
        ≤ ∑ v ∈ Finset.univ.filter (fun v => ¬ majorityVertexSide G S v),
            (if v ∈ edgeShoreMiddleVertices G S then 1 else 0) := by
          apply Finset.sum_le_sum
          intro v hv
          have hle : (shoreIncidentEdges G S v).card ≤ 1 := by
            have := (Finset.mem_filter.mp hv).2
            simp only [majorityVertexSide] at this
            omega
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
          · rw [h0]; exact Nat.zero_le _
          · rw [h1]
            simp [mem_middle_of_card_eq_one hregular S h1]
      _ ≤ ∑ v : V, (if v ∈ edgeShoreMiddleVertices G S then 1 else 0) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = (edgeShoreMiddleVertices G S).card := by
          rw [Finset.sum_boole, Nat.cast_id]
          congr 1
          ext v
          simp
  have htotal := sum_card_shoreIncidentEdges S
  omega

/-- The crossing edges of the majority side are charged to middle vertices. -/
theorem card_crossing_majority_le (hregular : G.IsRegularOfDegree 3) (S : Finset G.edgeSet) :
    (crossingEdgeFinset G (majorityVertexSide G S)).card ≤
      (edgeShoreMiddleVertices G S).card := by
  rw [card_crossingEdgeFinset_eq_card_crossingSideDart]
  exact card_crossingSideDart_majority_le_middle (card_incidentEdgeFinset_of_regular hregular) S

/-- A cubic side with at least three vertices behind at most four crossing
edges carries a cycle. -/
theorem hasCycleOnSide_of_crossing_le_four (hregular : G.IsRegularOfDegree 3)
    (side : V → Prop) (hcard : 3 ≤ Nat.card {v : V // side v})
    (hcross : (crossingEdgeFinset G side).card ≤ 4) : HasCycleOnSide G side := by
  by_contra hno
  have hacyclic : (G.induce {v | side v}).IsAcyclic := by
    intro vertex cycle hcycle
    apply hno
    let inclusion := (SimpleGraph.Embedding.induce (G := G) {v | side v}).toHom
    refine ⟨vertex.1, vertex.2, cycle.map inclusion, ?_, ?_⟩
    · exact hcycle.map (fun _ _ heq => Subtype.ext heq)
    · intro other hother
      have hother' : other ∈ cycle.support.map inclusion :=
        SimpleGraph.Walk.support_map inclusion cycle ▸ hother
      rcases List.mem_map.mp hother' with ⟨source, _, hsource⟩
      rw [← hsource]
      exact source.2
  let carrierEquiv : ↑({v | side v} : Set V) ≃ {v : V // side v} :=
    { toFun := fun v => ⟨v.1, v.2⟩
      invFun := fun v => ⟨v.1, v.2⟩
      left_inv := fun v => by cases v; rfl
      right_inv := fun v => by cases v; rfl }
  have hnonempty : Nonempty ↑({v | side v} : Set V) := by
    have : 0 < Nat.card {v : V // side v} := by omega
    obtain ⟨x⟩ := (Nat.card_pos_iff.mp this).1
    exact ⟨carrierEquiv.symm x⟩
  have hedge := natCard_edgeSet_add_one_le_of_isAcyclic (G.induce {v | side v}) hnonempty hacyclic
  rw [Nat.card_congr carrierEquiv] at hedge
  have hcount := card_crossing_add_twice_internal_eq_three_mul hregular side
  omega

/-- **The cut lemma.**  In a cubic cyclically five-edge-connected graph, a shore
and its complement with at least seven edges each have at least five middle
vertices. -/
theorem five_le_middle (graphData : Data G) (hregular : G.IsRegularOfDegree 3)
    (hcyclic : CyclicallyFiveEdgeConnected G) (S : Finset G.edgeSet) (hS : 7 ≤ S.card)
    (hSc : 7 ≤ (Finset.univ \ S).card) : 5 ≤ (edgeShoreMiddleVertices G S).card := by
  by_contra hlt
  have hmid : (edgeShoreMiddleVertices G S).card ≤ 4 := by omega
  have hcubic := card_incidentEdgeFinset_of_regular hregular
  set inside := Finset.univ.filter (majorityVertexSide G S) with hinside
  have hsideEq : (fun v => v ∈ inside) = majorityVertexSide G S := by
    funext v
    simp [hinside]
  have hcross : (crossingEdgeFinset G (fun v => v ∈ inside)).card ≤ 4 := by
    rw [hsideEq]
    exact le_trans (card_crossing_majority_le hregular S) hmid
  have hA : 4 ≤ inside.card := four_le_card_majority hregular S hS hmid
  have hAc : 4 ≤ (Finset.univ.filter (majorityVertexSide G (Finset.univ \ S))).card :=
    four_le_card_majority hregular _ hSc (by rw [middle_compl]; exact hmid)
  have hcompl : Finset.univ.filter (majorityVertexSide G (Finset.univ \ S)) =
      Finset.univ.filter (fun v => v ∉ inside) := by
    ext v
    simp [hinside, majorityVertexSide_complement_iff hcubic]
  rw [hcompl] at hAc
  have hcardIn : 3 ≤ Nat.card {v : V // v ∈ inside} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]; omega
  have hcardOut : 3 ≤ Nat.card {v : V // v ∉ inside} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; omega
  have hcrossOut : (crossingEdgeFinset G (fun v => v ∉ inside)).card ≤ 4 := by
    have heq : crossingEdgeFinset G (fun v => v ∉ inside) =
        crossingEdgeFinset G (fun v => v ∈ inside) := by
      ext e
      rw [mem_crossingEdgeFinset_iff, mem_crossingEdgeFinset_iff]
      exact edgeCrossesVertexSide_compl G (fun v => v ∈ inside) e
    rw [heq]; exact hcross
  have hin := hasCycleOnSide_of_crossing_le_four hregular _ hcardIn hcross
  have hout := hasCycleOnSide_of_crossing_le_four hregular _ hcardOut hcrossOut
  have hfive := five_le_card_vertexSetCrossingEdges_of_cycles graphData inside hcyclic hin hout
  have heq : vertexSetCrossingEdges graphData.toRotationSystem inside =
      crossingEdgeFinset G (fun v => v ∈ inside) := by
    ext e
    rw [mem_simpleGraph_vertexSetCrossingEdges_iff, mem_crossingEdgeFinset_iff]
  rw [heq] at hfive
  omega

/-! ## A balanced cut in every tree -/

/-- A property of every cut of a tree, leaf cuts included. -/
def EveryCut (Q : Finset G.edgeSet → Prop) : EdgeLeafTree G.edgeSet → Prop
  | .leaf e => Q {e}
  | .fork l r => Q (EdgeLeafTree.fork l r).shore ∧ EveryCut Q l ∧ EveryCut Q r

omit [Fintype V] [DecidableRel G.Adj] in
theorem card_shore_of_nodup (t : EdgeLeafTree G.edgeSet) (h : t.leafList.Nodup) :
    t.shore.card = t.leafList.length := by
  unfold EdgeLeafTree.shore
  exact List.toFinset_card_of_nodup h

omit [Fintype V] [DecidableRel G.Adj] in
/-- **A balanced cut.**  A tree with at least `k` leaves has a cut whose shore
has between `k` and `2k - 1` edges. -/
theorem exists_balanced_cut (Q : Finset G.edgeSet → Prop) (k : ℕ) (hk : 1 ≤ k) :
    ∀ t : EdgeLeafTree G.edgeSet, t.leafList.Nodup → EveryCut Q t → k ≤ t.shore.card →
      ∃ S, Q S ∧ k ≤ S.card ∧ S.card < 2 * k
  | .leaf e, _, hQ, hcard => by
      refine ⟨{e}, hQ, ?_, ?_⟩
      · have : (EdgeLeafTree.leaf e).shore = ({e} : Finset G.edgeSet) := by
          simp [EdgeLeafTree.shore, EdgeLeafTree.leafList]
        rw [this] at hcard; exact hcard
      · simp; omega
  | .fork l r, hnd, hQ, hcard => by
      by_cases hsmall : (EdgeLeafTree.fork l r).shore.card < 2 * k
      · exact ⟨_, hQ.1, hcard, hsmall⟩
      · have hl : l.leafList.Nodup := List.Nodup.of_append_left hnd
        have hr : r.leafList.Nodup := List.Nodup.of_append_right hnd
        have hsum : (EdgeLeafTree.fork l r).shore.card = l.shore.card + r.shore.card := by
          rw [card_shore_of_nodup _ hnd, card_shore_of_nodup _ hl, card_shore_of_nodup _ hr]
          simp [EdgeLeafTree.leafList]
        by_cases hlk : k ≤ l.shore.card
        · exact exists_balanced_cut Q k hk l hl hQ.2.1 hlk
        · exact exists_balanced_cut Q k hk r hr hQ.2.2 (by omega)

theorem everyCut_of_widthAtMost {w : ℕ} :
    ∀ t : EdgeLeafTree G.edgeSet, EveryCutWidthAtMost (G := G) w t →
      EveryCut (fun S => (edgeShoreMiddleVertices G S).card ≤ w) t
  | .leaf _, h => h
  | .fork l r, h => ⟨h.1, everyCut_of_widthAtMost l h.2.1, everyCut_of_widthAtMost r h.2.2⟩

theorem everyCut_of_geometry {k w : ℕ} :
    ∀ t : EdgeLeafTree G.edgeSet, EveryForkGeometry (G := G) k w t →
      EveryCut (fun S => S.card < 7 ∨ (edgeShoreMiddleVertices G S).card ≤ w) t
  | .leaf _, _ => Or.inl (by simp)
  | .fork l r, h =>
      ⟨Or.inr h.1.middleBound, everyCut_of_geometry l h.2.1, everyCut_of_geometry r h.2.2⟩

/-! ## The width of a least counterexample -/

/-- Leaves of the two rooted subtrees. -/
theorem card_left_add_right {l r : EdgeLeafTree G.edgeSet} {e0 : G.edgeSet}
    (hnd : (e0 :: (l.leafList ++ r.leafList)).Nodup)
    (hcover : (e0 :: (l.leafList ++ r.leafList)).toFinset = Finset.univ) :
    l.shore.card + r.shore.card + 1 = Fintype.card G.edgeSet := by
  have hlen := List.toFinset_card_of_nodup hnd
  rw [hcover, Finset.card_univ] at hlen
  have hl : l.leafList.Nodup := (List.nodup_cons.mp hnd).2.of_append_left
  have hr : r.leafList.Nodup := (List.nodup_cons.mp hnd).2.of_append_right
  rw [card_shore_of_nodup _ hl, card_shore_of_nodup _ hr, hlen]
  simp only [List.length_cons, List.length_append]

/-- **Width at least five.**  Every rooted branch decomposition of a cubic
cyclically five-edge-connected graph with at least thirty edges has a cut
with at least five middle vertices. -/
theorem five_le_width (graphData : Data G) (hregular : G.IsRegularOfDegree 3)
    (hcyclic : CyclicallyFiveEdgeConnected G) (hE : 30 ≤ Fintype.card G.edgeSet)
    (d : RootedBranchDecomposition (G := G)) {w : ℕ} (hw : d.WidthAtMost w) : 5 ≤ w := by
  have htotal := card_left_add_right d.leavesNodup d.leavesCover
  have hl : d.left.leafList.Nodup := (List.nodup_cons.mp d.leavesNodup).2.of_append_left
  have hr : d.right.leafList.Nodup := (List.nodup_cons.mp d.leavesNodup).2.of_append_right
  have key : ∀ t : EdgeLeafTree G.edgeSet, t.leafList.Nodup →
      EveryCut (fun S => (edgeShoreMiddleVertices G S).card ≤ w) t → 7 ≤ t.shore.card →
        5 ≤ w := by
    intro t ht hQ h7
    obtain ⟨S, hS, h7', h14⟩ := exists_balanced_cut _ 7 (by norm_num) t ht hQ h7
    have hSc : 7 ≤ (Finset.univ \ S).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
      omega
    have := five_le_middle graphData hregular hcyclic S h7' hSc
    omega
  by_cases hlk : 7 ≤ d.left.shore.card
  · exact key _ hl (everyCut_of_widthAtMost _ hw.2.1) hlk
  · exact key _ hr (everyCut_of_widthAtMost _ hw.2.2) (by omega)

/-- The connected form consumed by the fork-code base. -/
theorem five_le_width_connected (graphData : Data G) (hregular : G.IsRegularOfDegree 3)
    (hcyclic : CyclicallyFiveEdgeConnected G) (hE : 30 ≤ Fintype.card G.edgeSet) {k w : ℕ}
    (d : RootedConnectedBranchDecomposition (G := G) k w) : 5 ≤ w := by
  have htotal := card_left_add_right d.leavesNodup d.leavesCover
  have hl : d.left.leafList.Nodup := (List.nodup_cons.mp d.leavesNodup).2.of_append_left
  have hr : d.right.leafList.Nodup := (List.nodup_cons.mp d.leavesNodup).2.of_append_right
  have key : ∀ t : EdgeLeafTree G.edgeSet, t.leafList.Nodup →
      EveryCut (fun S => S.card < 7 ∨ (edgeShoreMiddleVertices G S).card ≤ w) t →
        7 ≤ t.shore.card → 5 ≤ w := by
    intro t ht hQ h7
    obtain ⟨S, hS, h7', h14⟩ := exists_balanced_cut _ 7 (by norm_num) t ht hQ h7
    have hSc : 7 ≤ (Finset.univ \ S).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
      omega
    have := five_le_middle graphData hregular hcyclic S h7' hSc
    rcases hS with hS | hS <;> omega
  by_cases hlk : 7 ≤ d.left.shore.card
  · exact key _ hl (everyCut_of_geometry _ d.leftGeometry) hlk
  · exact key _ hr (everyCut_of_geometry _ d.rightGeometry) (by omega)

/-- **A least counterexample has at least thirty edges**: it is spherical and
cubic, and each face has length at least five, so it has at least twelve
faces. -/
theorem thirty_le_card_edgeSet (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData) :
    30 ≤ Fintype.card G.edgeSet := by
  have hsph := minimal.spherical
  have hmin := orbitFaceMinimumFive_of_vertexMinimalTaitCounterexample graphData minimal
  have hcount := orbitFacePentagonCount_eq_twelve_add_negativeCurvatureWeight
    graphData.toRotationSystem hsph minimal.facesTwoSided hmin
  have hfaces : 12 ≤ Fintype.card (OrbitFace graphData.toRotationSystem) := by
    have hle := Multiset.count_le_card 5 (orbitFaceBoundaryLengths graphData.toRotationSystem)
    have hcardF : Multiset.card (orbitFaceBoundaryLengths graphData.toRotationSystem) =
        Fintype.card (OrbitFace graphData.toRotationSystem) := by
      simp [orbitFaceBoundaryLengths]
    omega
  have hD3 := graphData.toRotationSystem.card_darts_eq_three_times_card_vertices hsph.cubic
  have hD2 := graphData.toRotationSystem.card_darts_eq_twice_card_edges
  have heuler := hsph.euler
  omega

/-- **Every rooted branch decomposition of a least counterexample has width at
least five.** -/
theorem five_le_width_of_vertexMinimal (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (d : RootedBranchDecomposition (G := G)) {w : ℕ} (hw : d.WidthAtMost w) : 5 ≤ w :=
  five_le_width graphData (graphData.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic)
    (cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample graphData minimal)
    (thirty_le_card_edgeSet graphData minimal) d hw

/-- The connected form. -/
theorem five_le_width_connected_of_vertexMinimal (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData) {k w : ℕ}
    (d : RootedConnectedBranchDecomposition (G := G) k w) : 5 ≤ w :=
  five_le_width_connected graphData
    (graphData.toRotationSystem_isCubic_iff.mp minimal.spherical.cubic)
    (cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample graphData minimal)
    (thirty_le_card_edgeSet graphData minimal) d

end

/-! ## Consequences for the route -/

/-- **At widths at most four the width supply is the whole theorem.**  A raw
width supply at width at most four already excludes least counterexamples; the
audit of the finite closure plays no role. -/
theorem noMinimal_of_rawSupply {w : ℕ} (hw : w ≤ 4)
    (raw : RawBranchDecompositionSupply.{u} w) :
    GoertzelV24SphericalMinimalCounterexampleSelection.NoGraphBackedVertexMinimalTaitCounterexample.{u} := by
  intro V _ _ G _ graphData minimal
  obtain ⟨d, hd⟩ := raw graphData minimal
  have := five_le_width_of_vertexMinimal graphData minimal d hd
  omega

/-- The raw width supply at width at most four is equivalent to the absence of
least counterexamples. -/
theorem rawSupply_iff {w : ℕ} (hw : w ≤ 4) :
    RawBranchDecompositionSupply.{u} w ↔
      GoertzelV24SphericalMinimalCounterexampleSelection.NoGraphBackedVertexMinimalTaitCounterexample.{u} := by
  refine ⟨noMinimal_of_rawSupply hw, fun h => ?_⟩
  intro V _ _ G _ graphData minimal
  exact (h graphData minimal).elim

/-- A connected supply at width at most four likewise excludes least
counterexamples without any finite computation. -/
theorem noMinimal_of_connectedSupply {k w : ℕ} (hw : w ≤ 4)
    (supply : ConnectedDecompositionSupply.{u} k w) :
    GoertzelV24SphericalMinimalCounterexampleSelection.NoGraphBackedVertexMinimalTaitCounterexample.{u} := by
  intro V _ _ G _ graphData minimal
  have := five_le_width_connected_of_vertexMinimal graphData minimal (supply graphData minimal)
  omega

/-- The combinatorial Four-Colour statement follows from a raw width supply at
width at most four alone, with no finite base: at these widths the supply is
the whole theorem. -/
theorem combinatorialFourColorStatement_of_rawSupply {w : ℕ} (hw : w ≤ 4)
    (raw : RawBranchDecompositionSupply.{u} w) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} :=
  (GoertzelV24SphericalGraphPresentation.combinatorialFourColorStatement_iff_spherical.{u}).2
    (GoertzelV24SphericalMinimalCounterexampleSelection.sphericalFourColorStatement_of_no_minimal
      (noMinimal_of_rawSupply hw raw))

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeWidthBarrier
