import Mettapedia.GraphTheory.RelationExtras
import Mettapedia.GraphTheory.FourColor.RotationDiskData

namespace Mettapedia.GraphTheory.FourColor

open Finset Relation

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

namespace RotationDiskData

/-- Internal faces as a subtype, so dual-graph paths carry their face-membership
proofs with them. -/
abbrev Face (G : RotationDiskData V E) :=
  {f : Finset E // f ∈ G.rotation.internalFaces}

/-- Acyclicity for a chosen set of dual-tree edges. Adding any listed edge must
not connect two distinct incident internal faces that were already connected by
the remaining listed edges. -/
def IsAcyclic (G : RotationDiskData V E) (tree_edges : Finset E) : Prop :=
  ∀ e ∈ tree_edges, ∀ (f g : G.Face),
    f ≠ g →
    e ∈ f.1 → e ∈ g.1 →
    ¬ ReflTransGen
        (fun f' g' =>
          ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ f'.1 ∧ e' ∈ g'.1) f g

/-- A maximal acyclic set: every interior edge outside the selected set would
break acyclicity if inserted. -/
def IsMaximalAcyclic (G : RotationDiskData V E) (tree_edges : Finset E) : Prop :=
  G.IsAcyclic tree_edges ∧
    ∀ e, e ∉ G.rotation.boundaryEdges →
      e ∉ tree_edges →
      ¬ G.IsAcyclic (insert e tree_edges)

/-- Explicit modern replacement for the old hidden E2 surface: every interior
edge has exactly two incident internal faces, represented as a left/right pair
with a completeness principle. -/
structure InteriorEdgeFacePairData (G : RotationDiskData V E) where
  left : ∀ e : E, e ∉ G.rotation.boundaryEdges → G.Face
  right : ∀ e : E, e ∉ G.rotation.boundaryEdges → G.Face
  left_ne_right :
    ∀ (e : E) (he : e ∉ G.rotation.boundaryEdges), left e he ≠ right e he
  edge_mem_left :
    ∀ (e : E) (he : e ∉ G.rotation.boundaryEdges), e ∈ (left e he).1
  edge_mem_right :
    ∀ (e : E) (he : e ∉ G.rotation.boundaryEdges), e ∈ (right e he).1
  complete :
    ∀ {e : E} (he : e ∉ G.rotation.boundaryEdges) (f : G.Face),
      e ∈ f.1 → f = left e he ∨ f = right e he

namespace InteriorEdgeFacePairData

/-- The two faces supplied for an interior edge are adjacent in the interior dual
graph. -/
theorem dualAdjacent_left_right {G : RotationDiskData V E}
    (data : G.InteriorEdgeFacePairData)
    {e : E} (he : e ∉ G.rotation.boundaryEdges) :
    G.dualAdjacent (data.left e he).1 (data.right e he).1 := by
  refine ⟨(data.left e he).2, (data.right e he).2, ?_, ?_⟩
  · intro hfaces
    exact data.left_ne_right e he (Subtype.ext hfaces)
  · exact ⟨e, he, data.edge_mem_left e he, data.edge_mem_right e he⟩

/-- If an interior edge has only two incident internal faces, then the face on
the other side of that edge from a fixed face is unique. -/
theorem other_face_unique {G : RotationDiskData V E}
    (data : G.InteriorEdgeFacePairData)
    {e : E} (he : e ∉ G.rotation.boundaryEdges)
    {x y z : G.Face}
    (hxy : x ≠ y) (hxz : x ≠ z)
    (hx : e ∈ x.1) (hy : e ∈ y.1) (hz : e ∈ z.1) :
    y = z := by
  rcases data.complete he x hx with hxL | hxR
  · rcases data.complete he y hy with hyL | hyR
    · exact False.elim (hxy (hxL.trans hyL.symm))
    · rcases data.complete he z hz with hzL | hzR
      · exact False.elim (hxz (hxL.trans hzL.symm))
      · exact hyR.trans hzR.symm
  · rcases data.complete he y hy with hyL | hyR
    · rcases data.complete he z hz with hzL | hzR
      · exact hyL.trans hzL.symm
      · exact False.elim (hxz (hxR.trans hzR.symm))
    · exact False.elim (hxy (hxR.trans hyR.symm))

end InteriorEdgeFacePairData

/-- Project a dual path over internal-face subtypes to the underlying face edge
sets, after removing the inserted edge from the relation. -/
theorem transport_face_path_to_finset {G : RotationDiskData V E}
    {tree_edges : Finset E} {f' g' : G.Face} {extra : E}
    (h_path : ReflTransGen
      (fun (x y : G.Face) =>
        ∃ e' ∈ insert extra tree_edges, e' ≠ extra ∧ e' ∈ x.1 ∧ e' ∈ y.1)
      f' g') :
    ReflTransGen
      (fun (x y : Finset E) =>
        ∃ e' ∈ tree_edges, e' ≠ extra ∧ e' ∈ x ∧ e' ∈ y)
      f'.1 g'.1 := by
  induction h_path using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head h_step _h_rest ih =>
      rcases h_step with ⟨e', he'_ins, hne, hx, hy⟩
      have he'_tree : e' ∈ tree_edges := by
        rcases Finset.mem_insert.mp he'_ins with rfl | hmem
        · exact False.elim (hne rfl)
        · exact hmem
      exact .head ⟨e', he'_tree, hne, hx, hy⟩ ih

/-- Every finite set of interior edges contains a maximal acyclic subset. This
ports the finiteness/greedy part of the old dual-forest construction without
assuming the old planar E2 surface. -/
theorem exists_maximal_acyclic (G : RotationDiskData V E) :
    ∃ tree_edges : Finset E,
      (∀ e ∈ tree_edges, e ∉ G.rotation.boundaryEdges) ∧
      G.IsMaximalAcyclic tree_edges := by
  classical
  let interior_edges : Finset E :=
    Finset.univ.filter (fun e => e ∉ G.rotation.boundaryEdges)
  let candidates : Finset (Finset E) :=
    (interior_edges.powerset).filter (fun T => G.IsAcyclic T)
  have hCand_nonempty : candidates.Nonempty := by
    have hEmptyAcyclic : G.IsAcyclic ∅ := by
      intro e he
      simp at he
    have hEmptyIn : (∅ : Finset E) ⊆ interior_edges := by
      intro e he
      simp at he
    exact ⟨∅, by simp [candidates, hEmptyAcyclic, hEmptyIn]⟩
  have hcard_nonempty : (candidates.image Finset.card).Nonempty :=
    Finset.Nonempty.image hCand_nonempty _
  let maxCard := (candidates.image Finset.card).max' hcard_nonempty
  obtain ⟨T, hT_mem, hT_card⟩ : ∃ T ∈ candidates, T.card = maxCard := by
    have hmax_mem : maxCard ∈ candidates.image Finset.card :=
      Finset.max'_mem _ hcard_nonempty
    simpa [Finset.mem_image] using hmax_mem
  have hT_sub : T ⊆ interior_edges := by
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hT_mem).1
  have hT_acyclic : G.IsAcyclic T := (Finset.mem_filter.mp hT_mem).2
  have hT_interior : ∀ e ∈ T, e ∉ G.rotation.boundaryEdges := by
    intro e heT
    have : e ∈ interior_edges := hT_sub heT
    simpa [interior_edges] using this
  have hT_max :
      ∀ e, e ∉ G.rotation.boundaryEdges → e ∉ T →
        ¬ G.IsAcyclic (insert e T) := by
    intro e he_int he_notinT hInsAcyclic
    have hIns_sub : insert e T ⊆ interior_edges := by
      apply Finset.insert_subset
      · simpa [interior_edges] using he_int
      · exact hT_sub
    have hIns_mem : insert e T ∈ candidates := by
      simp [candidates, hIns_sub, hInsAcyclic]
    have hIns_card_mem : (insert e T).card ∈ candidates.image Finset.card :=
      Finset.mem_image_of_mem _ hIns_mem
    have h_gt : (insert e T).card = T.card + 1 :=
      Finset.card_insert_of_notMem he_notinT
    rw [hT_card] at h_gt
    have h_gt' : (insert e T).card > maxCard := by omega
    have h_le : (insert e T).card ≤ maxCard :=
      Finset.le_max' _ _ hIns_card_mem
    omega
  exact ⟨T, hT_interior, ⟨hT_acyclic, hT_max⟩⟩

/-- Maximal acyclic selected edges satisfy the spanning-forest dichotomy once
the modern E2 interface supplies the two incident faces of every interior edge. -/
theorem maximal_acyclic_dichotomy (G : RotationDiskData V E)
    (facePairs : G.InteriorEdgeFacePairData)
    (tree_edges : Finset E)
    (_h_interior : ∀ e ∈ tree_edges, e ∉ G.rotation.boundaryEdges)
    (h_maximal : G.IsMaximalAcyclic tree_edges) :
    ∀ e, e ∉ G.rotation.boundaryEdges →
      e ∈ tree_edges ∨
        (∃ f g, G.dualAdjacent f g ∧ e ∈ f ∧ e ∈ g ∧
          ReflTransGen
            (fun f' g' =>
              ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ f' ∧ e' ∈ g') f g) := by
  classical
  intro e he
  by_cases he_tree : e ∈ tree_edges
  · exact Or.inl he_tree
  · right
    have h_not_acyclic : ¬ G.IsAcyclic (insert e tree_edges) :=
      h_maximal.2 e he he_tree
    unfold IsAcyclic at h_not_acyclic
    push_neg at h_not_acyclic
    rcases h_not_acyclic with
      ⟨eWitness, heWitness_insert, f, g, hfg_ne, heWitness_f, heWitness_g, h_path⟩
    rcases Finset.mem_insert.mp heWitness_insert with heWitness_eq_e | heWitness_tree
    · subst eWitness
      have h_path_tree :
          ReflTransGen
            (fun f' g' =>
              ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ f' ∧ e' ∈ g') f.1 g.1 :=
        transport_face_path_to_finset h_path
      refine ⟨f.1, g.1, ?_, heWitness_f, heWitness_g, h_path_tree⟩
      exact ⟨f.2, g.2, fun hfg => hfg_ne (Subtype.ext hfg),
        ⟨e, he, heWitness_f, heWitness_g⟩⟩
    · let R : G.Face → G.Face → Prop :=
        fun x y =>
          ∃ e' ∈ tree_edges, e' ≠ eWitness ∧ e' ∈ x.1 ∧ e' ∈ y.1
      let S : G.Face → G.Face → Prop :=
        fun x y => e ∈ x.1 ∧ e ∈ y.1
      have h_path_RS : ReflTransGen (fun x y => R x y ∨ S x y) f g := by
        refine ReflTransGen.mono ?_ h_path
        intro x y hstep
        rcases hstep with ⟨e', he'_insert, hne, hx, hy⟩
        rcases Finset.mem_insert.mp he'_insert with rfl | he'_tree
        · exact Or.inr ⟨hx, hy⟩
        · exact Or.inl ⟨e', he'_tree, hne, hx, hy⟩
      have h_not_R : ¬ ReflTransGen R f g := by
        intro hR
        exact h_maximal.1 eWitness heWitness_tree f g hfg_ne heWitness_f heWitness_g hR
      rcases Mettapedia.GraphTheory.ReflTransGen.exists_new_step_of_not_left
          h_path_RS h_not_R with
        ⟨x, y, h_f_x, h_xy, hxy_ne, _h_y_g⟩

      have h_sym_R : Symmetric R := by
        intro a b h
        rcases h with ⟨e', he', hne, ha, hb⟩
        exact ⟨e', he', hne, hb, ha⟩
      have h_sym_RS : Symmetric (fun x y => R x y ∨ S x y) := by
        intro a b h
        rcases h with hR | hS
        · exact Or.inl (h_sym_R hR)
        · exact Or.inr ⟨hS.2, hS.1⟩
      have h_path_rev : ReflTransGen (fun x y => R x y ∨ S x y) g f :=
        Mettapedia.GraphTheory.ReflTransGen.reverse_of_symmetric h_sym_RS h_path_RS
      have h_not_R_rev : ¬ ReflTransGen R g f := by
        intro hR
        exact h_not_R
          (Mettapedia.GraphTheory.ReflTransGen.reverse_of_symmetric h_sym_R hR)
      rcases Mettapedia.GraphTheory.ReflTransGen.exists_new_step_of_not_left
          h_path_rev h_not_R_rev with
        ⟨u, _v, h_g_u, h_uv, _huv_ne, _h_v_f⟩

      have h_x_ne_u : x ≠ u := by
        intro hxu
        have h_u_g : ReflTransGen R u g :=
          Mettapedia.GraphTheory.ReflTransGen.reverse_of_symmetric h_sym_R h_g_u
        have h_x_g : ReflTransGen R x g := by
          simpa [hxu] using h_u_g
        exact h_not_R (Relation.ReflTransGen.trans h_f_x h_x_g)
      have h_y_eq_u : y = u :=
        facePairs.other_face_unique he hxy_ne h_x_ne_u h_xy.1 h_xy.2 h_uv.1

      have h_x_f : ReflTransGen R x f :=
        Mettapedia.GraphTheory.ReflTransGen.reverse_of_symmetric h_sym_R h_f_x
      let TRel : G.Face → G.Face → Prop :=
        fun a b => ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ a.1 ∧ e' ∈ b.1
      have hR_to_TRel : ∀ a b, R a b → TRel a b := by
        intro a b hR
        rcases hR with ⟨e', he', _hneWitness, ha, hb⟩
        exact ⟨e', he', by intro heq; exact he_tree (heq ▸ he'), ha, hb⟩
      have h_x_f_T : ReflTransGen TRel x f :=
        Relation.ReflTransGen.mono hR_to_TRel h_x_f
      have h_f_g_T : ReflTransGen TRel f g := by
        apply Relation.ReflTransGen.single
        exact ⟨eWitness, heWitness_tree,
          by
            intro h
            exact he_tree (h ▸ heWitness_tree),
          heWitness_f, heWitness_g⟩
      have h_g_y : ReflTransGen R g y := by
        simpa [h_y_eq_u] using h_g_u
      have h_g_y_T : ReflTransGen TRel g y :=
        Relation.ReflTransGen.mono hR_to_TRel h_g_y
      have h_x_y : ReflTransGen TRel x y :=
        Relation.ReflTransGen.trans h_x_f_T
          (Relation.ReflTransGen.trans h_f_g_T h_g_y_T)
      have h_x_y_fin :
          ReflTransGen
            (fun f' g' =>
              ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ f' ∧ e' ∈ g')
            x.1 y.1 := by
        apply Mettapedia.GraphTheory.ReflTransGen.map_rel Subtype.val ?_ h_x_y
        intro a b hT
        exact hT
      refine ⟨x.1, y.1, ?_, h_xy.1, h_xy.2, h_x_y_fin⟩
      exact ⟨x.2, y.2, fun hxy => hxy_ne (Subtype.ext hxy),
        ⟨e, he, h_xy.1, h_xy.2⟩⟩

/-- A modern spanning-forest witness follows from maximal acyclicity plus the
explicit two-incident-faces interface. -/
theorem exists_spanning_forest_of_interiorEdgeFacePairData
    (G : RotationDiskData V E) (facePairs : G.InteriorEdgeFacePairData) :
    ∃ _ : G.SpanningForest, True := by
  rcases G.exists_maximal_acyclic with ⟨tree_edges, h_interior, h_maximal⟩
  exact ⟨{
    tree_edges := tree_edges
    tree_edges_interior := h_interior
    dichotomy := G.maximal_acyclic_dichotomy facePairs tree_edges h_interior h_maximal
  }, trivial⟩

end RotationDiskData

end Mettapedia.GraphTheory.FourColor
