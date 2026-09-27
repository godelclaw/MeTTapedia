import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundaryEssentialGluing
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationEdgeBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness

/-!
# The rotation-system / multigraph adapter

The gluing lemmas are proved on a bare multigraph -- edges carrying their two
endpoints, reachability as a reflexive-transitive closure.  The map class they
have to speak to is stated on a rotation system, with connectivity read off
`rotationPrimalGraph` and bridgelessness off `edgeDeletedPrimalGraph`.  This
file identifies the two.

The identification is available because a rotation system already *is* a
loopless multigraph: `edge_fiber_two` says every edge identifier carries exactly
two darts, and `no_self_loops` says its two ends differ.  Choosing one dart per
edge gives the endpoint pair, and the other dart of that edge is its `alpha`.

Parallel edges survive the translation.  `rotationPrimalGraph` is a simple graph,
so it forgets multiplicity -- but it forgets it on *both* sides of every
statement here, and `edgeDeletedPrimalGraph` deletes a single edge *identifier*
rather than a whole parallel class, which is exactly what the multigraph's
`StepAvoiding` does.  So no legitimate parallel seam is banned by passing
through it.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationMultigraphAdapter

open GoertzelV24BoundaryEssentialGluing
open GoertzelV24RotationEdgeBridge
open GoertzelV24FaceDualConnectedness

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem V E)

/-- Every edge identifier carries a dart. -/
theorem exists_dart (e : E) : ∃ d : RS.D, RS.edgeOf d = e := by
  classical
  have h := RS.edge_fiber_two e
  have hne : (Finset.univ.filter (fun d => RS.edgeOf d = e)).Nonempty := by
    rw [← Finset.card_pos, h]; omega
  obtain ⟨d, hd⟩ := hne
  exact ⟨d, by simpa using hd⟩

/-- A chosen dart of each edge. -/
noncomputable def someDart (e : E) : RS.D := (exists_dart RS e).choose

@[simp] theorem edgeOf_someDart (e : E) : RS.edgeOf (someDart RS e) = e :=
  (exists_dart RS e).choose_spec

/-- **The two darts of an edge are the chosen one and its flip.** -/
theorem eq_someDart_or (e : E) {d : RS.D} (hd : RS.edgeOf d = e) :
    d = someDart RS e ∨ d = RS.alpha (someDart RS e) := by
  classical
  set s : Finset RS.D := Finset.univ.filter (fun x => RS.edgeOf x = e) with hs
  have hpair : ({someDart RS e, RS.alpha (someDart RS e)} : Finset RS.D) ⊆ s := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx'
    · simp [hs]
    · rw [Finset.mem_singleton] at hx'
      subst hx'
      simp [hs, RS.edge_alpha]
  have hcardpair : ({someDart RS e, RS.alpha (someDart RS e)} : Finset RS.D).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm (RS.alpha_fixfree (someDart RS e))]),
      Finset.card_singleton]
  have heq : ({someDart RS e, RS.alpha (someDart RS e)} : Finset RS.D) = s :=
    Finset.eq_of_subset_of_card_le hpair (by rw [hcardpair, hs, RS.edge_fiber_two e])
  have hmem : d ∈ s := by simp [hs, hd]
  rw [← heq] at hmem
  rcases Finset.mem_insert.1 hmem with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_singleton.1 h)

/-- **A rotation system, read as a multigraph.**  Each edge identifier carries
its two dart endpoints. -/
noncomputable def toMultigraph : Multigraph V E where
  fst e := RS.vertOf (someDart RS e)
  snd e := RS.vertOf (RS.alpha (someDart RS e))

@[simp] theorem toMultigraph_fst (e : E) :
    (toMultigraph RS).fst e = RS.vertOf (someDart RS e) := rfl

@[simp] theorem toMultigraph_snd (e : E) :
    (toMultigraph RS).snd e = RS.vertOf (RS.alpha (someDart RS e)) := rfl

/-- **Steps agree with primal adjacency, edge deletion included.**  A permitted
multigraph step across an edge other than `removed` is exactly an
`edgeDeletedPrimalGraph` adjacency. -/
theorem stepAvoiding_iff_edgeDeleted_adj (removed : E) (u v : V) :
    (toMultigraph RS).StepAvoiding (· = removed) u v ↔
      (edgeDeletedPrimalGraph RS removed).Adj u v := by
  constructor
  · rintro ⟨e, hne, hends⟩
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨someDart RS e, by simpa [edgeOf_someDart] using hne, h1, h2⟩
    · refine ⟨RS.alpha (someDart RS e), ?_, h2, ?_⟩
      · simpa [RS.edge_alpha, edgeOf_someDart] using hne
      · rw [RS.alpha_involutive]; exact h1
  · rintro ⟨d, hne, hu, hv⟩
    set e := RS.edgeOf d with he
    refine ⟨e, by simpa [he] using hne, ?_⟩
    simp only [toMultigraph_fst, toMultigraph_snd]
    rcases eq_someDart_or RS e he.symm with hd | hd
    · exact Or.inl ⟨by rw [← hd]; exact hu, by rw [← hd]; exact hv⟩
    · refine Or.inr ⟨?_, ?_⟩
      · rw [← hv, hd, RS.alpha_involutive]
      · rw [← hu, hd]

/-- Reachability agrees. -/
theorem reachAvoiding_iff_edgeDeleted_reachable (removed : E) (u v : V) :
    (toMultigraph RS).ReachAvoiding removed u v ↔
      (edgeDeletedPrimalGraph RS removed).Reachable u v := by
  constructor
  · intro h
    induction h with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail _ hstep ih =>
        exact ih.trans
          (SimpleGraph.Adj.reachable ((stepAvoiding_iff_edgeDeleted_adj RS removed _ _).1 hstep))
  · rintro ⟨p⟩
    induction p with
    | nil => exact Relation.ReflTransGen.refl
    | cons hadj _ ih =>
        exact Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single
            ((stepAvoiding_iff_edgeDeleted_adj RS removed _ _).2 hadj)) ih

/-- **Bridgelessness agrees.**  A multigraph with no bridge is a rotation system
with no bridging edge identifier, and conversely. -/
theorem bridgeless_iff_edgeBridgeFree :
    (toMultigraph RS).Bridgeless ↔ EdgeBridgeFree RS := by
  constructor
  · intro h dart
    set e := RS.edgeOf dart with he
    have hb := h e
    rw [Multigraph.IsBridge, not_not] at hb
    have hre := (reachAvoiding_iff_edgeDeleted_reachable RS _ _ _).1 hb
    simp only [toMultigraph_fst, toMultigraph_snd] at hre
    rcases eq_someDart_or RS e he.symm with hd | hd
    · rw [hd]; exact hre
    · rw [hd, RS.alpha_involutive]
      exact hre.symm
  · intro h e hbr
    apply hbr
    refine (reachAvoiding_iff_edgeDeleted_reachable RS e _ _).2 ?_
    have := h (someDart RS e)
    rwa [edgeOf_someDart] at this

/-- **Steps agree with primal adjacency.** -/
theorem step_iff_primal_adj (u v : V) :
    (toMultigraph RS).Step u v ↔ (rotationPrimalGraph RS).Adj u v := by
  constructor
  · rintro ⟨e, -, hends⟩
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨someDart RS e, h1, h2⟩
    · refine ⟨RS.alpha (someDart RS e), h2, ?_⟩
      rw [RS.alpha_involutive]; exact h1
  · rintro ⟨d, hu, hv⟩
    set e := RS.edgeOf d with he
    refine ⟨e, fun h => h, ?_⟩
    simp only [toMultigraph_fst, toMultigraph_snd]
    rcases eq_someDart_or RS e he.symm with hd | hd
    · exact Or.inl ⟨by rw [← hd]; exact hu, by rw [← hd]; exact hv⟩
    · refine Or.inr ⟨?_, ?_⟩
      · rw [← hv, hd, RS.alpha_involutive]
      · rw [← hu, hd]

theorem reach_iff_primal_reachable (u v : V) :
    (toMultigraph RS).Reach u v ↔ (rotationPrimalGraph RS).Reachable u v := by
  constructor
  · intro h
    induction h with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail _ hstep ih =>
        exact ih.trans (SimpleGraph.Adj.reachable ((step_iff_primal_adj RS _ _).1 hstep))
  · rintro ⟨p⟩
    induction p with
    | nil => exact Relation.ReflTransGen.refl
    | cons hadj _ ih =>
        exact Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single ((step_iff_primal_adj RS _ _).2 hadj)) ih

/-- **Connectivity agrees**, given a vertex to be connected from. -/
theorem primalConnected_of_connected [Nonempty V]
    (h : (toMultigraph RS).Connected) : (rotationPrimalGraph RS).Connected := by
  exact ⟨fun u v => (reach_iff_primal_reachable RS u v).1 (h u v)⟩

theorem connected_of_primalConnected (h : (rotationPrimalGraph RS).Connected) :
    (toMultigraph RS).Connected :=
  fun u v => (reach_iff_primal_reachable RS u v).2 (h u v)

/-! ## Vertex accounting for a seam glue -/

section VertexCount

variable {W : Type*} [Fintype W]

/-- The glue adds no vertices: the composite carries exactly the two sides'. -/
theorem card_vertices_glue : Fintype.card (V ⊕ W) = Fintype.card V + Fintype.card W := by
  simp

/-- **Strict decrease.**  If the original instance is the two retained sides
together with a nonempty deleted slab, the glued instance is strictly smaller.

The slab's vertex count enters as an explicit number: no vertex is created by
the seam, so the whole decrease is the slab. -/
theorem card_vertices_lt_of_slab_nonempty {Vorig : Type*} [Fintype Vorig] {slab : ℕ}
    (hslab : 0 < slab)
    (horig : Fintype.card Vorig = Fintype.card V + Fintype.card W + slab) :
    Fintype.card (V ⊕ W) < Fintype.card Vorig := by
  rw [card_vertices_glue]
  omega

end VertexCount

end GoertzelV24RotationMultigraphAdapter

end Mettapedia.GraphTheory.FourColor
