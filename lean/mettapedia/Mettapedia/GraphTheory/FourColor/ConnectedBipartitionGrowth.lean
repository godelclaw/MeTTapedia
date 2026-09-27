import Mettapedia.GraphTheory.FourColor.VertexSeparatorBond
import Mathlib.Data.Finset.Max

/-!
# Growing a connected side while keeping its complement connected

In a finite graph without a cut vertex, any two nested connected vertex
sets with connected complements admit an intermediate step adding just one
vertex. The new vertex is adjacent to the smaller set, and both new sides
remain connected.

This is the connected-bipartition property underlying st-numberings. Here
we prove the relative version directly: among candidate vertices, minimize
the side obtained by filling every complementary component except a fixed
root component. Any unwanted filled component supplies a strictly better
candidate, using connectivity after deleting the original candidate.

There is no planar embedding or colouring assumption in this result.
-/

namespace Mettapedia.GraphTheory.FourColor.ConnectedBipartitionGrowth

open VertexSeparatorBond

variable {V : Type*} (G : SimpleGraph V)

theorem connected_insert_of_adj {S : Set V} (hS : (G.induce S).Connected)
    {y a : V} (ha : a ∈ S) (hy : G.Adj y a) :
    (G.induce (insert y S)).Connected := by
  apply connected_of_walks G (Set.mem_insert y S)
  intro v hv
  rcases hv with rfl | hv
  · exact ⟨.nil, by simp⟩
  · obtain ⟨p, hp⟩ := exists_walk_in G hS ha hv
    refine ⟨p.cons hy, ?_⟩
    intro x hx
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (hp x hx)

theorem exists_adjacent_outside {S R : Set V}
    (hS : (G.induce S).Connected) (hR : (G.induce R).Connected)
    (hSR : S ⊂ R) :
    ∃ y ∈ R, y ∉ S ∧ ∃ a ∈ S, G.Adj y a := by
  obtain ⟨a⟩ := hS.nonempty
  obtain ⟨x, hxR, hxS⟩ := Set.exists_of_ssubset hSR
  obtain ⟨p, hp⟩ := exists_walk_in G hR hxR (hSR.subset a.property)
  obtain ⟨d, hd, hds, hdt⟩ := p.exists_boundary_dart Sᶜ hxS (not_not.mpr a.property)
  exact ⟨d.fst, hp _ (p.dart_fst_mem_support_of_mem_darts hd), hds,
    d.snd, by simpa using hdt, d.adj⟩

section Finite

variable [Fintype V]

/-- One vertex can be transferred between the sides of a connected
bipartition, inside a prescribed larger connected side. -/
theorem exists_connected_insert
    (hdelete : ∀ v : V, (G.induce ({v} : Set V)ᶜ).Connected)
    {S R : Set V} (hS : (G.induce S).Connected)
    (hSc : (G.induce Sᶜ).Connected) (hR : (G.induce R).Connected)
    (hRc : (G.induce Rᶜ).Connected) (hSR : S ⊂ R) :
    ∃ y ∈ R, y ∉ S ∧ (∃ a ∈ S, G.Adj y a) ∧
      (G.induce (insert y S)).Connected ∧
      (G.induce (insert y S)ᶜ).Connected := by
  classical
  obtain ⟨b⟩ := hRc.nonempty
  let C : V → Set V := fun y => flood G (insert y S)ᶜ {b.val}
  let candidates : Finset V := Finset.univ.filter fun y =>
    y ∈ R ∧ y ∉ S ∧ ∃ a ∈ S, G.Adj y a
  have hcandidates : candidates.Nonempty := by
    obtain ⟨y, hyR, hyS, ha⟩ := exists_adjacent_outside G hS hR hSR
    exact ⟨y, by simp [candidates, hyR, hyS, ha]⟩
  have hCsub (y : V) : C y ⊆ (insert y S)ᶜ := flood_subset G _ _
  have hbase (y : V) (hyR : y ∈ R) : b.val ∈ (insert y S)ᶜ := by
    rintro (h | h)
    · exact b.property (h ▸ hyR)
    · exact b.property (hSR.subset h)
  have hroot (y : V) (hyR : y ∈ R) : b.val ∈ C y :=
    mem_flood G _ _ (hbase y hyR) (by simp)
  have houtside (y : V) (hyR : y ∈ R) : Rᶜ ⊆ C y := by
    intro v hv
    obtain ⟨p, hp⟩ := exists_walk_in G hRc b.property hv
    refine ⟨b.val, by simp, p, ?_⟩
    intro x hx hi
    rcases hi with h | h
    · exact hp x hx (h ▸ hyR)
    · exact hp x hx (hSR.subset h)
  obtain ⟨y, hy, hmin⟩ :=
    candidates.exists_min_image (fun y => (C y)ᶜ.toFinset.card) hcandidates
  obtain ⟨hyR, hyS, a, ha, hya⟩ := (Finset.mem_filter.mp hy).2
  have hyC : y ∉ C y := fun h => hCsub y h (Set.mem_insert _ _)
  have hfilled : (C y)ᶜ ⊆ insert y S := by
    intro x hx
    by_contra hxS
    have hxy : x ≠ y := fun h => hxS (Or.inl h)
    have hay : a ≠ y := fun h => hyS (h ▸ ha)
    obtain ⟨p, hp⟩ := exists_walk_in G (hdelete y)
      (by simpa using hxy) (by simpa using hay)
    obtain ⟨d, hd, hds, hdt⟩ := p.exists_boundary_dart ((C y)ᶜ \ S)
      ⟨hx, fun h => hxS (Or.inr h)⟩ (by simp [ha])
    have hdy : d.fst ≠ y := by
      simpa using hp _ (p.dart_fst_mem_support_of_mem_darts hd)
    have hdty : d.snd ≠ y := by
      simpa using hp _ (p.dart_snd_mem_support_of_mem_darts hd)
    have hdtS : d.snd ∈ S := by
      by_contra hn
      have hdtC : d.snd ∈ C y := by
        by_contra hc
        exact hdt ⟨hc, hn⟩
      exact hds.1 (flood_adj G hdtC d.adj.symm (by simpa using And.intro hdy hds.2))
    have hdR : d.fst ∈ R := by
      by_contra hn
      exact hds.1 (houtside y hyR hn)
    have hdcand : d.fst ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hdR, hds.2, d.snd, hdtS, d.adj⟩
    have hinc : C y ⊆ C d.fst := by
      rintro v ⟨z, hz, q, hq⟩
      refine ⟨z, hz, q, ?_⟩
      intro t ht hi
      rcases hi with h | h
      · exact hds.1 (h ▸ support_subset_flood G hz q hq t ht)
      · exact hq t ht (Or.inr h)
    have hyNew : y ∈ C d.fst := by
      obtain ⟨q, hq⟩ := exists_walk_in G hSc
        (fun h => b.property (hSR.subset h)) hyS
      obtain ⟨e, he, hes, het⟩ := q.exists_boundary_dart (C y) (hroot y hyR) hyC
      have hetS : e.snd ∉ S := hq _ (q.dart_snd_mem_support_of_mem_darts he)
      have hety : e.snd = y := by
        by_contra hn
        exact het (flood_adj G hes e.adj (by simpa using And.intro hn hetS))
      have hadj : G.Adj e.fst y := hety ▸ e.adj
      exact flood_adj G (hinc hes) hadj (by simpa using And.intro hdy.symm hyS)
    have hstrict : (C d.fst)ᶜ.toFinset ⊂ (C y)ᶜ.toFinset := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · intro z hz
        simp only [Set.mem_toFinset, Set.mem_compl_iff] at hz ⊢
        exact fun h => hz (hinc h)
      · intro heq
        have hmem : y ∈ (C d.fst)ᶜ.toFinset := by
          rw [heq]
          simpa using hyC
        exact (by simpa using hmem : y ∉ C d.fst) hyNew
    exact (not_lt_of_ge (hmin d.fst hdcand)) (Finset.card_lt_card hstrict)
  have hCeq : C y = (insert y S)ᶜ := by
    apply Set.Subset.antisymm (hCsub y)
    intro v hv
    by_contra hn
    exact hv (hfilled hn)
  refine ⟨y, hyR, hyS, ⟨a, ha, hya⟩, connected_insert_of_adj G hS ha hya, ?_⟩
  rw [← hCeq]
  exact flood_singleton_connected G (hbase y hyR)

end Finite

end Mettapedia.GraphTheory.FourColor.ConnectedBipartitionGrowth
