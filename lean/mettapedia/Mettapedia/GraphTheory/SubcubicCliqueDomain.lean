import Mettapedia.GraphTheory.SubcubicThreeColouring

/-!
# The four-clique exception in a connected subcubic graph

Every vertex of a four-clique has already spent its three neighbours
inside that clique. Connectivity then forces the entire graph into the
four vertices. A larger connected subcubic graph therefore satisfies
the clique-free domain of the uniform three-colouring theorem.
-/

namespace Mettapedia.GraphTheory.SubcubicCliqueDomain

open SimpleGraph Finset
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem cliqueFree_of_connected_card_gt
    (hdeg : ∀ v, G.degree v ≤ 3) (hconn : G.Connected) (hcard : 4 < Fintype.card V) :
    G.CliqueFree 4 := by
  classical
  intro s hs
  have hclosed : ∀ x, x ∈ s → ∀ y, G.Adj x y → y ∈ s := by
    intro x hx
    have he : (s.erase x).card = 3 := by rw [Finset.card_erase_of_mem hx, hs.card_eq]
    have hsub : s.erase x ⊆ G.neighborFinset x := by
      intro y hy
      have hyx := Finset.mem_erase.mp hy
      simpa using hs.isClique hx hyx.2 hyx.1.symm
    have hle : (G.neighborFinset x).card ≤ (s.erase x).card := by
      rw [he, SimpleGraph.card_neighborFinset_eq_degree]
      exact hdeg x
    have heq : s.erase x = G.neighborFinset x := Finset.eq_of_subset_of_card_le hsub hle
    intro y hxy
    have hyn : y ∈ G.neighborFinset x := by simpa using hxy
    rw [← heq] at hyn
    exact Finset.mem_of_mem_erase hyn
  have propagate : ∀ {x y : V}, G.Reachable x y → x ∈ s → y ∈ s := by
    intro x y hxy
    obtain ⟨p⟩ := hxy
    induction p with
    | nil => exact fun hx => hx
    | @cons x z y hxz p ih => exact fun hx => ih (hclosed x hx z hxz)
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < s.card by rw [hs.card_eq]; decide)
  have hsub : (Finset.univ : Finset V) ⊆ s := by
    intro y _
    exact propagate (hconn x y) hx
  have hbound := Finset.card_le_card hsub
  simp only [Finset.card_univ, hs.card_eq] at hbound
  omega

theorem colourable_of_connected_card_gt
    (hdeg : ∀ v, G.degree v ≤ 3) (hconn : G.Connected) (hcard : 4 < Fintype.card V) :
    G.Colorable 3 :=
  SubcubicThreeColouring.colourable G hdeg (cliqueFree_of_connected_card_gt G hdeg hconn hcard)

end
end Mettapedia.GraphTheory.SubcubicCliqueDomain
