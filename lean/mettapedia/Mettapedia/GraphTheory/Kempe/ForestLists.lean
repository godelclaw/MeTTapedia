import Mettapedia.GraphTheory.Kempe.ForestFibre
import Mettapedia.GraphTheory.Kempe.ListPropagation

/-!
# Reconstructing list colourings from supported forest lists

On a finite forest, nonempty lists with support across each edge reconstruct
an actual colouring. The same result applies when a fixed set breaks all
cycles and its lists have at most one colour. The fixed colours remain joint
choices throughout propagation and reconstruction.
-/

namespace SimpleGraph.ColoringListPropagation

universe u w

variable {V : Type u} {A : Type w}

/-- Every retained colour has a compatible colour across each incident edge. -/
def Supported (G : SimpleGraph V) (L : V → Finset A) : Prop :=
  ∀ x y, G.Adj x y → ∀ a ∈ L x, ∃ b ∈ L y, a ≠ b

/-- Leaf induction turns local support into a common colouring witness. -/
theorem forest_colouring [Fintype V] (G : SimpleGraph V) (L : V → Finset A)
    (acyclic : G.IsAcyclic) (nonempty : ∀ x, (L x).Nonempty)
    (supported : Supported G L) : ∃ C : G.Coloring A, ∀ x, C x ∈ L x := by
  classical
  suffices ∀ n : ℕ, ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → G.IsAcyclic → ∀ (L : V → Finset A),
      (∀ x, (L x).Nonempty) → Supported G L →
      ∃ C : G.Coloring A, ∀ x, C x ∈ L x from
    this _ V G rfl acyclic L nonempty supported
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V inst G count acyclic L nonempty supported
    by_cases inhabited : Nonempty V
    · have := inhabited
      obtain ⟨v,leaf⟩ := KempeForestFibre.exists_leaf acyclic
      let X : Set V := ({v} : Set V)ᶜ
      let H := G.induce X
      have shorter : Fintype.card X < n := by
        rw [← count]
        exact Fintype.card_subtype_lt (x := v) (by simp [X])
      obtain ⟨E,fit⟩ := ih (Fintype.card X) shorter X H rfl (acyclic.induce X)
        (fun x => L x) (fun x => nonempty x)
        (fun x y h a ha => supported x y h a ha)
      have extend : ∃ z ∈ L v, ∀ x : X, G.Adj v x → z ≠ E x := by
        by_cases edge : ∃ x : X, G.Adj v x
        · obtain ⟨x,hx⟩ := edge
          obtain ⟨z,hz,hne⟩ := supported x v hx.symm (E x) (fit x)
          refine ⟨z,hz,fun y hy => ?_⟩
          have same : y = x := Subtype.ext (leaf y x hy hx)
          simpa only [same] using hne.symm
        · obtain ⟨z,hz⟩ := nonempty v
          exact ⟨z,hz,fun x hx => (edge ⟨x,hx⟩).elim⟩
      obtain ⟨z,hz,good⟩ := extend
      let C : G.Coloring A := .mk (fun x => if hx : x = v then z else E ⟨x,hx⟩) (by
        intro x y hxy
        by_cases hx : x = v <;> by_cases hy : y = v
        · exact (hxy.ne (hx.trans hy.symm)).elim
        · subst x; simpa [hy] using good ⟨y,hy⟩ hxy
        · subst y; simpa [hx] using (good ⟨x,hx⟩ hxy.symm).symm
        · simpa [hx,hy] using E.valid (show H.Adj ⟨x,hx⟩ ⟨y,hy⟩ from hxy))
      refine ⟨C,fun x => ?_⟩
      change (if hx : x = v then z else E ⟨x,hx⟩) ∈ L x
      by_cases hx : x = v
      · subst x; simpa using hz
      · simpa only [dite_eq_right hx] using fit ⟨x,hx⟩
    · exact ⟨.mk (fun x => (inhabited ⟨x⟩).elim)
        (fun {x} _ _ => (inhabited ⟨x⟩).elim), fun x => (inhabited ⟨x⟩).elim⟩

/-- A jointly pinned cycle-breaking set makes support sufficient on the
whole graph. No bound on the number of anchors is assumed. -/
theorem anchored_colouring [Fintype V] (G : SimpleGraph V) (L : V → Finset A)
    (K : Set V) (acyclic : (G.induce Kᶜ).IsAcyclic)
    (pinned : ∀ x ∈ K, (L x : Set A).Subsingleton)
    (nonempty : ∀ x, (L x).Nonempty) (supported : Supported G L) :
    ∃ C : G.Coloring A, ∀ x, C x ∈ L x := by
  classical
  obtain ⟨E,fit⟩ := forest_colouring (G.induce Kᶜ) (fun x => L x) acyclic
    (fun x => nonempty x) (fun x y h a ha => supported x y h a ha)
  choose chosen member using nonempty
  have avoid (x y : V) (hy : y ∈ K) (a : A) (ha : a ∈ L x) (edge : G.Adj x y) :
      a ≠ chosen y := by
    obtain ⟨b,hb,hn⟩ := supported x y edge a ha
    exact (pinned y hy hb (member y)) ▸ hn
  let C : G.Coloring A := .mk (fun x => if hx : x ∈ K then chosen x else E ⟨x,hx⟩) (by
    intro x y hxy
    by_cases hx : x ∈ K <;> by_cases hy : y ∈ K
    · simpa [hx,hy] using avoid x y hy (chosen x) (member x) hxy
    · simpa [hx,hy] using (avoid y x hx (E ⟨y,hy⟩) (fit _) hxy.symm).symm
    · simpa [hx,hy] using avoid x y hy (E ⟨x,hx⟩) (fit _) hxy
    · simpa [hx,hy] using E.valid (show (G.induce Kᶜ).Adj ⟨x,hx⟩ ⟨y,hy⟩ from hxy))
  refine ⟨C,fun x => ?_⟩
  change (if hx : x ∈ K then chosen x else E ⟨x,hx⟩) ∈ L x
  by_cases hx : x ∈ K
  · simpa only [dite_eq_left hx] using member x
  · simpa only [dite_eq_right hx] using fit ⟨x,hx⟩

theorem trim_subset [DecidableEq V] [DecidableEq A]
    (L : V → Finset A) (e : V × V) (x : V) : trim L e x ⊆ L x := by
  by_cases hx : x = e.2
  · subst x
    simp only [trim, Function.update_self]
    exact Finset.filter_subset _ _
  · simp only [trim, Function.update_of_ne hx, Finset.Subset.refl]

theorem run_subset [DecidableEq V] [DecidableEq A]
    (L : V → Finset A) (es : List (V × V)) (x : V) : run L es x ⊆ L x := by
  induction es generalizing L with
  | nil => exact Finset.Subset.refl _
  | cons e es ih => exact (ih (trim L e)).trans (trim_subset L e x)

/-- Once propagation has local support, nonempty residual lists are an
exact extension test for a jointly pinned forest complement. -/
theorem extension_iff_nonempty [Fintype V] [DecidableEq V] [DecidableEq A]
    (G : SimpleGraph V) (L : V → Finset A) (K : Set V)
    (acyclic : (G.induce Kᶜ).IsAcyclic)
    (pinned : ∀ x ∈ K, (L x : Set A).Subsingleton)
    (es : List (V × V)) (edges : ∀ e ∈ es, G.Adj e.1 e.2)
    (supported : Supported G (run L es)) :
    (∃ C : G.Coloring A, ∀ x, C x ∈ L x) ↔ ∀ x, (run L es x).Nonempty := by
  constructor
  · rintro ⟨C,fit⟩ x
    exact ⟨C x,run_sound C L fit es edges x⟩
  · intro nonempty
    obtain ⟨C,fit⟩ := anchored_colouring G (run L es) K acyclic
      (fun x hx _ ha _ hb => pinned x hx (run_subset L es x ha)
        (run_subset L es x hb)) nonempty supported
    exact ⟨C,fun x => run_subset L es x (fit x)⟩

end SimpleGraph.ColoringListPropagation
