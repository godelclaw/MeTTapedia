import Mettapedia.GraphTheory.Kempe.Symm

/-!
# Decomposing a proper partial colour transposition

If two proper colourings differ pointwise by either the identity or one
fixed transposition, the changed set is a union of actual bichromatic
components. On a finite graph, switching those components gives a Kempe
history. No planarity, degree bound, or fixed palette size is required.
-/

namespace SimpleGraph.Coloring

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq α]
variable (C D : G.Coloring α) (a b : α)

/-- A changed vertex forces every active neighbour to change as well;
otherwise the target colouring would give their edge equal colours. -/
theorem changed_neighbour_of_pointwise_swap
    (hpair : ∀ v, D v = C v ∨ D v = Equiv.swap a b (C v))
    {u v : V} (hu : D u ≠ C u) (hadj : G.Adj u v)
    (hv : C v = a ∨ C v = b) : D v ≠ C v := by
  have hus : D u = Equiv.swap a b (C u) := (hpair u).resolve_left hu
  have hua : C u = a ∨ C u = b :=
    Equiv.eq_or_eq_of_swap_apply_ne_self (fun h => hu (hus.trans h))
  have huv : C u ≠ C v := C.valid hadj
  have hswap : Equiv.swap a b (C u) = C v := by
    rcases hua with hua | hua <;> rcases hv with hv | hv <;> simp_all
  intro heq
  exact D.valid hadj (hus.trans (hswap.trans heq.symm))

/-- An actual component rooted at a discrepancy lies entirely in the
changed set. This identifies which physical switches must be used. -/
theorem component_changed_of_pointwise_swap
    (hpair : ∀ v, D v = C v ∨ D v = Equiv.swap a b (C v))
    {u : V} (hu : D u ≠ C u) (hua : u ∈ C.bicoloredSet a b) :
    C.kempeComponentSet a b
      ((C.bicoloredSubgraph a b).connectedComponentMk ⟨u, hua⟩) ⊆
        {v | D v ≠ C v} :=
  C.kempeComponentSet_subset_of_closed hua hu
    (fun _ _ h hAdj hActive => changed_neighbour_of_pointwise_swap C D a b hpair h hAdj hActive)

/-- A pointwise partial transposition between proper colourings is a
finite sequence of ordinary component switches. -/
theorem mem_kempeClosure_of_pointwise_swap [Fintype V]
    (hpair : ∀ v, D v = C v ∨ D v = Equiv.swap a b (C v)) :
    D ∈ G.KempeClosure C := by
  classical
  suffices ∀ n : ℕ, ∀ C : G.Coloring α,
      (Finset.univ.filter fun v => C v ≠ D v).card = n →
      (∀ v, D v = C v ∨ D v = Equiv.swap a b (C v)) →
      D ∈ G.KempeClosure C from this _ C rfl hpair
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro C hcard hpair
    by_cases heq : C = D
    · subst C
      exact .refl
    · obtain ⟨u, hu⟩ : ∃ u, D u ≠ C u := by
        by_contra! h
        exact heq (DFunLike.ext _ _ fun v => (h v).symm)
      have hus : D u = Equiv.swap a b (C u) := (hpair u).resolve_left hu
      have hua : u ∈ C.bicoloredSet a b :=
        Equiv.eq_or_eq_of_swap_apply_ne_self (fun h => hu (hus.trans h))
      let K := (C.bicoloredSubgraph a b).connectedComponentMk ⟨u, hua⟩
      let next := C.swapOnKempeComponent a b K
      have hchanged := component_changed_of_pointwise_swap C D a b hpair hu hua
      have hfix (v : V) (hv : v ∈ C.kempeComponentSet a b K) : next v = D v :=
        (C.swapOnKempeComponent_apply_of_mem hv).trans
          ((hpair v).resolve_left (hchanged hv)).symm
      have hnext : ∀ v, D v = next v ∨ D v = Equiv.swap a b (next v) := by
        intro v
        by_cases hv : v ∈ C.kempeComponentSet a b K
        · exact Or.inl (hfix v hv).symm
        · simpa only [next, C.swapOnKempeComponent_apply_of_not_mem hv] using hpair v
      let bad := Finset.univ.filter fun v => C v ≠ D v
      let smaller := Finset.univ.filter fun v => next v ≠ D v
      have hsub : smaller ⊆ bad := by
        intro v hv
        have hn := (Finset.mem_filter.mp hv).2
        have hout : v ∉ C.kempeComponentSet a b K := fun h => hn (hfix v h)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun h => hn ((C.swapOnKempeComponent_apply_of_not_mem hout).trans h)⟩
      have hub : u ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu.symm⟩
      have hun : u ∉ smaller := by
        intro h
        exact (Finset.mem_filter.mp h).2 (hfix u (C.mem_kempeComponentSet_self hua))
      have hlt : smaller.card < n := by
        rw [← hcard]
        exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨hsub, fun h => hun (h.symm ▸ hub)⟩)
      exact (Relation.ReflTransGen.single (G.kempeStep_swapOnKempeComponent C a b K)).trans
        (ih smaller.card hlt next rfl hnext)

end SimpleGraph.Coloring
