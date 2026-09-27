import Mettapedia.GraphTheory.Kempe.LowDegree

/-!
# Relative elimination transports Kempe reachability

The retained core is arbitrary. The graph representation is supplied
with its exact induced-adjacency law, so the result applies without
changing vertex identifiers. If every nonempty remaining part of a
deleted set has a vertex of degree at most two, a three-colour Kempe
history on the core can be reproduced before the deletion.
-/

namespace SimpleGraph.KempeRelativeElimination

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) (H : Finset V → SimpleGraph V)
variable [∀ A, DecidableRel (H A).Adj]
variable (faithful : ∀ A x y, (H A).Adj x y ↔ x ∈ A ∧ y ∈ A ∧ G.Adj x y)
include faithful

omit [Fintype V] [DecidableEq V] [∀ A, DecidableRel (H A).Adj] in
/-- Every representation with the exact induced adjacency is monotone. -/
theorem restriction_mono {A B : Finset V} (h : A ⊆ B) : H A ≤ H B := by
  intro x y hxy
  obtain ⟨hx, hy, hxy⟩ := (faithful A x y).mp hxy
  exact (faithful B x y).mpr ⟨h hx, h hy, hxy⟩

omit [∀ A, DecidableRel (H A).Adj] in
private theorem lift_ignored_vertices (A : Finset V)
    {C D : (H A).Coloring (Fin 3)} (history : D ∈ (H A).KempeClosure C)
    (old : (H A).Coloring (Fin 3)) (hold : ∀ x ∈ A, old x = C x) :
    ∃ final : (H A).Coloring (Fin 3),
      final ∈ (H A).KempeClosure old ∧ ∀ x ∈ A, final x = D x := by
  induction history with
  | refl => exact ⟨old, .refl, hold⟩
  | @tail D next hpath step ih =>
    obtain ⟨middle, hmiddle, hagree⟩ := ih
    obtain ⟨a, b, K, rfl⟩ := step
    let next := D.swapOnKempeComponent a b K
    let final : (H A).Coloring (Fin 3) := .mk
      (fun x => if x ∈ A then next x else middle x) (by
        intro x y hxy
        obtain ⟨hx, hy, _⟩ := (faithful A x y).mp hxy
        simpa [hx, hy] using next.valid hxy)
    have hval (x : V) : final x = (if x ∈ A then next x else middle x) := rfl
    have hreach : final ∈ (H A).KempeClosure middle := by
      apply middle.mem_kempeClosure_of_pointwise_swap final a b
      intro x
      by_cases hx : x ∈ A
      · rw [hval, ite_eq_left hx, hagree x hx]
        by_cases hK : x ∈ D.kempeComponentSet a b K
        · exact Or.inr (D.swapOnKempeComponent_apply_of_mem hK)
        · exact Or.inl (D.swapOnKempeComponent_apply_of_not_mem hK)
      · exact Or.inl (by simp [hval, hx])
    exact ⟨final, hmiddle.trans hreach, fun x hx => by simp [hval, hx, next]⟩

/-- Relative low-degree elimination lifts to any specified proper
reconstruction, including all colours on the restored vertices. -/
theorem lifts (A S : Finset V) (hAS : Disjoint A S)
    (peel : ∀ T ⊆ S, T.Nonempty → ∃ v ∈ T, (H (A ∪ T)).degree v ≤ 2)
    {C D : (H A).Coloring (Fin 3)} (history : D ∈ (H A).KempeClosure C)
    (old target : (H (A ∪ S)).Coloring (Fin 3))
    (hold : ∀ x ∈ A, old x = C x) (htarget : ∀ x ∈ A, target x = D x) :
    ∃ final : (H (A ∪ S)).Coloring (Fin 3),
      final ∈ (H (A ∪ S)).KempeClosure old ∧ ∀ x ∈ A ∪ S, final x = target x := by
  suffices ∀ T ⊆ S, ∀ old target : (H (A ∪ T)).Coloring (Fin 3),
      (∀ x ∈ A, old x = C x) → (∀ x ∈ A, target x = D x) →
      ∃ final : (H (A ∪ T)).Coloring (Fin 3),
        final ∈ (H (A ∪ T)).KempeClosure old ∧ ∀ x ∈ A ∪ T, final x = target x from
    this S Finset.Subset.rfl old target hold htarget
  intro T
  refine Finset.strongInductionOn T ?_
  intro T ih hTS old target hold htarget
  by_cases hT : T.Nonempty
  · obtain ⟨v, hv, hdeg⟩ := peel T hTS hT
    have hvA : v ∉ A := fun h => Finset.disjoint_left.mp hAS h (hTS hv)
    have hsub : A ∪ T.erase v ⊆ A ∪ T :=
      Finset.union_subset_union_right (Finset.erase_subset v T)
    let small := old.restrict (restriction_mono G H faithful hsub)
    let wanted := target.restrict (restriction_mono G H faithful hsub)
    obtain ⟨middle, hmiddle, hagree⟩ := ih (T.erase v) (Finset.erase_ssubset hv)
      ((Finset.erase_subset v T).trans hTS) small wanted hold htarget
    obtain ⟨final, hfinal, hlast⟩ := Coloring.kempeClosure_lifts_vertex v hdeg
      (fun x y hx hy hxy => by
        obtain ⟨hxT, hyT, hxy⟩ := (faithful (A ∪ T) x y).mp hxy
        apply (faithful (A ∪ T.erase v) x y).mpr
        exact ⟨by simpa [Finset.mem_union, Finset.mem_erase, hx] using hxT,
          by simpa [Finset.mem_union, Finset.mem_erase, hy] using hyT, hxy⟩)
      hmiddle old (fun _ _ => rfl)
    have hmatch (x : V) (hx : x ∈ A ∪ T) (hxv : x ≠ v) : final x = target x := by
      apply (hlast x hxv).trans
      exact hagree x (by simpa [Finset.mem_union, Finset.mem_erase, hxv] using hx)
    let answer : (H (A ∪ T)).Coloring (Fin 3) := .mk
      (fun x => if x = v then target x else final x) (by
        intro x y hxy
        have hm := (faithful (A ∪ T) x y).mp hxy
        by_cases hx : x = v <;> by_cases hy : y = v
        · exact (hxy.ne (hx.trans hy.symm)).elim
        · simpa [hx, hy, hmatch y hm.2.1 hy] using target.valid hxy
        · simpa [hx, hy, hmatch x hm.1 hx] using target.valid hxy
        · simpa [hx, hy] using final.valid hxy)
    have answer_apply (x : V) : answer x = (if x = v then target x else final x) := rfl
    have hanswer : answer ∈ (H (A ∪ T)).KempeClosure final := by
      apply final.mem_kempeClosure_of_pointwise_swap answer (final v) (target v)
      intro x
      by_cases hx : x = v
      · exact Or.inr (by simp [answer_apply, hx])
      · exact Or.inl (by simp [answer_apply, hx])
    refine ⟨answer, hfinal.trans hanswer, ?_⟩
    intro x hx
    by_cases hxv : x = v
    · simp [answer_apply, hxv]
    · simp [answer_apply, hxv, hmatch x hx hxv]
  · have hTempty := Finset.not_nonempty_iff_eq_empty.mp hT
    have base : ∀ start goal : (H (A ∪ T)).Coloring (Fin 3),
        (∀ x ∈ A, start x = C x) → (∀ x ∈ A, goal x = D x) →
        ∃ final : (H (A ∪ T)).Coloring (Fin 3),
          final ∈ (H (A ∪ T)).KempeClosure start ∧ ∀ x ∈ A ∪ T, final x = goal x := by
      rw [hTempty, Finset.union_empty]
      intro start goal hstart hgoal
      obtain ⟨final, hfinal, hagree⟩ := lift_ignored_vertices G H faithful A history start hstart
      exact ⟨final, hfinal, fun x hx => (hagree x hx).trans (hgoal x hx).symm⟩
    exact base old target hold htarget

end
end SimpleGraph.KempeRelativeElimination
