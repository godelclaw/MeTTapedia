import Mettapedia.GraphTheory.Kempe.PairDecomposition
import Mettapedia.GraphTheory.FourColor.KempeChainCertificate

/-!
# Uniform Kempe repair of an ordered fan exterior

Vertex zero is the hub; the remaining vertices form an ordered path.
First align the hub colour. Then align the path one vertex at a time by
transposing two colours on a suffix. The already aligned predecessor and
the hub use neither colour, so the suffix operation stays proper.

The existing partial-transposition theorem decomposes each operation into
actual whole-component switches. Thus any two proper colourings of any
finite fan are connected by a physical Kempe history, without a state table.
-/

namespace Mettapedia.GraphTheory.FourColor.OrderedFanKempe

open KempeChainCertificate

/-- A hub joined to every vertex of a path, including the degenerate sizes. -/
def graph (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj u v := u ≠ v ∧ (u = 0 ∨ v = 0 ∨ u.val + 1 = v.val ∨ v.val + 1 = u.val)
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (n : ℕ) : DecidableRel (graph n).Adj := by unfold graph; infer_instance

variable {n : ℕ} {α : Type*} [DecidableEq α]

private theorem across_cut (i u v : Fin (n + 1)) (hi : 0 < i.val)
    (hu : i.val ≤ u.val) (hv : v.val < i.val) (h : (graph n).Adj u v) :
    (graph n).Adj i v := by
  refine ⟨fun he => by have := congrArg Fin.val he; omega, ?_⟩
  rcases h.2 with hu0 | hv0 | huv | hvu
  · have : u.val = 0 := congrArg Fin.val hu0
    omega
  · exact Or.inr (Or.inl hv0)
  · omega
  · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- A single suffix transposition extends the agreed prefix. Its realization
may switch several components, all in the same two-colour graph. -/
theorem advance (C D : (graph n).Coloring α) (i : Fin (n + 1)) (hi : 0 < i.val)
    (agreed : ∀ v, v.val < i.val → C v = D v) :
    ∃ next : (graph n).Coloring α, next ∈ (graph n).KempeClosure C ∧
      ∀ v, v.val ≤ i.val → next v = D v := by
  classical
  let swap := Equiv.swap (C i) (D i)
  let nextValue := fun v : Fin (n + 1) => if i.val ≤ v.val then swap (C v) else C v
  have inactive (u v : Fin (n + 1)) (hu : i.val ≤ u.val) (hv : v.val < i.val)
      (h : (graph n).Adj u v) : swap (C v) = C v := by
    have edge := across_cut i u v hi hu hv h
    apply Equiv.swap_apply_of_ne_of_ne
    · exact (C.valid edge).symm
    · rw [agreed v hv]
      exact (D.valid edge).symm
  have proper : ∀ u v, (graph n).Adj u v → nextValue u ≠ nextValue v := by
    intro u v h
    by_cases hu : i.val ≤ u.val <;> by_cases hv : i.val ≤ v.val
    · simpa only [nextValue, ite_eq_left hu, ite_eq_left hv] using swap.injective.ne (C.valid h)
    · simp only [nextValue, ite_eq_left hu, ite_eq_right hv]
      rw [← inactive u v hu (by omega) h]
      exact swap.injective.ne (C.valid h)
    · simp only [nextValue, ite_eq_right hu, ite_eq_left hv]
      rw [← inactive v u hv (by omega) h.symm]
      exact swap.injective.ne (C.valid h)
    · simpa only [nextValue, ite_eq_right hu, ite_eq_right hv] using C.valid h
  let next : (graph n).Coloring α := .mk nextValue (fun h => proper _ _ h)
  refine ⟨next, C.mem_kempeClosure_of_pointwise_swap next (C i) (D i) ?_, ?_⟩
  · intro v
    change nextValue v = C v ∨ nextValue v = swap (C v)
    by_cases hv : i.val ≤ v.val
    · exact Or.inr (ite_eq_left hv)
    · exact Or.inl (ite_eq_right hv)
  · intro v hv
    change nextValue v = D v
    by_cases he : v = i
    · subst v
      simp [nextValue, swap]
    · have hlt : v.val < i.val := by
        have hne : v.val ≠ i.val := fun h => he (Fin.ext h)
        omega
      simpa only [nextValue, ite_eq_right (by omega : ¬ i.val ≤ v.val)] using agreed v hlt

/-- A fan of arbitrary length has a single Kempe class for any palette
for which the displayed source and target colourings exist. -/
theorem reachable (C D : (graph n).Coloring α) : D ∈ (graph n).KempeClosure C := by
  classical
  let swap := Equiv.swap (C 0) (D 0)
  let aligned : (graph n).Coloring α :=
    .mk (fun v => swap (C v)) (fun h => swap.injective.ne (C.valid h))
  have aligned_reachable : aligned ∈ (graph n).KempeClosure C :=
    C.mem_kempeClosure_of_pointwise_swap aligned (C 0) (D 0) (fun _ => Or.inr rfl)
  have fill : ∀ k, k ≤ n → ∃ next : (graph n).Coloring α,
      next ∈ (graph n).KempeClosure C ∧ ∀ v, v.val ≤ k → next v = D v := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨aligned, aligned_reachable, ?_⟩
      intro v hv
      have he : v = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      subst v
      exact Equiv.swap_apply_left _ _
    | succ k ih =>
      intro hk
      obtain ⟨middle, history, agreed⟩ := ih (by omega)
      let i : Fin (n + 1) := ⟨k + 1, by omega⟩
      obtain ⟨next, step, agree⟩ := advance middle D i (by simp [i])
        (fun v hv => agreed v (by change v.val < k + 1 at hv; omega))
      exact ⟨next, history.trans step, agree⟩
  obtain ⟨next, history, agree⟩ := fill n (by rfl)
  have he : next = D := DFunLike.ext _ _ (fun v => agree v (by have := v.isLt; omega))
  exact he ▸ history

/-- The reachability theorem supplies proof-relevant construction-language
histories with actual connected-component witnesses at every step. -/
theorem history (C D : (graph n).Coloring α) : Nonempty (History C D) :=
  nonempty_history_iff.mpr (reachable C D)

end Mettapedia.GraphTheory.FourColor.OrderedFanKempe
