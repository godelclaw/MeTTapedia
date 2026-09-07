import Archive.Wiedijk100Theorems.AscendingDescendingSequences
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# A common monotone subsequence for finitely many injective coordinates

Iterate the finite Erdős--Szekeres theorem on the same ordered index set.
For `a` coordinates, more than `b^(2^a)` indices supply `b+1` indices on
which each coordinate is strictly increasing or strictly decreasing.
The signs may differ between coordinates. No compatibility of the original
orders is assumed. Contour meshes use the indices as linkage columns and
the coordinates as the positions of first-hit vertices on contour rows.
-/

namespace Mettapedia.GraphTheory.FourColor.SimultaneousMonotoneThinning

/-- A dimension-explicit common subsequence; the index embedding itself is
increasing, so all previously established column data is retained. -/
theorem exists_orderEmbedding (a b N : ℕ) (f : Fin a → Fin N → ℕ)
    (hf : ∀ i, Function.Injective (f i)) (hn : b ^ (2 ^ a) < N) :
    ∃ e : Fin (b + 1) ↪o Fin N,
      ∀ i, StrictMono (fun j => f i (e j)) ∨ StrictAnti (fun j => f i (e j)) := by
  classical
  induction a generalizing N with
  | zero =>
    refine ⟨Fin.castLEOrderEmb (by simpa using hn), ?_⟩
    intro i
    exact Fin.elim0 i
  | succ a ih =>
    let r := b ^ (2 ^ a)
    have hsize : r * r < Fintype.card (Fin N) := by
      simpa [r, pow_succ, pow_mul, pow_two] using hn
    obtain ⟨s, hs, hmono⟩ : ∃ s : Finset (Fin N), r < s.card ∧
        (StrictMonoOn (f 0) s ∨ StrictAntiOn (f 0) s) := by
      rcases Theorems100.erdos_szekeres hsize (hf 0) with ⟨s, hs, hm⟩ | ⟨s, hs, hm⟩
      · exact ⟨s, hs, Or.inl hm⟩
      · exact ⟨s, hs, Or.inr hm⟩
    let e₀ : Fin (r + 1) ↪o Fin N := s.orderEmbOfCardLe (by omega)
    have he₀ (j) : e₀ j ∈ s := s.orderEmbOfCardLe_mem _ j
    obtain ⟨e, he⟩ := ih (r + 1) (fun i j => f i.succ (e₀ j))
      (fun i => (hf i.succ).comp e₀.injective) (by exact Nat.lt_succ_self r)
    refine ⟨e.trans e₀, ?_⟩
    intro i
    refine Fin.cases ?_ (fun i => he i) i
    rcases hmono with hm | hm
    · exact Or.inl (fun j k hjk => hm (he₀ (e j)) (he₀ (e k))
        (e₀.strictMono (e.strictMono hjk)))
    · exact Or.inr (fun j k hjk => hm (he₀ (e j)) (he₀ (e k))
        (e₀.strictMono (e.strictMono hjk)))

end Mettapedia.GraphTheory.FourColor.SimultaneousMonotoneThinning
