import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Ring.Parity

/-!
# An even edge set cannot be supported in a ranked forest

Orient each forest edge from child to parent. Children are distinct and
rank strictly decreases along an edge. A maximum-rank selected child then
has exactly one selected incident edge. Thus an edge set having even
incidence at every vertex is empty.

The intended consumer is the primal complement of a dual breadth-first
tree: full primal cuts have even incidence at each quotient face.
-/

namespace Mettapedia.GraphTheory.FourColor.RankedForestParity

variable {E F : Type*}

/-- A nonempty selection in a ranked forest has a leaf in that selection. -/
theorem exists_singleton_incidence (edges : Finset E)
    (child parent : E → F) (rank : F → ℕ)
    (hinj : Set.InjOn child edges)
    (hdown : ∀ e ∈ edges, rank (parent e) < rank (child e))
    (hne : edges.Nonempty) :
    ∃ e ∈ edges, ∀ f ∈ edges, child f = child e ∨ parent f = child e ↔ f = e := by
  obtain ⟨e, he, hmax⟩ := edges.exists_max_image (fun e => rank (child e)) hne
  refine ⟨e, he, ?_⟩
  intro f hf
  constructor
  · rintro (hc | hp)
    · exact hinj hf he hc
    · have hd := hdown f hf
      rw [hp] at hd
      exact (Nat.not_lt_of_ge (hmax f hf) hd).elim
  · rintro rfl
    exact Or.inl rfl

/-- Parity eliminates the only possible nonempty support in a ranked forest. -/
theorem eq_empty_of_even_incidence [DecidableEq E] [DecidableEq F] (edges : Finset E)
    (child parent : E → F) (rank : F → ℕ)
    (hinj : Set.InjOn child edges)
    (hdown : ∀ e ∈ edges, rank (parent e) < rank (child e))
    (heven : ∀ v, Even (edges.filter (fun e => child e = v ∨ parent e = v)).card) :
    edges = ∅ := by
  classical
  by_contra hn
  obtain ⟨e, he, hleaf⟩ := exists_singleton_incidence edges child parent rank hinj hdown
    (Finset.nonempty_iff_ne_empty.mpr hn)
  have hsingle : edges.filter (fun f => child f = child e ∨ parent f = child e) = {e} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hf, hv⟩
      exact (hleaf f hf).mp hv
    · rintro rfl
      exact ⟨he, Or.inl rfl⟩
  have := heven (child e)
  simpa [hsingle] using this

end Mettapedia.GraphTheory.FourColor.RankedForestParity
