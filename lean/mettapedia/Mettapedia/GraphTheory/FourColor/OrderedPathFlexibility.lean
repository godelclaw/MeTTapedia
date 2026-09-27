import Mettapedia.GraphTheory.FourColor.OrderedPathExtension
import Mathlib.Data.Fin.Rev

/-!
# Choosing a path colouring for a later attachment

On a path with at least four edges, prescribed end-edge colours leave
enough freedom to use any specified colour at the first internal vertex.
The chosen witness retains the original edge identifiers.
-/

namespace Mettapedia.GraphTheory.FourColor.OrderedEdgePath

open GoertzelV24ForkInterfaceSupport ThreeColourPathWords

noncomputable section

variable {V E : Type*} [DecidableEq V]
variable {inc : E → Finset V} {S : Finset E} (p : Path inc S)

/-- The vertex reached after the first edge. -/
def Path.nextVertex : V := p.vertex ⟨1, by have := p.positive; omega⟩

theorem Path.firstEdge_incident_next : p.nextVertex ∈ inc p.firstEdge := by
  rw [Path.firstEdge, p.endpoints]
  exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr
    (congrArg p.vertex (Fin.ext rfl)))

theorem Path.secondEdge_incident_next (h : 2 ≤ p.length) :
    p.nextVertex ∈ inc (p.edge ⟨1, by omega⟩).val := by
  rw [p.endpoints]
  exact Finset.mem_insert_self _ _

/-- Reversal changes only the path coordinates, not its vertices or edges. -/
def Path.reverse : Path inc S where
  length := p.length
  positive := p.positive
  vertex := fun i => p.vertex i.rev
  vertex_injective := p.vertex_injective.comp Fin.rev_injective
  edge := Fin.revPerm.trans p.edge
  endpoints := by
    intro i
    dsimp only [Equiv.trans_apply, Fin.revPerm_apply]
    rw [p.endpoints, Fin.rev_castSucc, Fin.rev_succ, Finset.pair_comm]
    rfl

@[simp] theorem Path.reverse_first : p.reverse.first = p.last := rfl

@[simp] theorem Path.reverse_last : p.reverse.last = p.first := by
  simp [Path.reverse, Path.first, Path.last]

@[simp] theorem Path.reverse_firstEdge : p.reverse.firstEdge = p.lastEdge := rfl

@[simp] theorem Path.reverse_lastEdge : p.reverse.lastEdge = p.firstEdge := by
  change (p.edge (⟨p.length - 1, _⟩ : Fin p.length).rev).val = (p.edge ⟨0, _⟩).val
  congr 2
  apply Fin.ext
  simp only [Fin.val_rev]
  have := p.positive
  omega

theorem Path.eq_next_of_first_edge {v : V} (hv : v ∈ inc p.firstEdge) (hne : v ≠ p.first) :
    v = p.nextVertex := by
  rw [Path.firstEdge, p.endpoints, Finset.mem_insert, Finset.mem_singleton] at hv
  exact hv.resolve_left hne

/-- A vertex just inside either end of the path, specified by incidence. -/
def Path.EndNeighbour (v : V) : Prop :=
  (v ∈ inc p.firstEdge ∧ v ≠ p.first) ∨ (v ∈ inc p.lastEdge ∧ v ≠ p.last)

variable [DecidableEq E]

/-- The first two edge colours can be chosen independently of the last,
subject only to their being different. -/
theorem Path.prescribed_second (hn : 4 ≤ p.length) (a b z : Fin 3) (hab : a ≠ b) :
    ∃ c : E → Fin 3, p.Consecutive c ∧ c p.firstEdge = a ∧
      c (p.edge ⟨1, by omega⟩).val = b ∧ c p.lastEdge = z := by
  obtain ⟨v, hv0, hvn, hv⟩ := admits_of_two_le (show 2 ≤ p.length - 2 by omega) b z
  let w : ℕ → Fin 3
    | 0 => a
    | i + 1 => v i
  have hw (i : ℕ) (hi : i < p.length - 1) : w i ≠ w (i + 1) := by
    cases i with
    | zero => simpa only [w, hv0] using hab
    | succ i => exact hv i (by omega)
  refine ⟨p.colourOfWord w, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    rw [p.colourOfWord_edge, p.colourOfWord_edge, ← hij]
    exact hw i.val (by have := j.isLt; omega)
  · exact p.colourOfWord_edge w ⟨0, p.positive⟩
  · exact (p.colourOfWord_edge w ⟨1, by omega⟩).trans hv0
  · rw [Path.lastEdge, p.colourOfWord_edge]
    have he : p.length - 1 = (p.length - 2) + 1 := by omega
    simpa only [he, w] using hvn

/-- Any one colour can be made present at the first internal vertex,
without changing the prescribed colours at either end of the path. -/
theorem Path.prescribed_using_next (hn : 4 ≤ p.length) (a z q : Fin 3) :
    ∃ c : E → Fin 3, p.Consecutive c ∧ c p.firstEdge = a ∧
      c p.lastEdge = z ∧ q ∈ profile inc S c p.nextVertex := by
  obtain ⟨b, hab, hq⟩ : ∃ b : Fin 3, a ≠ b ∧ (q = a ∨ q = b) := by
    by_cases hqa : q = a
    · obtain ⟨b, hba, _⟩ := Fin.exists_ne_and_ne_of_two_lt a a (by decide)
      exact ⟨b, hba.symm, Or.inl hqa⟩
    · exact ⟨q, Ne.symm hqa, Or.inr rfl⟩
  obtain ⟨c, hc, hca, hcb, hcz⟩ := p.prescribed_second hn a b z hab
  refine ⟨c, hc, hca, hcz, ?_⟩
  rcases hq with rfl | rfl
  · exact Finset.mem_image.mpr ⟨p.firstEdge,
      Finset.mem_filter.mpr ⟨p.firstEdge_mem, p.firstEdge_incident_next⟩, hca⟩
  · exact Finset.mem_image.mpr ⟨(p.edge ⟨1, by omega⟩).val,
      Finset.mem_filter.mpr ⟨(p.edge _).property, p.secondEdge_incident_next (by omega)⟩, hcb⟩

/-- The freedom is available at either end, independently of orientation. -/
theorem Path.prescribed_using_neighbour (hn : 4 ≤ p.length) (v : V)
    (hv : p.EndNeighbour v) (a z q : Fin 3) :
    ∃ c : E → Fin 3, p.Consecutive c ∧ c p.firstEdge = a ∧
      c p.lastEdge = z ∧ q ∈ profile inc S c v := by
  rcases hv with ⟨hv, hne⟩ | ⟨hv, hne⟩
  · rw [p.eq_next_of_first_edge hv hne]
    exact p.prescribed_using_next hn a z q
  · have hv' : v = p.reverse.nextVertex :=
      p.reverse.eq_next_of_first_edge (by simpa using hv) (by simpa using hne)
    obtain ⟨c, hc, hcz, hca, hq⟩ := p.reverse.prescribed_using_next hn z a q
    exact ⟨c, (p.proper_iff c).mp ((p.reverse.proper_iff c).mpr hc),
      by simpa using hca, by simpa using hcz, hv'.symm ▸ hq⟩

end
end Mettapedia.GraphTheory.FourColor.OrderedEdgePath
