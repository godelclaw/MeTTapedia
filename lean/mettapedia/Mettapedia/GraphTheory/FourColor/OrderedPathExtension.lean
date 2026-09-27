import Mettapedia.GraphTheory.FourColor.OrderedEdgePath
import Mettapedia.GraphTheory.FourColor.ThreeColourPathWords

/-!
# Extension along an ordered simple edge path

Colour words are transported to the path's original edge identifiers.
This gives an exact length criterion for prescribed end-edge colours.
-/

namespace Mettapedia.GraphTheory.FourColor.OrderedEdgePath

open GoertzelV24ForkInterfaceSupport ThreeColourPathWords

noncomputable section

variable {V E : Type*} [DecidableEq V] [DecidableEq E]
variable {inc : E → Finset V} {S : Finset E} (p : Path inc S)

/-- Pull a word back to the original edge set; values outside it are irrelevant. -/
def Path.colourOfWord (w : ℕ → Fin 3) : E → Fin 3 :=
  fun x => if hx : x ∈ S then w (p.edge.symm ⟨x, hx⟩).val else 0

theorem Path.colourOfWord_edge (w : ℕ → Fin 3) (i : Fin p.length) :
    p.colourOfWord w (p.edge i).val = w i.val := by
  simp only [Path.colourOfWord, dite_eq_left (p.edge i).property]
  have he : (⟨(p.edge i).val, (p.edge i).property⟩ : S) = p.edge i := rfl
  rw [he, p.edge.symm_apply_apply]

/-- All prescribed-end assignments on the original path correspond to
words with one fewer adjacent pair than there are edges. -/
theorem Path.prescribed_iff (a b : Fin 3) :
    (∃ c : E → Fin 3, p.Consecutive c ∧ c p.firstEdge = a ∧ c p.lastEdge = b) ↔
      Admits (p.length - 1) a b := by
  constructor
  · rintro ⟨c, hc, hfirst, hlast⟩
    let w : ℕ → Fin 3 := fun i => if hi : i < p.length then c (p.edge ⟨i, hi⟩).val else 0
    have hw (i : Fin p.length) : w i.val = c (p.edge i).val := by
      simp only [w, dite_eq_left i.isLt]
    refine ⟨w, ?_, ?_, ?_⟩
    · exact (hw ⟨0, p.positive⟩).trans hfirst
    · exact (hw ⟨p.length - 1, by have := p.positive; omega⟩).trans hlast
    · intro i hi
      have hi0 : i < p.length := by omega
      have hi1 : i + 1 < p.length := by omega
      rw [hw ⟨i, hi0⟩, hw ⟨i + 1, hi1⟩]
      exact hc ⟨i, hi0⟩ ⟨i + 1, hi1⟩ rfl
  · rintro ⟨w, hw0, hwn, hnext⟩
    refine ⟨p.colourOfWord w, ?_, ?_, ?_⟩
    · intro i j hij
      rw [p.colourOfWord_edge, p.colourOfWord_edge]
      rw [← hij]
      exact hnext i.val (by have := j.isLt; omega)
    · exact (p.colourOfWord_edge w ⟨0, p.positive⟩).trans hw0
    · exact (p.colourOfWord_edge w ⟨p.length - 1, by have := p.positive; omega⟩).trans hwn

/-- A single edge forces equal ends, two edges force different ends, and
every longer path accepts every prescribed pair. -/
theorem Path.prescribed_length_iff (a b : Fin 3) :
    (∃ c : E → Fin 3, p.Consecutive c ∧ c p.firstEdge = a ∧ c p.lastEdge = b) ↔
      (p.length = 1 ∧ a = b) ∨ (p.length = 2 ∧ a ≠ b) ∨ 3 ≤ p.length := by
  rw [p.prescribed_iff, admits_iff]
  have := p.positive
  omega

/-- When each endpoint profile omits exactly one colour, the compatibility
criterion is the prescribed-end classification. -/
theorem Path.endpoint_extension_iff (A : Finset E) (a : E → Fin 3) (r s : Fin 3)
    (hr : ∀ q, q ∉ profile inc A a p.first ↔ q = r)
    (hs : ∀ q, q ∉ profile inc A a p.last ↔ q = s) :
    (∃ c : E → Fin 3, p.Consecutive c ∧ p.EndpointCompatible A a c) ↔
      (p.length = 1 ∧ r = s) ∨ (p.length = 2 ∧ r ≠ s) ∨ 3 ≤ p.length := by
  simp only [Path.EndpointCompatible, hr, hs]
  exact p.prescribed_length_iff r s

end
end Mettapedia.GraphTheory.FourColor.OrderedEdgePath
