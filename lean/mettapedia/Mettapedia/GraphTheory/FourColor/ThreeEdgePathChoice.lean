import Mettapedia.GraphTheory.FourColor.OrderedPathFlexibility

/-!
# The exact choice available on a three-edge path

With end colours r and s, a colour q can be used at the first internal
vertex exactly when q = r or q differs from s. Thus a later constraint
cannot always be prepared: q = s with q different from r is the unique
obstruction. All witnesses retain the original edge identifiers.
-/

namespace Mettapedia.GraphTheory.FourColor.OrderedEdgePath

open GoertzelV24ForkInterfaceSupport

noncomputable section

variable {V E : Type*} [DecidableEq V] [DecidableEq E]
variable {inc : E → Finset V} {S : Finset E} (p : Path inc S)

omit [DecidableEq E] in
/-- Only the first two edges meet the first internal vertex. -/
theorem Path.profile_next (h : 2 ≤ p.length) (c : E → Fin 3) :
    profile inc S c p.nextVertex = {c p.firstEdge, c (p.edge ⟨1, by omega⟩).val} := by
  ext q
  simp only [profile, Finset.mem_image, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨x, ⟨hx, hvx⟩, hcx⟩
    obtain ⟨i, hi⟩ := p.edge.surjective ⟨x, hx⟩
    have he : (p.edge i).val = x := congrArg Subtype.val hi
    rw [← he, p.endpoints, Finset.mem_insert, Finset.mem_singleton] at hvx
    have hidx : i.val = 0 ∨ i.val = 1 := by
      rcases hvx with hvx | hvx
      · have hh := congrArg Fin.val (p.vertex_injective hvx)
        exact Or.inr hh.symm
      · have hh := congrArg Fin.val (p.vertex_injective hvx)
        exact Or.inl (by change 1 = i.val + 1 at hh; omega)
    rcases hidx with hidx | hidx
    · left
      have hi0 : i = ⟨0, p.positive⟩ := Fin.ext hidx
      exact hcx.symm.trans (congrArg c (he.symm.trans (by rw [hi0]; rfl)))
    · right
      have hi1 : i = ⟨1, by omega⟩ := Fin.ext hidx
      exact hcx.symm.trans (congrArg c (he.symm.trans (by rw [hi1])))
  · rintro (hq | hq)
    · exact ⟨p.firstEdge, ⟨p.firstEdge_mem, p.firstEdge_incident_next⟩, hq.symm⟩
    · exact ⟨(p.edge ⟨1, by omega⟩).val,
        ⟨(p.edge _).property, p.secondEdge_incident_next h⟩, hq.symm⟩

/-- A three-edge word has exactly its two adjacent inequalities. -/
theorem Path.prescribed_three (h : p.length = 3) (r m s : Fin 3)
    (hrm : r ≠ m) (hms : m ≠ s) :
    ∃ c : E → Fin 3, p.Consecutive c ∧ c p.firstEdge = r ∧
      c (p.edge ⟨1, by omega⟩).val = m ∧ c p.lastEdge = s := by
  let w : ℕ → Fin 3 := fun i => if i = 0 then r else if i = 1 then m else s
  refine ⟨p.colourOfWord w, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    rw [p.colourOfWord_edge, p.colourOfWord_edge]
    have hi : i.val = 0 ∨ i.val = 1 := by have := j.isLt; omega
    rcases hi with hi | hi
    · have hj : j.val = 1 := by omega
      simpa [w, hi, hj] using hrm
    · have hj : j.val = 2 := by omega
      simpa [w, hi, hj] using hms
  · simp [Path.firstEdge, p.colourOfWord_edge, w]
  · simp [p.colourOfWord_edge, w]
  · simp [Path.lastEdge, p.colourOfWord_edge, w, h]

/-- Exact support for a later request at the first internal vertex. -/
theorem Path.prescribed_using_next_three_iff (h : p.length = 3) (r s q : Fin 3) :
    (∃ c : E → Fin 3, p.Consecutive c ∧ c p.firstEdge = r ∧
      c p.lastEdge = s ∧ q ∈ profile inc S c p.nextVertex) ↔ q = r ∨ q ≠ s := by
  constructor
  · rintro ⟨c, hc, hcr, hcs, hq⟩
    rw [p.profile_next (by omega) c, hcr, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq | hq
    · exact Or.inl hq
    · right
      have hh := hc ⟨1, by omega⟩ ⟨p.length - 1, by omega⟩ (by simp [h])
      change c (p.edge ⟨1, by omega⟩).val ≠ c p.lastEdge at hh
      rw [hcs, ← hq] at hh
      exact hh
  · intro hq
    obtain ⟨m, hrm, hms, hqm⟩ : ∃ m : Fin 3, r ≠ m ∧ m ≠ s ∧ (q = r ∨ q = m) := by
      by_cases hqr : q = r
      · obtain ⟨m, hmr, hms⟩ := Fin.exists_ne_and_ne_of_two_lt r s (by decide)
        exact ⟨m, hmr.symm, hms, Or.inl hqr⟩
      · exact ⟨q, Ne.symm hqr, hq.resolve_left hqr, Or.inr rfl⟩
    obtain ⟨c, hc, hcr, hcm, hcs⟩ := p.prescribed_three h r m s hrm hms
    refine ⟨c, hc, hcr, hcs, ?_⟩
    rw [p.profile_next (by omega) c, hcr, hcm, Finset.mem_insert, Finset.mem_singleton]
    exact hqm

end
end Mettapedia.GraphTheory.FourColor.OrderedEdgePath
