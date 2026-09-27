import Mettapedia.GraphTheory.Kempe.RelativeElimination
import Mettapedia.GraphTheory.FourColor.ShortPathKempeLifting

/-!
# Long path deletion preserves Kempe reachability

An attached simple path with at least three edges can be removed by
low-degree deletions in the literal incidence graph. Internal path edges
have at most two neighbours. Once they are gone, each end edge meets at
most two retained edges. Thus smaller recolouring histories lift without
any intermediate reconstruction hypothesis.
-/

namespace Mettapedia.GraphTheory.FourColor.LongPathKempeLifting

open GoertzelV24ForkInterfaceSupport IncidenceKempeSwitch KempeChainCertificate
open Mettapedia.GSLT.Ultrainfinite

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
variable {inc : E → Finset V} {S : Finset E} (p : OrderedEdgePath.Path inc S)

omit [DecidableEq E] [Fintype E] in
theorem meeting_indices {i j : Fin p.length}
    (hne : (p.edge i).val ≠ (p.edge j).val)
    (hmeet : (inc (p.edge i).val ∩ inc (p.edge j).val).Nonempty) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  obtain ⟨v, hv⟩ := hmeet
  obtain ⟨hi, hj⟩ := Finset.mem_inter.mp hv
  rw [p.endpoints, Finset.mem_insert, Finset.mem_singleton] at hi hj
  have hidx : i ≠ j := fun h => hne (congrArg (fun k => (p.edge k).val) h)
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · have h := congrArg Fin.val (p.vertex_injective (hi.symm.trans hj))
    exact (hidx (Fin.ext h)).elim
  · exact Or.inr (congrArg Fin.val (p.vertex_injective (hj.symm.trans hi)))
  · exact Or.inl (congrArg Fin.val (p.vertex_injective (hi.symm.trans hj)))
  · exact (hidx (Fin.ext (by
      have h := congrArg Fin.val (p.vertex_injective (hi.symm.trans hj))
      change i.val + 1 = j.val + 1 at h
      omega))).elim

variable (A : Finset E)
variable (shared : ∀ x ∈ A, ∀ y ∈ S, ∀ v, v ∈ inc x → v ∈ inc y →
  v = p.first ∨ v = p.last)
include shared

omit [Fintype E] in
/-- A path-internal edge has no neighbours in the retained core. -/
theorem internal_not_meet {x y : E} (hx : x ∈ S)
    (hfirst : x ≠ p.firstEdge) (hlast : x ≠ p.lastEdge) (hy : y ∈ A) :
    ¬ (inc x ∩ inc y).Nonempty := by
  rintro ⟨v, hv⟩
  obtain ⟨hvx, hvy⟩ := Finset.mem_inter.mp hv
  rcases shared y hy x hx v hvy hvx with hv | hv
  · exact hfirst (p.eq_firstEdge hx (hv ▸ hvx))
  · exact hlast (p.eq_lastEdge hx (hv ▸ hvx))

/-- Every nonempty remaining subset has a removable edge of degree at
most two. This is geometric and independent of the chosen colouring. -/
theorem peel (hlong : 3 ≤ p.length)
    (hfirst : (A.filter fun x => p.first ∈ inc x).card ≤ 2)
    (hlast : (A.filter fun x => p.last ∈ inc x).card ≤ 2)
    (T : Finset E) (hTS : T ⊆ S) (hT : T.Nonempty) :
    ∃ x ∈ T, (graph inc (A ∪ T)).degree x ≤ 2 := by
  by_cases hint : ∃ x ∈ T, x ≠ p.firstEdge ∧ x ≠ p.lastEdge
  · obtain ⟨x, hx, hxf, hxl⟩ := hint
    obtain ⟨i, hi⟩ := p.edge.surjective ⟨x, hTS hx⟩
    have hix : (p.edge i).val = x := congrArg Subtype.val hi
    let index : E → ℕ := fun y => if hy : y ∈ S then (p.edge.symm ⟨y, hy⟩).val else 0
    have index_edge (j : Fin p.length) : index (p.edge j).val = j.val := by
      simp [index]
    refine ⟨x, hx, le_trans (Finset.card_le_card_of_injOn index (t := {i.val - 1, i.val + 1}) ?_ ?_)
      Finset.card_le_two⟩
    · intro y hy
      have hadj := ((graph inc (A ∪ T)).mem_neighborFinset x y).mp hy
      have hyT : y ∈ T := (Finset.mem_union.mp hadj.2.2.1).resolve_left
        (fun hyA => internal_not_meet p A shared (hTS hx) hxf hxl hyA hadj.2.2.2)
      obtain ⟨j, hj⟩ := p.edge.surjective ⟨y, hTS hyT⟩
      have hjy : (p.edge j).val = y := congrArg Subtype.val hj
      have hnext := meeting_indices p (hix.symm ▸ hjy.symm ▸ hadj.1)
        (hix.symm ▸ hjy.symm ▸ hadj.2.2.2)
      rw [← hjy, index_edge]
      change j.val ∈ ({i.val - 1, i.val + 1} : Finset ℕ)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · intro y hy z hz heq
      have retained (w : E) (hw : w ∈ (graph inc (A ∪ T)).neighborFinset x) : w ∈ S := by
        have h := ((graph inc (A ∪ T)).mem_neighborFinset x w).mp hw
        exact hTS ((Finset.mem_union.mp h.2.2.1).resolve_left
          (fun hwA => internal_not_meet p A shared (hTS hx) hxf hxl hwA h.2.2.2))
      have hyS := retained y hy
      have hzS := retained z hz
      have idx : p.edge.symm ⟨y, hyS⟩ = p.edge.symm ⟨z, hzS⟩ :=
        Fin.ext (by simpa [index, hyS, hzS] using heq)
      exact congrArg Subtype.val (p.edge.symm.injective idx)
  · have hend : ∀ x ∈ T, x = p.firstEdge ∨ x = p.lastEdge := by
      intro x hx
      by_contra h
      exact hint ⟨x, hx, fun hxf => h (Or.inl hxf), fun hxl => h (Or.inr hxl)⟩
    have apart : ¬ (inc p.firstEdge ∩ inc p.lastEdge).Nonempty := by
      intro hm
      have hne : p.firstEdge ≠ p.lastEdge := by
        intro he
        have h := congrArg Fin.val (p.edge.injective (Subtype.ext he))
        change 0 = p.length - 1 at h
        omega
      have h := meeting_indices p (i := ⟨0, p.positive⟩)
        (j := ⟨p.length - 1, by have := p.positive; omega⟩) hne hm
      dsimp only at h
      omega
    obtain ⟨x, hx⟩ := hT
    have hsmall (v : V) (hv : x = p.firstEdge ∧ v = p.first ∨ x = p.lastEdge ∧ v = p.last) :
        (graph inc (A ∪ T)).neighborFinset x ⊆ A.filter (fun y => v ∈ inc y) := by
      intro y hy
      have h := ((graph inc (A ∪ T)).mem_neighborFinset x y).mp hy
      have hyA : y ∈ A := (Finset.mem_union.mp h.2.2.1).resolve_right (fun hyT => by
        rcases hend x hx with hxf | hxl <;> rcases hend y hyT with hyf | hyl
        · exact h.1 (hxf.trans hyf.symm)
        · exact apart (hxf ▸ hyl ▸ h.2.2.2)
        · exact apart (by simpa [hxl, hyf, Finset.inter_comm] using h.2.2.2)
        · exact h.1 (hxl.trans hyl.symm))
      obtain ⟨w, hw⟩ := h.2.2.2
      obtain ⟨hwx, hwy⟩ := Finset.mem_inter.mp hw
      rcases shared y hyA x (hTS hx) w hwy hwx with hw | hw
      · rcases hv with ⟨_, rfl⟩ | ⟨hxl, _⟩
        · exact Finset.mem_filter.mpr ⟨hyA, hw ▸ hwy⟩
        · exact (apart ⟨p.first, Finset.mem_inter.mpr
            ⟨p.firstEdge_incident, hxl ▸ hw ▸ hwx⟩⟩).elim
      · rcases hv with ⟨hxf, _⟩ | ⟨_, rfl⟩
        · exact (apart ⟨p.last, Finset.mem_inter.mpr
            ⟨hxf ▸ hw ▸ hwx, p.lastEdge_incident⟩⟩).elim
        · exact Finset.mem_filter.mpr ⟨hyA, hw ▸ hwy⟩
    refine ⟨x, hx, ?_⟩
    rcases hend x hx with hf | hl
    · exact (Finset.card_le_card (hsmall p.first (Or.inl ⟨hf, rfl⟩))).trans hfirst
    · exact (Finset.card_le_card (hsmall p.last (Or.inr ⟨hl, rfl⟩))).trans hlast

/-- Every smaller history lifts across a path of at least three edges.
Only its two endpoint incidences meet the arbitrary retained core. -/
theorem history_lifts (hlong : 3 ≤ p.length) (hAS : Disjoint A S)
    (hfirst : (A.filter fun x => p.first ∈ inc x).card ≤ 2)
    (hlast : (A.filter fun x => p.last ∈ inc x).card ≤ 2)
    {C D : (graph inc A).Coloring (Fin 3)} (history : History C D)
    (old target : (graph inc (A ∪ S)).Coloring (Fin 3))
    (hold : ∀ x ∈ A, old x = C x) (htarget : ∀ x ∈ A, target x = D x) :
    ∃ final : (graph inc (A ∪ S)).Coloring (Fin 3),
      Nonempty (History old final) ∧ ∀ x ∈ A ∪ S, final x = target x := by
  have faithful : ∀ B x y, (graph inc B).Adj x y ↔
      x ∈ B ∧ y ∈ B ∧ (graph inc Finset.univ).Adj x y := by
    intro B x y
    change (x ≠ y ∧ x ∈ B ∧ y ∈ B ∧ _) ↔
      (x ∈ B ∧ y ∈ B ∧ x ≠ y ∧ x ∈ Finset.univ ∧ y ∈ Finset.univ ∧ _)
    simp only [Finset.mem_univ, true_and]
    tauto
  obtain ⟨final, hfinal, hagree⟩ := SimpleGraph.KempeRelativeElimination.lifts
    (graph inc Finset.univ) (graph inc) faithful A S hAS
    (peel p A shared hlong hfirst hlast)
    (nonempty_history_iff.mp ⟨history⟩) old target hold htarget
  exact ⟨final, nonempty_history_iff.mpr hfinal, hagree⟩

end
end Mettapedia.GraphTheory.FourColor.LongPathKempeLifting
