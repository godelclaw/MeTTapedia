import Mettapedia.GraphTheory.FourColor.IncidenceKempeEnds

/-!
# Repairing a three-contact colouring constraint

The constraint q = r or q differs from s can always be arranged at three
distinct contacts by at most one physical Kempe switch. In the forbidden
case, the selected component through the third contact cannot also end
at both of the other contacts.
-/

namespace Mettapedia.GraphTheory.FourColor.IncidenceKempeSwitch

open GoertzelV24ForkInterfaceSupport

noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
variable {inc : E → Finset V} {S : Finset E}

/-- The revised witness is either unchanged or the result of one actual
component switch, and satisfies the exact three-contact constraint. -/
theorem exists_compatible_three_contacts
    (C : (graph inc S).Coloring (Fin 3)) (hsize : ∀ x : E, (inc x).card ≤ 2)
    {u t w : V} (hut : u ≠ t) (huw : u ≠ w) (htw : t ≠ w)
    (r s q : Fin 3)
    (hu : ∀ k, k ∉ profile inc S C u ↔ k = r)
    (ht : ∀ k, k ∉ profile inc S C t ↔ k = s)
    (hw : ∀ k, k ∉ profile inc S C w ↔ k = q) :
    ∃ D : (graph inc S).Coloring (Fin 3),
      (D = C ∨ ∃ a b : Fin 3, ∃ K : (C.bicoloredSubgraph a b).ConnectedComponent,
        D = C.swapOnKempeComponent a b K) ∧
      ∃ r' s' q' : Fin 3,
        (∀ k, k ∉ profile inc S D u ↔ k = r') ∧
        (∀ k, k ∉ profile inc S D t ↔ k = s') ∧
        (∀ k, k ∉ profile inc S D w ↔ k = q') ∧ (q' = r' ∨ q' ≠ s') := by
  classical
  by_cases hgood : q = r ∨ q ≠ s
  · exact ⟨C, Or.inl rfl, r, s, q, hu, ht, hw, hgood⟩
  have hqr : q ≠ r := fun h => hgood (Or.inl h)
  have hqs : q = s := by by_contra h; exact hgood (Or.inr h)
  subst s
  obtain ⟨K, hKw⟩ := exists_component_touches_of_missing C q r hw hqr
  have hnot : ¬ (Touches C q r K u ∧ Touches C q r K t) := by
    rintro ⟨hKu, hKt⟩
    have hbound := terminal_contacts_card_le_two C q r hsize K {u, t, w}
      (by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · exact Or.inr ((hu r).mpr rfl)
        · exact Or.inl ((ht q).mpr rfl)
        · exact Or.inl ((hw q).mpr rfl))
      (by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · exact hKu
        · exact hKt
        · exact hKw)
    have hcard : ({u, t, w} : Finset V).card = 3 := by simp [hut, huw, htw]
    omega
  refine ⟨C.swapOnKempeComponent q r K, Or.inr ⟨q, r, K, rfl⟩,
    (if Touches C q r K u then q else r),
    (if Touches C q r K t then r else q), r, ?_, ?_, ?_, ?_⟩
  · intro k
    simpa only [Equiv.swap_apply_right] using missing_switch C q r K hu k
  · intro k
    simpa only [Equiv.swap_apply_left] using missing_switch C q r K ht k
  · intro k
    simpa only [hKw, ite_true, Equiv.swap_apply_left] using missing_switch C q r K hw k
  · by_cases hKt : Touches C q r K t
    · have hKu : ¬ Touches C q r K u := fun h => hnot ⟨h, hKt⟩
      exact Or.inl (by rw [ite_eq_right hKu])
    · exact Or.inr (by simpa only [ite_eq_right hKt] using Ne.symm hqr)

end
end Mettapedia.GraphTheory.FourColor.IncidenceKempeSwitch
