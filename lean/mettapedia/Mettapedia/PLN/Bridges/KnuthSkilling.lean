import Mettapedia.PLN.Evidence.BinaryEvidence
import KnuthSkilling.Core.HeytingValuation
import KnuthSkilling.Core.HeytingBounds
import KnuthSkilling.Core.HeytingIntervalRepresentation

/-!
# Evidence order, complements and scalar readouts

Coordinatewise evidence has incomparable elements. This does not establish
non-Booleanity: Boolean lattices can also be incomparable. Failure of a complement
for `(1,0)` proves the stronger claim separately. Strength is not monotone in the
information order, so it cannot serve as an order-reflecting scalar representation.
-/

namespace Mettapedia.PLN.Bridges.KnuthSkilling
open Mettapedia.PLN.Evidence _root_.KnuthSkilling.Heyting

def evidence_3_2 : BinaryEvidence := ⟨3, 2⟩
def evidence_2_3 : BinaryEvidence := ⟨2, 3⟩

theorem not_3_2_le_2_3 : ¬(evidence_3_2 ≤ evidence_2_3) := by
  intro h
  have hh : (3 : ENNReal) ≤ 2 := h.1
  norm_num at hh

theorem not_2_3_le_3_2 : ¬(evidence_2_3 ≤ evidence_3_2) := by
  intro h
  have hh : (3 : ENNReal) ≤ 2 := h.2
  norm_num at hh

theorem evidence_incomparable :
    ¬(evidence_3_2 ≤ evidence_2_3) ∧ ¬(evidence_2_3 ≤ evidence_3_2) :=
  ⟨not_3_2_le_2_3, not_2_3_le_3_2⟩

theorem evidence_not_total_order : ¬(∀ e₁ e₂ : BinaryEvidence, e₁ ≤ e₂ ∨ e₂ ≤ e₁) := by
  intro h
  exact (h evidence_3_2 evidence_2_3).elim not_3_2_le_2_3 not_2_3_le_3_2

theorem evidence_has_incomparable : ∃ e₁ e₂ : BinaryEvidence, Incomparable e₁ e₂ :=
  ⟨evidence_3_2, evidence_2_3, evidence_incomparable⟩

/-- Any complement would have positive coordinate both zero and infinite. -/
theorem one_zero_has_no_complement : ¬∃ c : BinaryEvidence, IsCompl (⟨1, 0⟩ : BinaryEvidence) c := by
  rintro ⟨c, hc⟩
  have hi := congrArg BinaryEvidence.pos hc.inf_eq_bot
  have hs := congrArg BinaryEvidence.pos hc.sup_eq_top
  change min (1 : ENNReal) c.pos = 0 at hi
  change max (1 : ENNReal) c.pos = ⊤ at hs
  have hz : c.pos = 0 := by
    rcases le_total (1 : ENNReal) c.pos with h | h
    · rw [min_eq_left h] at hi; norm_num at hi
    · simpa only [min_eq_right h] using hi
  rw [hz, max_eq_left (show (0 : ENNReal) ≤ 1 from zero_le)] at hs
  norm_num at hs

/-- Non-Booleanity is witnessed by missing complements, independently of incomparability. -/
theorem pln_evidence_not_boolean : ¬ComplementedLattice BinaryEvidence := by
  intro h
  let := h
  exact one_zero_has_no_complement (exists_isCompl (⟨1, 0⟩ : BinaryEvidence))

/-- Adding negative evidence increases information while decreasing the strength readout. -/
theorem strength_not_monotone : ¬Monotone BinaryEvidence.strengthAsPoint := by
  intro h
  have hh := h (show (⟨1, 0⟩ : BinaryEvidence) ≤ ⟨1, 1⟩ from ⟨le_rfl, by norm_num⟩)
  norm_num [BinaryEvidence.strengthAsPoint, BinaryEvidence.toStrength, BinaryEvidence.total] at hh

end Mettapedia.PLN.Bridges.KnuthSkilling
