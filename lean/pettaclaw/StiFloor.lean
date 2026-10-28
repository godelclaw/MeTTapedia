/-!
# StiFloor — Invariant B: floor tiebreak by facts of record

The STI claim-state specification developed on 2026-08-19 states:
scalar STI may hit a rounding floor f > 0 and tie. Ranking at the floor MUST NOT
use salience s_i. Tiebreak key: (last injection time, then bundle creation time)
— both facts of record, not claims. Steadfastness analogue (GOLEM nugget 2): a
bundle with zero injection since boot promotes nothing.

Self-contained (no Mathlib), beside StiMass.lean.
-/

namespace StiFloor

structure Facts where
  lastInj : Nat
  created : Nat

def outranks (a b : Facts) : Prop :=
  b.lastInj < a.lastInj ∨ (a.lastInj = b.lastInj ∧ b.created < a.created)

theorem outranks_irrefl (a : Facts) : ¬ outranks a a := by
  rintro (h | ⟨-, h⟩) <;> omega

theorem outranks_asymm {a b : Facts} : outranks a b → ¬ outranks b a := by
  intro h1 h2
  simp only [outranks] at h1 h2
  omega

theorem outranks_trans {a b c : Facts} : outranks a b → outranks b c → outranks a c := by
  intro h1 h2
  simp only [outranks] at h1 h2 ⊢
  omega

theorem outranks_total (a b : Facts) : outranks a b ∨ outranks b a ∨ a = b := by
  rcases Nat.lt_or_ge b.lastInj a.lastInj with h | h
  · exact Or.inl (Or.inl h)
  rcases Nat.lt_or_ge a.lastInj b.lastInj with h2 | h2
  · exact Or.inr (Or.inl (Or.inl h2))
  have heq : a.lastInj = b.lastInj := Nat.le_antisymm h h2
  rcases Nat.lt_or_ge b.created a.created with hc | hc
  · exact Or.inl (Or.inr ⟨heq, hc⟩)
  rcases Nat.lt_or_ge a.created b.created with hc2 | hc2
  · exact Or.inr (Or.inl (Or.inr ⟨heq.symm, hc2⟩))
  have hceq : a.created = b.created := Nat.le_antisymm hc hc2
  obtain ⟨al, ac⟩ := a
  obtain ⟨bl, bc⟩ := b
  simp_all

theorem injected_outranks_never {a b : Facts} (ha : 0 < a.lastInj) (hb : b.lastInj = 0) :
    outranks a b :=
  Or.inl (by omega)

end StiFloor

#print axioms StiFloor.outranks_irrefl
#print axioms StiFloor.outranks_trans
#print axioms StiFloor.outranks_total
#print axioms StiFloor.injected_outranks_never
