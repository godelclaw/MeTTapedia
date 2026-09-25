import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlatCheck

/-!
# Checking one page in chunks

A page of the checker glues one member of the certificate with every member.
A heavy page can be checked in chunks: the partners with indices in
`[a, a + b)` for consecutive blocks.  Each chunk is a separate kernel
evaluation.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

/-- The pairs of one page with the partners of indices `a` to `a + b - 1`. -/
def pairsOk (bound : ℕ) (C : List FCode) (L : FCode) (a b : ℕ) : Bool :=
  ((C.drop a).take b).all (pairOk bound C L)

theorem all_of_chunks {α : Type*} (P : α → Bool) (step : ℕ) (hstep : 0 < step) :
    ∀ (l : List α), (∀ t, t * step < l.length → ((l.drop (t * step)).take step).all P = true) →
      l.all P = true := by
  suffices H : ∀ n (l : List α), l.length ≤ n →
      (∀ t, t * step < l.length → ((l.drop (t * step)).take step).all P = true) →
        l.all P = true from fun l => H l.length l le_rfl
  intro n
  induction n with
  | zero =>
      intro l hl _
      rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)]
      rfl
  | succ n ih =>
      intro l hl h
      by_cases hl0 : l.length = 0
      · rw [List.length_eq_zero_iff.mp hl0]; rfl
      · rw [← List.take_append_drop step l, List.all_append, Bool.and_eq_true]
        refine ⟨?_, ?_⟩
        · have := h 0 (by rw [Nat.zero_mul]; omega)
          simpa using this
        · apply ih
          · rw [List.length_drop]; omega
          · intro t ht
            have := h (t + 1) (by
              rw [List.length_drop] at ht; rw [Nat.add_mul, Nat.one_mul]; omega)
            rw [List.drop_drop]
            convert this using 3
            ring_nf

/-- **A page from its chunks.** -/
theorem pageOk_of_chunks {bound : ℕ} {C : List FCode} {L : FCode} (step : ℕ) (hstep : 0 < step)
    (h : ∀ t, t * step < C.length → pairsOk bound C L (t * step) step = true) :
    pageOk bound C L = true :=
  all_of_chunks _ step hstep C h

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
