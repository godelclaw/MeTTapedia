import MettapediaFourColor.KempeChromogramMatching

/-!
# Two component choices in one retained exterior matching

A first chord switch does not discard the original component matching.
Interval exclusion either finds a successful single chord, or certifies
that the two prescribed anchor components admit a composed continuation.
The theorem is uniform in boundary length and retains the same exterior.
-/

namespace FourColor.KempeRetainedMatching

open Color KempeMatchingChromogram KempeIntervalRepair KempeIntervalMatching

variable {n : ℕ}

/-- Edges allowed when the mate of a specified anchor is fixed. -/
def pin (a p i j : Fin n) : Bool := decide ((i = a → j = p) ∧ (j = a → i = p))

theorem pin_mate (m : Fin n → Fin n) (hi : Function.Involutive m) (a i : Fin n) :
    pin a (m a) i (m i) = true := by
  simp only [pin, decide_eq_true_eq]
  constructor
  · intro h; subst i; rfl
  · intro h
    simpa only [hi i] using congrArg m h

/-- Failure of all single repairs, retaining both specified partners. -/
def allowed (single : Fin n → Fin n → Bool) (a p b q : Fin n) (i j : ℕ) : Bool :=
  if hi : i < n then if hj : j < n then
    !single ⟨i,hi⟩ ⟨j,hj⟩ && pin a p ⟨i,hi⟩ ⟨j,hj⟩ && pin b q ⟨i,hi⟩ ⟨j,hj⟩
  else false else false

/-- The actual matching is a witness for the interval recurrence whenever
all its edges satisfy the supplied constraint. -/
theorem possible_of_mate (c : Fin n → Color) (m : Fin n → Fin n)
    (hi : Function.Involutive m) (hn : Noncrossing m)
    (hz : ∀ i, c i ≠ 0) (hf : ∀ i, m i = i ↔ c i = c1)
    (ok : ℕ → ℕ → Bool) (he : ∀ i, c i ≠ c1 → ok i.val (m i).val = true) :
    possible (active c) ok 0 n = true := by
  apply possible_of_matching (liftMate m) (liftMate_involutive m hi)
    (liftMate_noncrossing m hn) (active c) ok 0 n
  · intro i _ bound
    exact ⟨Nat.zero_le _, by simpa using liftMate_bound m i (by omega)⟩
  · intro i _ bound
    have bound : i < n := by omega
    have h : (m ⟨i,bound⟩).val = i ↔ c ⟨i,bound⟩ = c1 := Fin.ext_iff.symm.trans (hf _)
    have z := hz ⟨i,bound⟩
    simp only [liftMate, active, dite_eq_left bound, h]
    cases hc : c ⟨i,bound⟩ <;> simp_all
  · intro i _ bound ha
    have bound : i < n := by omega
    have hne : c ⟨i,bound⟩ ≠ c1 := by
      simp only [active, dite_eq_left bound] at ha
      intro h; simp [h] at ha
    simpa only [liftMate, dite_eq_left bound] using he ⟨i,bound⟩ hne

/-- One or two component switches use the originally supplied matching.
Continuations can themselves be composed repairs in the same exterior. -/
theorem two_anchor_coclosure {P : List Color → Prop} (c : Fin n → Color)
    (hz : ∀ i, c i ≠ 0) (a b : Fin n) (ha : c a ≠ c1) (hb : c b ≠ c1)
    (single double : Fin n → Fin n → Bool)
    (one : ∀ i j, single i j = true → KempeCoclosure P (List.ofFn (switch c i j)))
    (two : ∀ p q, double p q = true →
      KempeCoclosure P (List.ofFn (switch (switch c a p) b q)))
    (reject : ∀ p q, double p q = false →
      possible (active c) (allowed single a p b q) 0 n = false) :
    KempeCoclosure P (List.ofFn c) := by
  classical
  intro outside hout hold
  obtain ⟨_, w, hw, hall⟩ := hout _ hold
  obtain ⟨m, hi, hn, hf, hs⟩ := KempeChromogramMatching.recover_stable c w hw
  by_cases found : ∃ i, c i ≠ c1 ∧ single i (m i) = true
  · obtain ⟨i, ha, good⟩ := found
    exact one i (m i) good outside hout (hall _ (hs c hw i ha))
  · have failed : ∀ i, c i ≠ c1 → single i (m i) = false := by
      intro i ha
      cases h : single i (m i) with
      | false => rfl
      | true => exact (found ⟨i,ha,h⟩).elim
    have success : double (m a) (m b) = true := by
      cases h : double (m a) (m b) with
      | true => rfl
      | false =>
        have yes := possible_of_mate c m hi hn hz hf (allowed single a (m a) b (m b))
          (fun i ha => by simp [allowed, failed i ha, pin_mate m hi])
        have no := reject (m a) (m b) h
        simp_all
    have first := hs c hw a ha
    have second := hs (switch c a (m a)) first b hb
    exact two (m a) (m b) success outside hout (hall _ second)

end FourColor.KempeRetainedMatching
