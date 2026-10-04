import MettapediaFourColor.KempeIntervalMatching

/-!
# Adaptive repair using an actual noncrossing component matching

Interval exclusion selects one chord of the supplied exterior matching.
Switching that chord retains the original chromogram. The terminal
predicate may carry a whole graph colouring or another repair obligation.
-/

namespace FourColor.KempeIntervalRepair

open Color KempeMatchingChromogram KempeIntervalMatching

variable {n : ℕ}

def switch (c : Fin n → Color) (a b i : Fin n) : Color :=
  if i = a ∨ i = b then EdgePerm.e132 (c i) else c i

private theorem swap_eq_one (c : Color) : EdgePerm.e132 c = c1 ↔ c = c1 := by
  cases c <;> decide

private theorem swap_ne_zero (c : Color) : c ≠ 0 → EdgePerm.e132 c ≠ 0 := by
  cases c <;> decide

theorem gram_switch (mate : Fin n → Fin n) (c : Fin n → Color)
    (hinv : Function.Involutive mate) (a : Fin n) :
    gram mate (switch c a (mate a)) = gram mate c := by
  apply congrArg List.ofFn
  funext i
  have same : (i = a ∨ i = mate a) ↔ (mate i = a ∨ mate i = mate a) := by
    constructor
    · rintro (rfl | rfl)
      · exact Or.inr rfl
      · exact Or.inl (hinv a)
    · rintro (h | h)
      · exact Or.inr ((hinv i).symm.trans (congrArg mate h))
      · exact Or.inl (hinv.injective h)
  have eq : switch c a (mate a) i = switch c a (mate a) (mate i) ↔ c i = c (mate i) := by
    by_cases h : i = a ∨ i = mate a
    · simp only [switch, ite_eq_left h, ite_eq_left (same.mp h)]
      cases c i <;> cases c (mate i) <;> decide
    · simp [switch, h, not_congr same |>.mp h]
  simp only [eq]

/-- Exactly one whole component is switched, with the original matching retained. -/
theorem switch_matches (mate : Fin n → Fin n) (c : Fin n → Color)
    (hinv : Function.Involutive mate) (hnc : Noncrossing mate)
    (hz : ∀ i, c i ≠ 0) (hf : ∀ i, mate i = i ↔ c i = c1) (a : Fin n) :
    matchg [] (List.ofFn (switch c a (mate a))) (gram mate c) := by
  have nz : ∀ i, switch c a (mate a) i ≠ 0 := by
    intro i
    unfold switch
    split
    · exact swap_ne_zero _ (hz i)
    · exact hz i
  have fixed : ∀ i, mate i = i ↔ switch c a (mate a) i = c1 := by
    intro i
    rw [hf]
    unfold switch
    split
    · exact (swap_eq_one _).symm
    · rfl
  have h := (reconstruct mate (switch c a (mate a)) hinv hnc nz fixed).1
  rwa [gram_switch mate c hinv a] at h

def active (c : Fin n → Color) (i : ℕ) : Bool :=
  if h : i < n then (c ⟨i,h⟩).hi else false

def bad (good : Fin n → Fin n → Bool) (i j : ℕ) : Bool :=
  if hi : i < n then if hj : j < n then !good ⟨i,hi⟩ ⟨j,hj⟩ else false else false

/-- Successful pair choices are tested jointly by the interval rule. There is
no requirement that a single anchor work for every exterior matching. -/
theorem answer (c : Fin n → Color) (good : Fin n → Fin n → Bool)
    (P : List Color → Prop)
    (terminal : ∀ a b, good a b = true → P (List.ofFn (switch c a b)))
    (reject : possible (active c) (bad good) 0 n = false)
    (mate : Fin n → Fin n) (hinv : Function.Involutive mate) (hnc : Noncrossing mate)
    (hz : ∀ i, c i ≠ 0) (hf : ∀ i, mate i = i ↔ c i = c1) :
    ∃ a : Fin n, (c a).hi = true ∧ good a (mate a) = true ∧
      P (List.ofFn (switch c a (mate a))) ∧
      matchg [] (List.ofFn (switch c a (mate a))) (gram mate c) := by
  have closed : Closed (liftMate mate) 0 n := by
    intro i _ hi
    exact ⟨Nat.zero_le _, by simpa using liftMate_bound mate i (by omega)⟩
  have fixed : ∀ i, 0 ≤ i → i < 0 + n →
      (liftMate mate i = i ↔ active c i = false) := by
    intro i _ hi
    have bound : i < n := by omega
    have h : (mate ⟨i,bound⟩).val = i ↔ c ⟨i,bound⟩ = c1 :=
      Fin.ext_iff.symm.trans (hf ⟨i,bound⟩)
    have z := hz ⟨i,bound⟩
    simp only [liftMate, active, dite_eq_left bound, h]
    cases hc : c ⟨i,bound⟩ <;> simp_all
  obtain ⟨i, _, hi, ha, hg⟩ := successful_chord (liftMate mate)
    (liftMate_involutive mate hinv) (liftMate_noncrossing mate hnc)
    (active c) (bad good) 0 n closed fixed reject
  have bound : i < n := by omega
  let a : Fin n := ⟨i,bound⟩
  have hgood : good a (mate a) = true := by
    simpa [bad, liftMate, bound, a] using hg
  refine ⟨a, ?_, hgood, terminal a (mate a) hgood,
    switch_matches mate c hinv hnc hz hf a⟩
  simpa [active, bound, a] using ha

end FourColor.KempeIntervalRepair
