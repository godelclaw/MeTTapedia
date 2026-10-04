import MettapediaFourColor.KempeRetainedMatching

/-!
# Selecting two components from a retained set of anchors

The anchors all query one matching. Interval exclusion either supplies a
successful single component or two components selected from those anchors.
The number of boundary ports and the number of anchors are arbitrary.
Every continuation uses the original exterior predicate.
-/

namespace FourColor.KempeAnchorSelection

open Color KempeMatchingChromogram KempeIntervalRepair KempeRetainedMatching

variable {n k : ℕ}

def pins (a p : Fin k → Fin n) (i j : Fin n) : Bool :=
  (List.finRange k).all fun t =>
    (!(i == a t) || j == p t) && (!(j == a t) || i == p t)

theorem pins_mate (m : Fin n → Fin n) (hi : Function.Involutive m)
    (a : Fin k → Fin n) (i : Fin n) : pins a (fun t => m (a t)) i (m i) = true := by
  apply List.all_eq_true.mpr
  intro t _
  have backward : m i = a t → i = m (a t) := by
    intro h
    simpa only [hi i] using congrArg m h
  simp only [Bool.and_eq_true]
  constructor
  · by_cases h : i = a t <;> simp [h]
  · by_cases h : m i = a t
    · simp [backward h]
    · simp [h]

def allowed (single : Fin n → Fin n → Bool) (a p : Fin k → Fin n) (i j : ℕ) : Bool :=
  if hi : i < n then if hj : j < n then
    !single ⟨i,hi⟩ ⟨j,hj⟩ && pins a p ⟨i,hi⟩ ⟨j,hj⟩
  else false else false

def successful (double : Fin k → Fin k → Fin n → Fin n → Bool) (p : Fin k → Fin n) : Bool :=
  decide (∃ r t, double r t (p r) (p t) = true)

def crosses (i j u v : Fin n) : Bool := decide (
  (min i.val j.val < min u.val v.val ∧ min u.val v.val < max i.val j.val ∧
    max i.val j.val < max u.val v.val) ∨
  (min u.val v.val < min i.val j.val ∧ min i.val j.val < max u.val v.val ∧
    max u.val v.val < max i.val j.val))

/-- Necessary joint constraints discard impossible partner assignments before
the interval check. They do not assert existence of a complete matching. -/
def feasible (c : Fin n → Color) (a p : Fin k → Fin n) : Bool :=
  (List.finRange k).all fun t =>
    (!(p t == a t) && !(c (p t) == c1)) &&
      (List.finRange k).all fun r =>
        (!(p t == a r) || p r == a t) && !crosses (a t) (p t) (a r) (p r)

theorem feasible_mate (c : Fin n → Color) (m : Fin n → Fin n)
    (hi : Function.Involutive m) (hn : Noncrossing m)
    (hf : ∀ i, m i = i ↔ c i = c1) (a : Fin k → Fin n)
    (ha : ∀ t, c (a t) ≠ c1) : feasible c a (fun t => m (a t)) = true := by
  apply List.all_eq_true.mpr
  intro t _
  have ne : m (a t) ≠ a t := fun h => ha t ((hf (a t)).mp h)
  have active : c (m (a t)) ≠ c1 := by
    intro h
    have eq := (hf (m (a t))).mpr h
    rw [hi] at eq
    exact ne eq.symm
  simp only [Bool.and_eq_true]
  refine ⟨by simp [ne, active], ?_⟩
  apply List.all_eq_true.mpr
  intro r _
  have nc : crosses (a t) (m (a t)) (a r) (m (a r)) = false :=
    decide_eq_false (hn (a t) (a r))
  have backward : m (a t) = a r → m (a r) = a t := by
    intro h
    simpa only [hi (a t)] using (congrArg m h).symm
  simp only [nc, Bool.not_false, Bool.and_true]
  by_cases h : m (a t) = a r
  · simp [backward h]
  · simp [h]

theorem feasible_reindex {l : ℕ} (c : Fin n → Color) (a p : Fin k → Fin n)
    (f : Fin l → Fin k) (h : feasible c a p = true) :
    feasible c (a ∘ f) (p ∘ f) = true := by
  apply List.all_eq_true.mpr
  intro t _
  have ht := List.all_eq_true.mp h (f t) (List.mem_finRange (f t))
  simp only [Bool.and_eq_true] at ht ⊢
  refine ⟨ht.1, ?_⟩
  apply List.all_eq_true.mpr
  intro r _
  exact List.all_eq_true.mp ht.2 (f r) (List.mem_finRange (f r))

/-- The selected pair can depend on all retained anchor partners. This
does not replace their joint matching by independent partner possibilities. -/
theorem coclosure {P : List Color → Prop} (c : Fin n → Color)
    (hz : ∀ i, c i ≠ 0) (a : Fin k → Fin n) (ha : ∀ t, c (a t) ≠ c1)
    (single : Fin n → Fin n → Bool)
    (double : Fin k → Fin k → Fin n → Fin n → Bool)
    (one : ∀ i j, single i j = true → KempeCoclosure P (List.ofFn (switch c i j)))
    (two : ∀ r t p q, double r t p q = true →
      KempeCoclosure P (List.ofFn (switch (switch c (a r) p) (a t) q)))
    (reject : ∀ p, feasible c a p = true → successful double p = false →
      KempeIntervalMatching.possible (active c) (allowed single a p) 0 n = false) :
    KempeCoclosure P (List.ofFn c) := by
  classical
  intro outside hout hold
  obtain ⟨_,w,hw,hall⟩ := hout _ hold
  obtain ⟨m,hi,hn,hf,hs⟩ := KempeChromogramMatching.recover_stable c w hw
  by_cases found : ∃ i, c i ≠ c1 ∧ single i (m i) = true
  · obtain ⟨i,active,good⟩ := found
    exact one i (m i) good outside hout (hall _ (hs c hw i active))
  · have failed : ∀ i, c i ≠ c1 → single i (m i) = false := by
      intro i active
      cases h : single i (m i) with
      | false => rfl
      | true => exact (found ⟨i,active,h⟩).elim
    have yes := possible_of_mate c m hi hn hz hf (allowed single a (fun t => m (a t)))
      (fun i active => by simp [allowed, failed i active, pins_mate m hi])
    have good : successful double (fun t => m (a t)) = true := by
      cases h : successful double (fun t => m (a t)) with
      | true => rfl
      | false =>
        have no := reject (fun t => m (a t)) (feasible_mate c m hi hn hf a ha) h
        simp_all
    obtain ⟨r,t,hrt⟩ := (of_decide_eq_true good)
    have first := hs c hw (a r) (ha r)
    have second := hs (switch c (a r) (m (a r))) first (a t) (ha t)
    exact two r t (m (a r)) (m (a t)) hrt outside hout (hall _ second)

end FourColor.KempeAnchorSelection
