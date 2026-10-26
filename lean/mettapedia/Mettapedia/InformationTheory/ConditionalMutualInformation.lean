import Mettapedia.InformationTheory.MarkovProjection

/-!
# Conditional information along finite paths

The general divergence laws live in `FiniteDivergence`; the Markov projection
and its conditional-information identity live in `MarkovProjection`.
Here the information lost at each hop adds exactly to the divergence from the
joint path law to its Markov-chain projection. Factorization through the middle
coordinate supplies a sufficient condition for zero loss.
-/

namespace Mettapedia.InformationTheory.FiniteRV

open Real Finset BigOperators

/-! ## Hop additivity along a path

A path is a map `Fin (n+1) → X`.  Hop `i` compares the joint law of the prefix `X_{<i}`, the
current state `X_i` and the next state `X_{i+1}`; its conditional mutual information
`I(X_{i+1} ; X_{<i} | X_i)` is what the Markov assumption at that hop ignores.  Summing over
all hops gives exactly the divergence from the joint law to the Markov chain with the same
one-step transition laws (`sum_hopCondMutualInfo_eq_klSum_pathMarkov`).  Since every summand is
nonnegative, the losses of the hops add and never cancel.
-/

section Paths

variable {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}

/-- Restriction of a path to the indices `≤ j`. -/
def prefixLE (j : Fin (n + 1)) (x : Fin (n + 1) → X) : {k : Fin (n + 1) // k ≤ j} → X :=
  fun k => x k.1

/-- Restriction of a path to the indices `< j`. -/
def prefixLT (j : Fin (n + 1)) (x : Fin (n + 1) → X) : {k : Fin (n + 1) // k < j} → X :=
  fun k => x k.1

omit [Fintype X] [DecidableEq X] in
theorem prefixLE_eq_iff (j : Fin (n + 1)) (x y : Fin (n + 1) → X) :
    prefixLE j y = prefixLE j x ↔ ∀ k, k ≤ j → y k = x k := by
  exact ⟨fun h k hk => congrFun h ⟨k, hk⟩, fun h => funext fun k => h k.1 k.2⟩

omit [Fintype X] [DecidableEq X] in
theorem prefixLT_eq_iff (j : Fin (n + 1)) (x y : Fin (n + 1) → X) :
    prefixLT j y = prefixLT j x ↔ ∀ k, k < j → y k = x k := by
  exact ⟨fun h k hk => congrFun h ⟨k, hk⟩, fun h => funext fun k => h k.1 k.2⟩

omit [Fintype X] [DecidableEq X] in
theorem prefixLE_last_injective :
    Function.Injective (prefixLE (Fin.last n) : (Fin (n + 1) → X) → _) := by
  intro x y h
  funext k
  exact (prefixLE_eq_iff (Fin.last n) y x).1 h k (Fin.le_last k)

omit [Fintype X] [DecidableEq X] in
theorem prefixLE_zero_eq_iff (x y : Fin (n + 1) → X) :
    prefixLE 0 y = prefixLE 0 x ↔ y 0 = x 0 := by
  simp [prefixLE_eq_iff]

omit [Fintype X] [DecidableEq X] in
/-- Fibre identity behind hop `i`: knowing `X_{<i}`, `X_i`, `X_{i+1}` is knowing `X_{≤ i+1}`. -/
theorem hop_law3_fiber_iff (i : Fin n) (x y : Fin (n + 1) → X) :
    (prefixLT i.castSucc y, y i.castSucc, y i.succ) =
      (prefixLT i.castSucc x, x i.castSucc, x i.succ) ↔
    prefixLE i.succ y = prefixLE i.succ x := by
  rw [Prod.mk.injEq, Prod.mk.injEq, prefixLT_eq_iff, prefixLE_eq_iff]
  constructor
  · rintro ⟨hlt, hi, hi1⟩ k hk
    by_cases hki : k < i.castSucc
    · exact hlt k hki
    · have cases : k = i.castSucc ∨ k = i.succ := by
        simp only [Fin.le_def, Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hk hki
        have : k.val = i.castSucc.val ∨ k.val = i.succ.val := by simp; omega
        exact this.imp Fin.ext Fin.ext
      rcases cases with rfl | rfl <;> assumption
  · intro h
    exact ⟨fun k hk => h k ((Nat.le_of_lt hk).trans (Nat.le_succ _)),
      h i.castSucc (Nat.le_succ _), h i.succ le_rfl⟩

omit [Fintype X] [DecidableEq X] in
/-- Fibre identity: knowing `X_{<i}` and `X_i` is knowing `X_{≤ i}`. -/
theorem hop_law2_fiber_iff (i : Fin n) (x y : Fin (n + 1) → X) :
    (prefixLT i.castSucc y, y i.castSucc) = (prefixLT i.castSucc x, x i.castSucc) ↔
    prefixLE i.castSucc y = prefixLE i.castSucc x := by
  rw [Prod.mk.injEq, prefixLT_eq_iff, prefixLE_eq_iff]
  constructor
  · rintro ⟨hlt, hi⟩ k hk
    rcases lt_or_eq_of_le hk with hlt' | heq
    · exact hlt k hlt'
    · rw [heq]; exact hi
  · intro h
    exact ⟨fun k hk => h k hk.le, h i.castSucc le_rfl⟩

omit [Fintype X] [DecidableEq X] in
/-- Telescoping sum over `Fin n`. -/
theorem fin_sum_succ_sub_castSucc (F : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (F i.succ - F i.castSucc) = F (Fin.last n) - F 0 := by
  rw [Finset.sum_sub_distrib]
  have hfirst := Fin.sum_univ_succ F
  have hlast := Fin.sum_univ_castSucc F
  linarith

/-- Conditional mutual information ignored by the Markov assumption at hop `i`:
`I(X_{i+1} ; X_{<i} | X_i)`. -/
noncomputable def hopCondMutualInfo (p : (Fin (n + 1) → X) → ℝ) (i : Fin n) : ℝ :=
  condMutualInfo p (prefixLT i.castSucc) (fun x => x i.castSucc) (fun x => x i.succ)

/-- The Markov chain with the initial law and the one-step transition laws of `p`. -/
noncomputable def pathMarkov (p : (Fin (n + 1) → X) → ℝ) (x : Fin (n + 1) → X) : ℝ :=
  pushforward p (fun y => y 0) (x 0) *
    ∏ i : Fin n, (if pushforward p (fun y => y i.castSucc) (x i.castSucc) = 0 then 0
      else law2 p (fun y => y i.castSucc) (fun y => y i.succ) (x i.castSucc, x i.succ) /
        pushforward p (fun y => y i.castSucc) (x i.castSucc))

/-- Hop additivity: `∑ᵢ I(X_{i+1}; X_{<i} | X_i) = KL(P ∥ P_Markov)`. -/
theorem sum_hopCondMutualInfo_eq_klSum_pathMarkov (p : (Fin (n + 1) → X) → ℝ)
    (hp : ∀ x, 0 ≤ p x) :
    ∑ i : Fin n, hopCondMutualInfo p i = klSum p (pathMarkov p) := by
  unfold hopCondMutualInfo
  simp only [condMutualInfo_eq_sum_omega]
  rw [Finset.sum_comm]
  unfold klSum klSumOn
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum]
  rcases (hp x).lt_or_eq with hpos | hzero
  · congr 1
    -- positivity of every law evaluated on the realised path
    have hm : ∀ j : Fin (n + 1), 0 < pushforward p (prefixLE j) (prefixLE j x) :=
      fun j => pushforward_pos_of_pos p hp _ hpos
    have hP : ∀ j : Fin (n + 1), 0 < pushforward p (fun y => y j) (x j) :=
      fun j => pushforward_pos_of_pos p hp (fun y => y j) hpos
    have hL : ∀ i : Fin n,
        0 < law2 p (fun y => y i.castSucc) (fun y => y i.succ) (x i.castSucc, x i.succ) :=
      fun i => pushforward_pos_of_pos p hp (fun y => (y i.castSucc, y i.succ)) hpos
    -- the prefix laws appearing in the hop terms
    have hL3 : ∀ i : Fin n, law3 p (prefixLT i.castSucc) (fun y => y i.castSucc)
        (fun y => y i.succ) (prefixLT i.castSucc x, x i.castSucc, x i.succ) =
        pushforward p (prefixLE i.succ) (prefixLE i.succ x) :=
      fun i => pushforward_congr_fiber p _ _ x (fun y => hop_law3_fiber_iff i x y)
    have hL2A : ∀ i : Fin n, law2 p (prefixLT i.castSucc) (fun y => y i.castSucc)
        (prefixLT i.castSucc x, x i.castSucc) =
        pushforward p (prefixLE i.castSucc) (prefixLE i.castSucc x) :=
      fun i => pushforward_congr_fiber p _ _ x (fun y => hop_law2_fiber_iff i x y)
    simp_rw [hL3, hL2A,
      Real.log_div (mul_pos (hm _) (hP _)).ne' (mul_pos (hm _) (hL _)).ne',
      Real.log_mul (hm _).ne' (hP _).ne', Real.log_mul (hm _).ne' (hL _).ne',
      add_sub_add_comm]
    rw [Finset.sum_add_distrib,
      fin_sum_succ_sub_castSucc (fun j => Real.log (pushforward p (prefixLE j) (prefixLE j x)))]
    have hlast : pushforward p (prefixLE (Fin.last n)) (prefixLE (Fin.last n) x) = p x :=
      pushforward_of_injective p _ prefixLE_last_injective x
    have hzero' : pushforward p (prefixLE 0) (prefixLE 0 x) =
        pushforward p (fun y => y 0) (x 0) :=
      pushforward_congr_fiber p _ _ x (fun y => prefixLE_zero_eq_iff x y)
    rw [hlast, hzero']
    -- expand the logarithm of the Markov chain
    unfold pathMarkov
    simp_rw [if_neg (hP _).ne']
    have hprod : 0 < ∏ i : Fin n,
        law2 p (fun y => y i.castSucc) (fun y => y i.succ) (x i.castSucc, x i.succ) /
          pushforward p (fun y => y i.castSucc) (x i.castSucc) :=
      Finset.prod_pos fun i _ => div_pos (hL i) (hP _)
    rw [Real.log_div hpos.ne' (mul_pos (hP 0) hprod).ne', Real.log_mul (hP 0).ne' hprod.ne',
      Real.log_prod (fun i _ => (div_pos (hL i) (hP _)).ne')]
    rw [Finset.sum_congr rfl (fun i _ => Real.log_div (hL i).ne' (hP i.castSucc).ne'),
      Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    ring
  · rw [← hzero]
    simp

theorem hopCondMutualInfo_nonneg (p : (Fin (n + 1) → X) → ℝ) (hp : ∀ x, 0 ≤ p x) (i : Fin n) :
    0 ≤ hopCondMutualInfo p i :=
  condMutualInfo_nonneg p hp _ _ _

/-- The divergence to the Markov chain is nonnegative and dominates every single hop's
conditional mutual information: no hop's loss is cancelled by another. -/
theorem hopCondMutualInfo_le_klSum_pathMarkov (p : (Fin (n + 1) → X) → ℝ) (hp : ∀ x, 0 ≤ p x)
    (i : Fin n) : hopCondMutualInfo p i ≤ klSum p (pathMarkov p) := by
  rw [← sum_hopCondMutualInfo_eq_klSum_pathMarkov p hp]
  exact Finset.single_le_sum (f := fun i => hopCondMutualInfo p i)
    (fun j _ => hopCondMutualInfo_nonneg p hp j) (Finset.mem_univ i)

end Paths

/-! ## Factorization through the middle coordinate

The discrete Bayesian-network reading of the positive canary: when the joint weight on
`α × β × γ` factorizes through the middle coordinate, `p (a,b,c) = φ a b * ψ b c`, the outer
coordinates are conditionally independent given the middle one, so the Markov projection is
exact and every chain loss vanishes.  This is the factorization form used by the discrete local
Markov development in `Mettapedia.ProbabilityTheory.BayesianNetworks`. -/

section Factorization

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] in
/-- The coordinate maps of a triple recover the triple. -/
theorem coordinates_injective :
    Function.Injective (fun x : α × β × γ => (x.1, x.2.1, x.2.2)) := by
  intro x y h
  exact h

/-- Factorization through the middle coordinate gives `A ⊥ C | B`. -/
theorem condIndep_of_factorization (φ : α → β → ℝ) (ψ : β → γ → ℝ) :
    CondIndep (fun x : α × β × γ => φ x.1 x.2.1 * ψ x.2.1 x.2.2)
      (fun x => x.1) (fun x => x.2.1) (fun x => x.2.2) := by
  set p : α × β × γ → ℝ := fun x => φ x.1 x.2.1 * ψ x.2.1 x.2.2 with hpdef
  have h3 : ∀ x, law3 p (fun x => x.1) (fun x => x.2.1) (fun x => x.2.2) x = p x := fun x =>
    pushforward_of_injective p _ coordinates_injective x
  have hfg : ∀ a b, law2 p (fun x => x.1) (fun x => x.2.1) (a, b) = φ a b * ∑ c, ψ b c := by
    intro a b
    rw [← sum_law3_right p (fun x => x.1) (fun x => x.2.1) (fun x => x.2.2) a b, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => h3 (a, b, c)
  have hgh : ∀ b c, law2 p (fun x => x.2.1) (fun x => x.2.2) (b, c) = (∑ a, φ a b) * ψ b c := by
    intro b c
    rw [← sum_law3_left p (fun x => x.1) (fun x => x.2.1) (fun x => x.2.2) b c, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => h3 (a, b, c)
  have hg : ∀ b, pushforward p (fun x => x.2.1) b = (∑ a, φ a b) * ∑ c, ψ b c := by
    intro b
    rw [← sum_law2_left p (fun x => x.1) (fun x => x.2.1) b, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => hfg a b
  intro x
  rw [h3 x, hg x.2.1, hfg x.1 x.2.1, hgh x.2.1 x.2.2]
  simp only [hpdef]
  ring

end Factorization

end Mettapedia.InformationTheory.FiniteRV
