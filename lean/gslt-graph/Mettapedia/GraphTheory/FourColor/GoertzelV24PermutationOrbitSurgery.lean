import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# Permutation orbit surgery: the transposition split/merge law

The generic combinatorial-map fact underlying "an edge with the same face on
both sides is a bridge" is a pure permutation statement: multiplying a
permutation by a transposition changes its orbit count by exactly one —
splitting the orbit through the transposed points when they share an orbit,
merging their two orbits when they do not.

This module proves that law for the orbit count used throughout the face
machinery (`Quotient (Equiv.Perm.SameCycle.setoid ·)`, fixed points
included).  Mathlib has the sign-parity shadow of this fact but not the
count itself.  Everything here is finite-walk combinatorics: first-return
minimality along an orbit, one-step orbit comparison, and a fiberwise count
of the orbit quotients.

The two headline results:

* `orbitCount_swap_mul_of_sameCycle` — if `a ≠ b` lie on one `σ`-orbit then
  `swap a b * σ` has exactly one more orbit than `σ`;
* `orbitCount_swap_mul_of_not_sameCycle` — if they lie on different
  `σ`-orbits then `swap a b * σ` has exactly one fewer.

The merge law is the split law applied to `swap a b * σ`, since the swap is
an involution; only the split side needs the counting argument.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PermutationOrbitSurgery

open Equiv Equiv.Perm

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable instance orbitQuotientFintype (σ : Perm D) :
    Fintype (Quotient (SameCycle.setoid σ)) :=
  Fintype.ofFinite _

/-- The number of orbits of a permutation, fixed points included: vertices,
edges, and faces of a combinatorial map are all counts of this shape. -/
noncomputable def orbitCount (σ : Perm D) : ℕ :=
  Fintype.card (Quotient (SameCycle.setoid σ))

omit [DecidableEq D] in
/-- Points on one orbit reach each other by a nonnegative power. -/
theorem exists_nat_pow_apply_eq {σ : Perm D} {x y : D}
    (h : σ.SameCycle x y) : ∃ n : ℕ, (σ ^ n) x = y := by
  obtain ⟨i, _, hi⟩ := h.exists_pow_eq'
  exact ⟨i, hi⟩

omit [Fintype D] [DecidableEq D] in
/-- A point whose power returns to start does so periodically. -/
theorem pow_mul_apply_eq_self {σ : Perm D} {p : ℕ} {x : D}
    (hfix : (σ ^ p) x = x) (q : ℕ) : (σ ^ (p * q)) x = x := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ, pow_add, Perm.mul_apply, hfix, ih]

omit [DecidableEq D] in
/-- If every single step of `π` stays inside a `σ`-orbit, then whole
`π`-orbits stay inside `σ`-orbits. -/
theorem sameCycle_mono_of_step {π σ : Perm D}
    (hstep : ∀ x : D, σ.SameCycle x (π x)) :
    ∀ {x y : D}, π.SameCycle x y → σ.SameCycle x y := by
  intro x y h
  obtain ⟨n, rfl⟩ := exists_nat_pow_apply_eq h
  clear h
  induction n with
  | zero => simpa using SameCycle.refl σ x
  | succ n ih =>
      have hpow : (π ^ (n + 1)) x = π ((π ^ n) x) := by
        rw [pow_succ', Perm.mul_apply]
      rw [hpow]
      exact ih.trans (hstep ((π ^ n) x))

section Split

variable {σ : Perm D} {a b : D}

omit [Fintype D] in
/-- One step of `swap a b * σ` stays inside a `σ`-orbit, provided `a` and
`b` share a `σ`-orbit. -/
theorem step_sameCycle_of_sameCycle (h : σ.SameCycle a b) (x : D) :
    σ.SameCycle x ((swap a b * σ) x) := by
  have hx : σ.SameCycle x (σ x) := ⟨1, by simp⟩
  rw [Perm.mul_apply]
  rcases eq_or_ne (σ x) a with ha | ha
  · rw [ha, swap_apply_left]
    exact (ha ▸ hx).trans h
  · rcases eq_or_ne (σ x) b with hb | hb
    · rw [hb, swap_apply_right]
      exact (hb ▸ hx).trans h.symm
    · rw [swap_apply_of_ne_of_ne ha hb]
      exact hx

/-- In the split case, orbits of `swap a b * σ` refine orbits of `σ`. -/
theorem sameCycle_of_swap_mul_sameCycle (h : σ.SameCycle a b) {x y : D}
    (hxy : (swap a b * σ).SameCycle x y) : σ.SameCycle x y :=
  sameCycle_mono_of_step (step_sameCycle_of_sameCycle h) hxy

/-- **Separation.**  When `a ≠ b` share a `σ`-orbit, the product
`swap a b * σ` puts them on different orbits: the walk from `a` closes back
to `a` strictly before it can reach `b`. -/
theorem not_swap_mul_sameCycle_of_sameCycle
    (hab : a ≠ b) (h : σ.SameCycle a b) :
    ¬ (swap a b * σ).SameCycle a b := by
  classical
  have hexists : ∃ n : ℕ, 0 < n ∧ (σ ^ n) a = b := by
    obtain ⟨i, hi⟩ := exists_nat_pow_apply_eq h
    refine ⟨i, ?_, hi⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact absurd (by simpa using hi) hab
    · exact hpos
  obtain ⟨m, hm_min, hm_pos, hm_eq⟩ :
      ∃ m, (∀ k < m, ¬(0 < k ∧ (σ ^ k) a = b)) ∧ 0 < m ∧ (σ ^ m) a = b :=
    ⟨Nat.find hexists, fun k hk => Nat.find_min hexists hk,
      (Nat.find_spec hexists).1, (Nat.find_spec hexists).2⟩
  -- no earlier power of σ reaches b
  have hbefore : ∀ i < m, (σ ^ i) a ≠ b := by
    intro i hi hib
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact hab (by simpa using hib)
    · exact hm_min i hi ⟨hpos, hib⟩
  -- the walk of swap a b * σ from a stays among the first m powers of σ
  have hwalk : ∀ n : ℕ, ∃ i < m, ((swap a b * σ) ^ n) a = (σ ^ i) a := by
    intro n
    induction n with
    | zero => exact ⟨0, hm_pos, by simp⟩
    | succ n ih =>
        obtain ⟨i, hi, hstep⟩ := ih
        have hpow : ((swap a b * σ) ^ (n + 1)) a =
            (swap a b) (σ ((σ ^ i) a)) := by
          rw [pow_succ', Perm.mul_apply, hstep, Perm.mul_apply]
        have hsigma : σ ((σ ^ i) a) = (σ ^ (i + 1)) a := by
          rw [pow_succ', Perm.mul_apply]
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt hi) with hlast | hlt
        · -- the next power is exactly b; the swap folds it back to a
          refine ⟨0, hm_pos, ?_⟩
          have hlast' : i + 1 = m := hlast
          have hb : (σ ^ (i + 1)) a = b := by rw [hlast', hm_eq]
          rw [hpow, hsigma, hb, swap_apply_right]
          simp
        · -- strictly interior: the next power avoids both a and b
          refine ⟨i + 1, hlt, ?_⟩
          have hne_b : (σ ^ (i + 1)) a ≠ b := hbefore _ hlt
          have hne_a : (σ ^ (i + 1)) a ≠ a := by
            intro hret
            -- a period i+1 < m would put b at an earlier power
            have hperiod : ∀ q : ℕ, (σ ^ ((i + 1) * q)) a = a :=
              pow_mul_apply_eq_self hret
            have hdecomp : m % (i + 1) + (i + 1) * (m / (i + 1)) = m := by
              rw [Nat.add_comm]
              exact Nat.div_add_mod m (i + 1)
            have hearly : (σ ^ (m % (i + 1))) a = b := by
              have hsplit : (σ ^ m) a =
                  (σ ^ (m % (i + 1)))
                    ((σ ^ ((i + 1) * (m / (i + 1)))) a) := by
                rw [← Perm.mul_apply, ← pow_add, hdecomp]
              rw [hperiod] at hsplit
              rw [← hsplit, hm_eq]
            have hlt' : m % (i + 1) < m :=
              lt_of_lt_of_le (Nat.mod_lt _ (Nat.succ_pos i)) (le_of_lt hlt)
            exact hbefore _ hlt' hearly
          rw [hpow, hsigma, swap_apply_of_ne_of_ne hne_a hne_b]
  -- b is never visited, so it is not on the orbit of a
  intro hcontra
  obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq hcontra
  obtain ⟨i, hi, hwalk_n⟩ := hwalk n
  exact hbefore i hi (by rw [← hwalk_n, hn])

/-- **Coverage.**  Every point of the `σ`-orbit through `a` lies on the
`swap a b * σ`-orbit of `a` or of `b`; no relation between `a` and `b` is
needed. -/
theorem swap_mul_sameCycle_or {x : D} (hx : σ.SameCycle a x) :
    (swap a b * σ).SameCycle a x ∨ (swap a b * σ).SameCycle b x := by
  obtain ⟨n, rfl⟩ := exists_nat_pow_apply_eq hx
  clear hx
  induction n with
  | zero =>
      have hzero : (σ ^ 0) a = a := by simp
      rw [hzero]
      exact Or.inl (SameCycle.refl _ _)
  | succ n ih =>
      have hpow : (σ ^ (n + 1)) a = σ ((σ ^ n) a) := by
        rw [pow_succ', Perm.mul_apply]
      rcases eq_or_ne (σ ((σ ^ n) a)) a with hya | hya
      · rw [hpow, hya]
        exact Or.inl (SameCycle.refl _ _)
      · rcases eq_or_ne (σ ((σ ^ n) a)) b with hyb | hyb
        · rw [hpow, hyb]
          exact Or.inr (SameCycle.refl _ _)
        · have hstep : (swap a b * σ) ((σ ^ n) a) = σ ((σ ^ n) a) := by
            rw [Perm.mul_apply, swap_apply_of_ne_of_ne hya hyb]
          have hnext : ∀ z : D,
              (swap a b * σ).SameCycle z ((σ ^ n) a) →
              (swap a b * σ).SameCycle z ((σ ^ (n + 1)) a) := by
            intro z hz
            rw [hpow, ← hstep]
            exact hz.trans ⟨1, by simp⟩
          rcases ih with hcase | hcase
          · exact Or.inl (hnext a hcase)
          · exact Or.inr (hnext b hcase)

/-- Orbits of `σ` that avoid the transposed pair survive unchanged. -/
theorem swap_mul_sameCycle_of_sameCycle_avoiding {x : D}
    (hxa : ¬ σ.SameCycle x a) (hxb : ¬ σ.SameCycle x b) {y : D}
    (hxy : σ.SameCycle x y) : (swap a b * σ).SameCycle x y := by
  obtain ⟨n, rfl⟩ := exists_nat_pow_apply_eq hxy
  clear hxy
  have hagree : ∀ k : ℕ, ((swap a b * σ) ^ k) x = (σ ^ k) x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hxk : σ.SameCycle x ((σ ^ k) x) := ⟨k, by simp⟩
        have hne_a : σ ((σ ^ k) x) ≠ a := by
          intro hhit
          apply hxa
          have hreach : σ.SameCycle x (σ ((σ ^ k) x)) :=
            hxk.trans ⟨1, by simp⟩
          rwa [hhit] at hreach
        have hne_b : σ ((σ ^ k) x) ≠ b := by
          intro hhit
          apply hxb
          have hreach : σ.SameCycle x (σ ((σ ^ k) x)) :=
            hxk.trans ⟨1, by simp⟩
          rwa [hhit] at hreach
        rw [pow_succ', Perm.mul_apply, ih, Perm.mul_apply,
          swap_apply_of_ne_of_ne hne_a hne_b, ← Perm.mul_apply, ← pow_succ']
  exact ⟨n, by rw [zpow_natCast, hagree]⟩

end Split

/-- **The split law.**  Multiplying by a transposition of two distinct
points on one orbit increases the orbit count by exactly one. -/
theorem orbitCount_swap_mul_of_sameCycle (σ : Perm D) {a b : D}
    (hab : a ≠ b) (h : σ.SameCycle a b) :
    orbitCount (swap a b * σ) = orbitCount σ + 1 := by
  classical
  -- the refinement map between orbit quotients
  let F : Quotient (SameCycle.setoid (swap a b * σ)) →
      Quotient (SameCycle.setoid σ) :=
    Quotient.lift (fun x => Quotient.mk (SameCycle.setoid σ) x)
      (fun x y hxy => Quotient.sound (sameCycle_of_swap_mul_sameCycle h hxy))
  have hF_mk : ∀ x : D,
      F (Quotient.mk (SameCycle.setoid (swap a b * σ)) x) =
        Quotient.mk (SameCycle.setoid σ) x := fun _ => rfl
  -- count the finer quotient fiberwise over F
  have hcount :
      (Finset.univ :
          Finset (Quotient (SameCycle.setoid (swap a b * σ)))).card =
        ∑ c ∈ (Finset.univ : Finset (Quotient (SameCycle.setoid σ))),
          (Finset.univ.filter fun q => F q = c).card :=
    Finset.card_eq_sum_card_fiberwise (fun q _ => Finset.mem_univ (F q))
  set ca : Quotient (SameCycle.setoid σ) :=
    Quotient.mk (SameCycle.setoid σ) a with hca_def
  -- the distinguished fiber holds exactly the two split classes
  have hfiber_a :
      (Finset.univ.filter fun q => F q = ca) =
        {Quotient.mk (SameCycle.setoid (swap a b * σ)) a,
          Quotient.mk (SameCycle.setoid (swap a b * σ)) b} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hq
      obtain ⟨x, rfl⟩ := Quotient.exists_rep q
      rw [hF_mk] at hq
      have hx : σ.SameCycle a x := Quotient.exact hq.symm
      rcases swap_mul_sameCycle_or hx with hcase | hcase
      · exact Or.inl (Quotient.sound hcase.symm)
      · exact Or.inr (Quotient.sound hcase.symm)
    · rintro (rfl | rfl)
      · rw [hF_mk]
      · rw [hF_mk]
        exact Quotient.sound h.symm
  have hclasses_ne :
      (Quotient.mk (SameCycle.setoid (swap a b * σ)) a :
          Quotient (SameCycle.setoid (swap a b * σ))) ≠
        Quotient.mk (SameCycle.setoid (swap a b * σ)) b := by
    intro heq
    exact not_swap_mul_sameCycle_of_sameCycle hab h (Quotient.exact heq)
  have hfiber_a_card :
      (Finset.univ.filter fun q => F q = ca).card = 2 := by
    rw [hfiber_a]
    exact Finset.card_pair hclasses_ne
  -- every other fiber is a single class
  have hfiber_other :
      ∀ c : Quotient (SameCycle.setoid σ), c ≠ ca →
        (Finset.univ.filter fun q => F q = c).card = 1 := by
    intro c hc
    obtain ⟨x, rfl⟩ := Quotient.exists_rep c
    have hxa : ¬ σ.SameCycle x a := by
      intro hxa
      exact hc (Quotient.sound hxa)
    have hxb : ¬ σ.SameCycle x b := fun hxb => hxa (hxb.trans h.symm)
    rw [Finset.card_eq_one]
    refine ⟨Quotient.mk (SameCycle.setoid (swap a b * σ)) x, ?_⟩
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hq
      obtain ⟨y, rfl⟩ := Quotient.exists_rep q
      rw [hF_mk] at hq
      have hxy : σ.SameCycle x y := (Quotient.exact hq).symm
      exact Quotient.sound
        (swap_mul_sameCycle_of_sameCycle_avoiding hxa hxb hxy).symm
    · rintro rfl
      rw [hF_mk]
  -- assemble the sum: all fibers count one except the distinguished pair
  have hsum :
      ∑ c ∈ (Finset.univ : Finset (Quotient (SameCycle.setoid σ))),
          (Finset.univ.filter fun q => F q = c).card =
        Fintype.card (Quotient (SameCycle.setoid σ)) + 1 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ca), hfiber_a_card]
    have hones :
        ∑ c ∈ (Finset.univ :
            Finset (Quotient (SameCycle.setoid σ))).erase ca,
            (Finset.univ.filter fun q => F q = c).card =
          ((Finset.univ :
            Finset (Quotient (SameCycle.setoid σ))).erase ca).card := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl ?_
      intro c hc
      exact hfiber_other c (Finset.ne_of_mem_erase hc)
    rw [hones, Finset.card_erase_of_mem (Finset.mem_univ ca),
      ← Finset.card_univ]
    have hpos :
        0 < (Finset.univ :
          Finset (Quotient (SameCycle.setoid σ))).card :=
      Finset.card_pos.mpr ⟨ca, Finset.mem_univ ca⟩
    omega
  calc orbitCount (swap a b * σ)
      = (Finset.univ :
          Finset (Quotient (SameCycle.setoid (swap a b * σ)))).card :=
        Finset.card_univ.symm
    _ = Fintype.card (Quotient (SameCycle.setoid σ)) + 1 := by
        rw [hcount, hsum]
    _ = orbitCount σ + 1 := rfl

/-- The walk from `a` reaches `b` in the merge case: after a full period of
`a`'s own `σ`-orbit, the swap redirects the return step to `b`. -/
theorem swap_mul_sameCycle_of_not_sameCycle {σ : Perm D} {a b : D}
    (h : ¬ σ.SameCycle a b) : (swap a b * σ).SameCycle a b := by
  classical
  have hexists : ∃ n : ℕ, 0 < n ∧ (σ ^ n) a = a := by
    refine ⟨orderOf σ, orderOf_pos σ, ?_⟩
    rw [pow_orderOf_eq_one]
    rfl
  obtain ⟨p, hp_min, hp_pos, hp_eq⟩ :
      ∃ p, (∀ k < p, ¬(0 < k ∧ (σ ^ k) a = a)) ∧ 0 < p ∧ (σ ^ p) a = a :=
    ⟨Nat.find hexists, fun k hk => Nat.find_min hexists hk,
      (Nat.find_spec hexists).1, (Nat.find_spec hexists).2⟩
  have hinterior : ∀ n : ℕ, 0 < n → n < p → (σ ^ n) a ≠ a := by
    intro n hn hnp hret
    exact hp_min n hnp ⟨hn, hret⟩
  have hwalk : ∀ n < p, ((swap a b * σ) ^ n) a = (σ ^ n) a := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        have hlt : n < p := Nat.lt_of_succ_lt hn
        have hnext : σ ((σ ^ n) a) = (σ ^ (n + 1)) a := by
          rw [pow_succ', Perm.mul_apply]
        have hne_a : σ ((σ ^ n) a) ≠ a := by
          rw [hnext]
          exact hinterior (n + 1) (Nat.succ_pos n) hn
        have hne_b : σ ((σ ^ n) a) ≠ b := by
          intro hhit
          apply h
          have hto_pow : σ.SameCycle a ((σ ^ n) a) := ⟨n, by simp⟩
          have hone_step : σ.SameCycle ((σ ^ n) a) (σ ((σ ^ n) a)) :=
            ⟨1, by simp⟩
          have hreach := hto_pow.trans hone_step
          rwa [hhit] at hreach
        rw [pow_succ', Perm.mul_apply, ih hlt, Perm.mul_apply,
          swap_apply_of_ne_of_ne hne_a hne_b, ← Perm.mul_apply, ← pow_succ']
  have hfinal : ((swap a b * σ) ^ p) a = b := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 :=
      ⟨p - 1, (Nat.succ_pred_eq_of_pos hp_pos).symm⟩
    have hq : ((swap a b * σ) ^ q) a = (σ ^ q) a :=
      hwalk q (Nat.lt_succ_self q)
    have hreturn : σ ((σ ^ q) a) = a := by
      have hnext : σ ((σ ^ q) a) = (σ ^ (q + 1)) a := by
        rw [pow_succ', Perm.mul_apply]
      rw [hnext, hp_eq]
    rw [pow_succ', Perm.mul_apply, hq, Perm.mul_apply, hreturn,
      swap_apply_left]
  exact ⟨p, by rw [zpow_natCast, hfinal]⟩

/-- **The merge law.**  Multiplying by a transposition of two points on
different orbits decreases the orbit count by exactly one.  This is the
split law read through the swap involution. -/
theorem orbitCount_swap_mul_of_not_sameCycle (σ : Perm D) {a b : D}
    (hab : a ≠ b) (h : ¬ σ.SameCycle a b) :
    orbitCount σ = orbitCount (swap a b * σ) + 1 := by
  have hconn := swap_mul_sameCycle_of_not_sameCycle h
  have hsplit :=
    orbitCount_swap_mul_of_sameCycle (swap a b * σ) hab hconn
  rwa [swap_mul_self_mul] at hsplit

end GoertzelV24PermutationOrbitSurgery

end Mettapedia.GraphTheory.FourColor
