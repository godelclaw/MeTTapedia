import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedRegionBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24PermutationOrbitSurgery

/-!
# Restriction of boundary order through permutation surgery

First return to a smaller marked set is independent of an intermediate
restriction. A transposition preserves the order of marked points whenever
they lie on one cycle both before and after surgery. These are order, not
merely same-cycle, statements for the computed first-return permutation.
-/

namespace Mettapedia.GraphTheory.FourColor.PermutationFirstReturnRestriction

open Equiv Equiv.Perm
open GoertzelV24SeamFaceArc GoertzelV24BoundaryFaceReturnProfile
open GoertzelV24OrderedCutFaceReturnProfile GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24PermutationOrbitSurgery

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable section

/-- A positive orbit segment ending at its first marked point. The starting
point need not itself be marked. -/
def ReturnArc (p : Perm D) (hit : D → Prop) (x y : D) (n : ℕ) : Prop :=
  0 < n ∧ (p ^ n) x = y ∧ ∀ i, 0 < i → i < n → ¬ hit ((p ^ i) x)

theorem nextHit_eq_of_returnArc (p : Perm D) (hit : D → Prop)
    (x y : {d // hit d}) {n : ℕ} (h : ReturnArc p hit x.1 y.1 n) :
    nextHitPerm p hit x = y := by
  have hle := firstPositiveHitTime_le_of_hit p hit x.1 x.2 h.1 (h.2.1 ▸ y.2)
  have heq : firstPositiveHitTime p hit x.1 x.2 = n := by
    by_contra hn
    exact h.2.2 _ (firstPositiveHitTime_pos p hit x.1 x.2)
      (lt_of_le_of_ne hle hn) (firstPositiveHitTime_hits p hit x.1 x.2)
  apply Subtype.ext
  change (p ^ firstPositiveHitTime p hit x.1 x.2) x.1 = y.1
  rw [heq]
  exact h.2.1

theorem nextHit_apply_of_step (p : Perm D) (hit : D → Prop)
    (x : {d // hit d}) (h : hit (p x.1)) :
    (nextHitPerm p hit x).1 = p x.1 := by
  have := nextHit_eq_of_returnArc p hit x ⟨p x.1, h⟩
    (n := 1) ⟨by omega, by simp, by intro i hi hil; omega⟩
  exact congrArg Subtype.val this

/-- Compressing an orbit arc at a larger marked set preserves its first
small marked endpoint and the absence of earlier small marked points. -/
theorem returnArc_nextHit (p : Perm D) (small big : D → Prop)
    (hsub : ∀ d, small d → big d) :
    ∀ n (x y : {d // big d}), small y.1 → ReturnArc p small x.1 y.1 n →
      ∃ j, ReturnArc (nextHitPerm p big) (fun d => small d.1) x y j := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hy hn
    let t := firstPositiveHitTime p big x.1 x.2
    have ht : 0 < t := firstPositiveHitTime_pos p big x.1 x.2
    have htn : t ≤ n := firstPositiveHitTime_le_of_hit p big x.1 x.2
      hn.1 (hn.2.1 ▸ hsub _ hy)
    let z := nextHitPerm p big x
    have hz : z.1 = (p ^ t) x.1 := rfl
    by_cases heq : t = n
    · refine ⟨1, by omega, ?_, ?_⟩
      · apply Subtype.ext
        change z.1 = y.1
        rw [hz, heq]
        exact hn.2.1
      · intro i hi hil; omega
    · have hlt : t < n := lt_of_le_of_ne htn heq
      have hpow (i : ℕ) : (p ^ i) z.1 = (p ^ (i + t)) x.1 := by
        rw [hz, ← Perm.mul_apply, ← pow_add]
      have hrem : ReturnArc p small z.1 y.1 (n - t) := by
        refine ⟨by omega, ?_, ?_⟩
        · rw [hpow, Nat.sub_add_cancel htn]; exact hn.2.1
        · intro i hi hil
          rw [hpow]
          exact hn.2.2 (i + t) (by omega) (by omega)
      obtain ⟨j, hj⟩ := ih (n - t) (by omega) z y hy hrem
      refine ⟨j + 1, by omega, ?_, ?_⟩
      · rw [pow_succ, Perm.mul_apply]
        exact hj.2.1
      · intro i hi hil
        by_cases hi1 : i = 1
        · subst i
          simpa only [pow_one, ← hz, z] using hn.2.2 t ht hlt
        · have hi' : 0 < i - 1 := by omega
          have he : i = (i - 1) + 1 := by omega
          rw [he, pow_succ, Perm.mul_apply]
          exact hj.2.2 (i - 1) hi' (by omega)

/-- The literal equivalence between a small marked set and the same points
viewed as marks inside a larger marked set. -/
def nestedMarks (small big : D → Prop) (hsub : ∀ d, small d → big d) :
    {d // small d} ≃ {d : {d // big d} // small d.1} where
  toFun d := ⟨⟨d.1, hsub d.1 d.2⟩, d.2⟩
  invFun d := ⟨d.1.1, d.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- First-return restriction is transitive, with literal point identities. -/
theorem nextHit_nested (p : Perm D) (small big : D → Prop)
    (hsub : ∀ d, small d → big d) :
    nextHitPerm (nextHitPerm p big) (fun d => small d.1) =
      (nestedMarks small big hsub).permCongr (nextHitPerm p small) := by
  apply Equiv.ext
  intro x
  let x' : {d // small d} := ⟨x.1.1, x.2⟩
  let y := nextHitPerm p small x'
  let n := firstPositiveHitTime p small x'.1 x'.2
  have h : ReturnArc p small x'.1 y.1 n :=
    ⟨firstPositiveHitTime_pos p small x'.1 x'.2, rfl,
      fun _ hi hil => not_hit_before_firstPositiveHitTime p small x'.1 x'.2 hi hil⟩
  obtain ⟨j, hj⟩ := returnArc_nextHit p small big hsub n x.1
    ⟨y.1, hsub _ y.2⟩ y.2 h
  exact nextHit_eq_of_returnArc _ _ x ((nestedMarks small big hsub) y) hj

/-- Two permutations cannot differ at exactly one point. -/
theorem perm_eq_of_eq_except {A : Type*} (p q : Perm A) (e : A)
    (h : ∀ x, x ≠ e → p x = q x) : p = q := by
  apply Equiv.ext
  intro x
  by_cases hx : x = e
  · subst x
    let y := q.symm (p e)
    by_cases hy : y = e
    · simpa only [y, hy] using (q.apply_symm_apply (p e)).symm
    · have hpy : p y = p e := (h y hy).trans (q.apply_symm_apply (p e))
      exact False.elim (hy (p.injective hpy))
  · exact h x hx

/-- A change at at most one point of an invariant region can only insert an
excursion outside it. First return erases that excursion exactly. -/
theorem nextHit_eq_of_invariant_except (p q : Perm D) (keep : D → Prop)
    (hp : ∀ d, keep d → keep (p d)) (e : D)
    (heq : ∀ d, keep d → d ≠ e → q d = p d) :
    nextHitPerm q keep = nextHitPerm p keep := by
  have he (d : {d // keep d}) (hd : d.1 ≠ e) :
      nextHitPerm q keep d = nextHitPerm p keep d := by
    apply Subtype.ext
    rw [nextHit_apply_of_step p keep d (hp _ d.2),
      nextHit_apply_of_step q keep d (by rw [heq _ d.2 hd]; exact hp _ d.2),
      heq _ d.2 hd]
  by_cases hk : keep e
  · apply perm_eq_of_eq_except _ _ ⟨e, hk⟩
    intro d hd
    exact he d (fun h => hd (Subtype.ext h))
  · apply Equiv.ext
    intro d
    exact he d (fun h => hk (h ▸ d.2))

/-- Equality of first-return order on a larger interface descends to any
subset, without introducing a new coordinate permutation. -/
theorem nextHit_eq_of_nested (p q : Perm D) (small big : D → Prop)
    (hsub : ∀ d, small d → big d)
    (h : nextHitPerm p big = nextHitPerm q big) :
    nextHitPerm p small = nextHitPerm q small := by
  have he := congrArg (fun r : Perm {d // big d} =>
    nextHitPerm r (fun d => small d.1)) h
  rw [nextHit_nested p small big hsub, nextHit_nested q small big hsub] at he
  exact (nestedMarks small big hsub).permCongr.injective he

/-- A swap joining an invariant region to its exterior does not reorder
any marked subset of that region. -/
theorem nextHit_swap_mul_of_invariant (p : Perm D) (hit keep : D → Prop)
    (hp : ∀ d, keep d → keep (p d)) (hsub : ∀ d, hit d → keep d)
    (a b : D) (hab : ¬ (keep a ∧ keep b)) :
    nextHitPerm (swap a b * p) hit = nextHitPerm p hit := by
  classical
  apply nextHit_eq_of_nested _ _ hit keep hsub
  by_cases ha : keep a
  · apply nextHit_eq_of_invariant_except p _ keep hp (p.symm a)
    intro d hd hde
    have hda : p d ≠ a := by
      intro he; apply hde; exact p.injective (he.trans (p.apply_symm_apply a).symm)
    have hdb : p d ≠ b := fun he => hab ⟨ha, he ▸ hp d hd⟩
    simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hda hdb]
  · apply nextHit_eq_of_invariant_except p _ keep hp (p.symm b)
    intro d hd hde
    have hda : p d ≠ a := fun he => ha (he ▸ hp d hd)
    have hdb : p d ≠ b := by
      intro he; apply hde; exact p.injective (he.trans (p.apply_symm_apply b).symm)
    simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hda hdb]

/-- Merging a marked cycle with another cycle inserts only an unmarked
excursion. The induced marked order is unchanged. -/
theorem nextHit_swap_mul_of_not_sameCycle (p : Perm D) (hit : D → Prop)
    (a b : D) (hab : ¬ p.SameCycle a b)
    (hmarks : ∀ x y, hit x → hit y → p.SameCycle x y) :
    nextHitPerm (swap a b * p) hit = nextHitPerm p hit := by
  classical
  by_cases hex : ∃ r, hit r
  · obtain ⟨r, hr⟩ := hex
    let keep := p.SameCycle r
    have hp (d : D) (hd : keep d) : keep (p d) := hd.trans ⟨1, by simp⟩
    have hsub (d : D) (hd : hit d) : keep d := hmarks r d hr hd
    apply nextHit_eq_of_nested _ _ hit keep hsub
    by_cases ha : keep a
    · apply nextHit_eq_of_invariant_except p _ keep hp (p.symm a)
      intro d hd hde
      have hda : p d ≠ a := by
        intro he; apply hde; exact p.injective (he.trans (p.apply_symm_apply a).symm)
      have hdb : p d ≠ b := by
        intro he; apply hab; exact ha.symm.trans (he ▸ hp d hd)
      simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hda hdb]
    · apply nextHit_eq_of_invariant_except p _ keep hp (p.symm b)
      intro d hd hde
      have hda : p d ≠ a := fun he => ha (he ▸ hp d hd)
      have hdb : p d ≠ b := by
        intro he; apply hde; exact p.injective (he.trans (p.apply_symm_apply b).symm)
      simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hda hdb]
  · apply Equiv.ext
    intro x
    exact False.elim (hex ⟨x.1, x.2⟩)

/-- A transposition cannot change the cyclic order of marks that occupy
one cycle both before and after the surgery. -/
theorem nextHit_swap_mul_of_one_cycle (p : Perm D) (hit : D → Prop)
    (a b : D)
    (hbefore : ∀ x y, hit x → hit y → p.SameCycle x y)
    (hafter : ∀ x y, hit x → hit y → (swap a b * p).SameCycle x y) :
    nextHitPerm (swap a b * p) hit = nextHitPerm p hit := by
  classical
  by_cases heq : a = b
  · subst b
    rw [swap_self]
    change nextHitPerm (1 * p) hit = nextHitPerm p hit
    rw [one_mul]
  by_cases hab : p.SameCycle a b
  · let q := swap a b * p
    have hnot : ¬ q.SameCycle a b := not_swap_mul_sameCycle_of_sameCycle heq hab
    have h := nextHit_swap_mul_of_not_sameCycle q hit a b hnot hafter
    have hc : swap a b * q = p := by simp [q, ← mul_assoc]
    rw [hc] at h
    exact h.symm
  · exact nextHit_swap_mul_of_not_sameCycle p hit a b hab hbefore

omit [Fintype D] [DecidableEq D] in
/-- Powers commute with an embedding that intertwines permutation steps. -/
theorem pow_map {A : Type*} (p : Perm A) (q : Perm D) (f : A → D)
    (hstep : ∀ a, q (f a) = f (p a)) (n : ℕ) (a : A) :
    (q ^ n) (f a) = f ((p ^ n) a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, hstep, pow_succ', Perm.mul_apply]

/-- First return commutes with a literal embedding of an invariant carrier.
No arbitrary relabelling of the boundary is introduced. -/
theorem nextHit_map {A : Type*} [Fintype A] [DecidableEq A] (p : Perm A) (q : Perm D)
    (f : A → D) (hstep : ∀ a, q (f a) = f (p a))
    (small : A → Prop) (hit : D → Prop) (hhit : ∀ a, hit (f a) ↔ small a)
    (x : {a // small a}) :
    (nextHitPerm q hit ⟨f x.1, (hhit x.1).mpr x.2⟩).1 =
      f (nextHitPerm p small x).1 := by
  let y := nextHitPerm p small x
  let n := firstPositiveHitTime p small x.1 x.2
  have hy : (p ^ n) x.1 = y.1 := rfl
  have harc : ReturnArc q hit (f x.1) (f y.1) n := by
    refine ⟨firstPositiveHitTime_pos p small x.1 x.2, ?_, ?_⟩
    · rw [pow_map p q f hstep, hy]
    · intro i hi hil hh
      rw [pow_map p q f hstep] at hh
      exact not_hit_before_firstPositiveHitTime p small x.1 x.2 hi hil
        ((hhit _).mp hh)
  exact congrArg Subtype.val (nextHit_eq_of_returnArc q hit
    ⟨f x.1, (hhit x.1).mpr x.2⟩ ⟨f y.1, (hhit y.1).mpr y.2⟩ harc)

end
end Mettapedia.GraphTheory.FourColor.PermutationFirstReturnRestriction
