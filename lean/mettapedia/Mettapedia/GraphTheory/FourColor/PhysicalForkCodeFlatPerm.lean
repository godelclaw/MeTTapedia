import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitPartitionBridge

/-!
# Permutations stored as lists

A permutation `π` of a finite type `A` is stored in a list `p` of natural
numbers under a numbering `e` of `A` when `p` sends the number of each point to
the number of its image.  Three executable operations on stored permutations
agree with the semantic ones: iteration, the first return to a marked set
(searching at most as many steps as `A` has points), and the number of cycles,
computed as the number of points that are least on their own cycle.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

open Equiv Equiv.Perm
open GoertzelV24SeamFaceArc GoertzelV24OrderedCutFaceReturnProfile
open PhysicalForkCode

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The list `p` stores `π` under the numbering `e`. -/
def Stores (e : A → ℕ) (p : List ℕ) (π : Perm A) : Prop :=
  ∀ a, getN p (e a) = e (π a)

/-- Iterate a stored permutation `t` times. -/
def iterF (p : List ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | t + 1, x => iterF p t (getN p x)

omit [Fintype A] [DecidableEq A] in
theorem iterF_stores {e : A → ℕ} {p : List ℕ} {π : Perm A} (h : Stores e p π) (t : ℕ)
    (a : A) : iterF p t (e a) = e ((π ^ t) a) := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih => rw [iterF, h a, ih, pow_succ, Perm.mul_apply]

/-- The first return to the marked positions, searching at most `fuel` steps. -/
def firstRet (p : List ℕ) (kept : List Bool) : ℕ → ℕ → ℕ
  | 0, y => y
  | fuel + 1, y => if getB kept (getN p y) then getN p y else firstRet p kept fuel (getN p y)

/-- **The bounded search finds the first return.** -/
theorem firstRet_stores {e : A → ℕ} {p : List ℕ} {π : Perm A} (h : Stores e p π)
    {kept : List Bool} {hit : A → Prop} (hk : ∀ a, getB kept (e a) = true ↔ hit a)
    {fuel : ℕ} (hfuel : Fintype.card A ≤ fuel) (a : {a // hit a}) :
    firstRet p kept fuel (e a.1) = e (nextHitPerm π hit a).1 := by
  set T := firstPositiveHitTime π hit a.1 a.2 with hT
  have key : ∀ fuel s, s < T → T - s ≤ fuel →
      firstRet p kept fuel (e ((π ^ s) a.1)) = e ((π ^ T) a.1) := by
    intro fuel
    induction fuel with
    | zero => intro s hs hf; omega
    | succ fuel ih =>
        intro s hs hf
        have hz : getN p (e ((π ^ s) a.1)) = e ((π ^ (s + 1)) a.1) := by
          rw [h, pow_succ', Perm.mul_apply]
        simp only [firstRet, hz]
        by_cases hlast : s + 1 = T
        · have hhit : getB kept (e ((π ^ (s + 1)) a.1)) = true := by
            rw [hk, hlast]
            exact firstPositiveHitTime_hits π hit a.1 a.2
          rw [ite_eq_left hhit, hlast]
        · have hmiss : ¬ getB kept (e ((π ^ (s + 1)) a.1)) = true := by
            rw [hk]
            exact not_hit_before_firstPositiveHitTime π hit a.1 a.2 (by omega) (by omega)
          rw [ite_eq_right hmiss]
          exact ih (s + 1) (by omega) (by omega)
  have hle : T ≤ Fintype.card A :=
    (firstPositiveHitTime_le_sameCycle_card π hit a.1 a.2).trans (Finset.card_le_univ _)
  have := key fuel 0 (firstPositiveHitTime_pos π hit a.1 a.2) (by omega)
  rw [pow_zero, Perm.one_apply] at this
  exact this

/-! ## Counting cycles by their least points -/

/-- Whether `x` is least among its first `N` iterates. -/
def isMinF (p : List ℕ) (N x : ℕ) : Bool :=
  (List.range N).all fun t => decide (x ≤ iterF p t x)

/-- The number of cycles of a stored permutation of the numbers below `N`. -/
def cycF (p : List ℕ) (N : ℕ) : ℕ := ((List.range N).filter (isMinF p N)).length

theorem cyc_eq_card_least (π : Perm A) (e : A → ℕ) (he : Function.Injective e) :
    cyc π = (Finset.univ.filter fun a => ∀ b, π.SameCycle a b → e a ≤ e b).card := by
  classical
  unfold cyc
  rw [← GoertzelV24FaceOrbitPartitionBridge.card_permOrbit_eq_card_partition_parts,
    ← Fintype.card_subtype]
  symm
  apply Fintype.card_congr
  refine Equiv.ofBijective (fun a => Quotient.mk (SameCycle.setoid π) a.1) ⟨?_, ?_⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hs : π.SameCycle a b := Quotient.exact hab
    exact Subtype.ext (he (le_antisymm (ha b hs) (hb a hs.symm)))
  · intro q
    induction q using Quotient.inductionOn with
    | h z =>
        obtain ⟨m, hm, hmin⟩ := (Finset.univ.filter fun b => π.SameCycle z b).exists_min_image e
          ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, SameCycle.refl π z⟩⟩
        have hzm : π.SameCycle z m := (Finset.mem_filter.mp hm).2
        refine ⟨⟨m, fun b hb => hmin b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          hzm.trans hb⟩)⟩, ?_⟩
        exact Quotient.sound hzm.symm

theorem exists_pow_lt_card {π : Perm A} {a b : A} (h : π.SameCycle a b) :
    ∃ t < Fintype.card A, (π ^ t) a = b := by
  by_cases ha : a ∈ π.support
  · obtain ⟨t, ht, hab⟩ := h.exists_pow_eq_of_mem_support ha
    exact ⟨t, ht.trans_le (Finset.card_le_univ _), hab⟩
  · have hfix : π a = a := by simpa using ha
    refine ⟨0, Fintype.card_pos_iff.mpr ⟨a⟩, ?_⟩
    rw [pow_zero, Perm.one_apply]
    exact h.eq_of_left hfix

omit [DecidableEq A] in
theorem length_filter_range {N : ℕ} {e : A → ℕ} (he : Function.Injective e)
    (hrange : ∀ x, x < N ↔ ∃ a, e a = x) (P : ℕ → Bool) :
    ((List.range N).filter P).length = (Finset.univ.filter fun a => P (e a) = true).card := by
  rw [← Finset.card_image_of_injective _ he,
    ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  congr 1
  ext x
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hx, hP⟩
    obtain ⟨a, rfl⟩ := (hrange x).mp hx
    exact ⟨a, hP, rfl⟩
  · rintro ⟨a, hP, rfl⟩
    exact ⟨(hrange _).mpr ⟨a, rfl⟩, hP⟩

omit [DecidableEq A] in
theorem card_eq_of_range {N : ℕ} {e : A → ℕ} (he : Function.Injective e)
    (hrange : ∀ x, x < N ↔ ∃ a, e a = x) : Fintype.card A = N := by
  have := length_filter_range he hrange (fun _ => true)
  rw [List.filter_true, List.length_range] at this
  rw [this]
  simp

/-- **The flat cycle count is the number of cycles.** -/
theorem cycF_stores {N : ℕ} {e : A → ℕ} {p : List ℕ} {π : Perm A}
    (he : Function.Injective e) (hrange : ∀ x, x < N ↔ ∃ a, e a = x) (h : Stores e p π) :
    cycF p N = cyc π := by
  have hcard := card_eq_of_range he hrange
  rw [cyc_eq_card_least π e he, cycF, length_filter_range he hrange]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, isMinF, List.all_eq_true,
    List.mem_range, decide_eq_true_eq]
  constructor
  · intro hmin b hab
    obtain ⟨t, ht, rfl⟩ := exists_pow_lt_card hab
    have := hmin t (hcard ▸ ht)
    rwa [iterF_stores h] at this
  · intro hmin t _
    rw [iterF_stores h]
    exact hmin _ ((sameCycle_pow_right).mpr (SameCycle.refl π a))

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
