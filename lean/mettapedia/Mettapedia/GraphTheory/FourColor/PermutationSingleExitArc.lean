import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

/-!
# One exit from a finite permutation orbit determines an ordered arc

A subset of one permutation orbit with exactly one outgoing transition is
a contiguous, nonrepeating segment of that orbit. A cardinal version detects
this condition when adjoining all successors adds exactly one point.

The construction chooses a point with maximal first-hit distance to the
unique exit. This recovers the order as actual permutation powers, rather
than merely proving connectedness of an auxiliary graph.
-/

namespace Mettapedia.GraphTheory.FourColor.PermutationSingleExitArc

open Equiv Equiv.Perm

noncomputable section

variable {D : Type*} [DecidableEq D]
variable (p : Perm D) (A : Finset D)

def exits : Finset D := A.filter fun d => p d ∉ A

/-- A literal interval of successive permutation applications. -/
structure Arc where
  first : D
  length : ℕ
  positive : 0 < length
  exact : A = (Finset.range length).image (fun i => (p ^ i) first)
  injective : Function.Injective (fun i : Fin length => (p ^ i.val) first)
  after_outside : (p ^ length) first ∉ A

variable {p A}

theorem Arc.mem (a : Arc p A) {i : ℕ} (hi : i < a.length) : (p ^ i) a.first ∈ A := by
  apply (congrArg (fun B : Finset D => (p ^ i) a.first ∈ B) a.exact).mpr
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

theorem Arc.first_mem (a : Arc p A) : a.first ∈ A := by
  simpa using a.mem a.positive

theorem Arc.length_eq_card (a : Arc p A) : a.length = A.card := by
  have hi : Set.InjOn (fun i => (p ^ i) a.first) (Finset.range a.length) := by
    intro i hi j hj hij
    exact congrArg Fin.val (a.injective (show
      (p ^ (⟨i, Finset.mem_range.mp hi⟩ : Fin a.length).val) a.first =
        (p ^ (⟨j, Finset.mem_range.mp hj⟩ : Fin a.length).val) a.first from hij))
  have hc := congrArg Finset.card a.exact
  rw [Finset.card_image_of_injOn hi, Finset.card_range] at hc
  exact hc.symm

theorem Arc.before_outside (a : Arc p A) : p.symm a.first ∉ A := by
  intro h
  have hm := (congrArg (fun B : Finset D => p.symm a.first ∈ B) a.exact).mp h
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
  have hil := Finset.mem_range.mp hi
  have hs : (p ^ (i + 1)) a.first = a.first := by
    rw [pow_succ', Perm.mul_apply, he, p.apply_symm_apply]
  by_cases hlast : i + 1 = a.length
  · exact a.after_outside (by rw [← hlast, hs]; exact a.first_mem)
  · have hlt : i + 1 < a.length := by omega
    have hh := a.injective (show
      (p ^ (⟨i + 1, hlt⟩ : Fin a.length).val) a.first =
        (p ^ (⟨0, a.positive⟩ : Fin a.length).val) a.first by simpa using hs)
    have := congrArg Fin.val hh
    simp only at this
    omega

theorem Arc.last_mem (a : Arc p A) : (p ^ (a.length - 1)) a.first ∈ A :=
  a.mem (by have := a.positive; omega)

theorem Arc.last_next (a : Arc p A) :
    p ((p ^ (a.length - 1)) a.first) = (p ^ a.length) a.first := by
  rw [← Perm.mul_apply, ← pow_succ']
  congr 2
  have := a.positive
  omega

/-- The arc's first point is the only entry from its complement. -/
theorem Arc.entry_eq_first (a : Arc p A) {x : D} (hx : x ∈ A) (hb : p.symm x ∉ A) :
    x = a.first := by
  have him := (congrArg (fun B : Finset D => x ∈ B) a.exact).mp hx
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp him
  have hil := Finset.mem_range.mp hi
  by_cases hz : i = 0
  · simpa [hz] using hix.symm
  · have hs : p ((p ^ (i - 1)) a.first) = x := by
      rw [← Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel (by omega)]
      exact hix
    exfalso
    apply hb
    rw [← hs, p.symm_apply_apply]
    exact a.mem (by omega)

/-- The arc's last point is the only exit to its complement. -/
theorem Arc.exit_eq_last (a : Arc p A) {x : D} (hx : x ∈ A) (hn : p x ∉ A) :
    x = (p ^ (a.length - 1)) a.first := by
  have him := (congrArg (fun B : Finset D => x ∈ B) a.exact).mp hx
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp him
  have hil := Finset.mem_range.mp hi
  have hiend : i + 1 = a.length := by
    by_contra hne
    have hlt : i + 1 < a.length := by omega
    apply hn
    rw [← hix, ← Perm.mul_apply, ← pow_succ']
    exact a.mem hlt
  have heq : i = a.length - 1 := by omega
  simpa only [heq] using hix.symm

variable (p A)

/-- The successor-union count measures the number of exits. -/
theorem exits_card_of_union_card (hcard : (A ∪ A.image p).card = A.card + 1) :
    (exits p A).card = 1 := by
  classical
  have hi : (exits p A).image p = A.image p \ A := by
    ext y
    simp only [Finset.mem_image, exits, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨x, ⟨hx, hp⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hp⟩
    · rintro ⟨⟨x, hx, rfl⟩, hp⟩
      exact ⟨x, ⟨hx, hp⟩, rfl⟩
  have hci := Finset.card_image_of_injective (exits p A) p.injective
  rw [hi] at hci
  have hp := Finset.card_image_of_injective A p.injective
  have hu := Finset.card_union_add_card_inter A (A.image p)
  have hs := Finset.card_sdiff_add_card_inter (A.image p) A
  rw [Finset.inter_comm (A.image p) A] at hs
  omega

variable [Fintype D]

/-- A unique exit constructs the whole ordered arc, with no supplied start
point, order, or length. All selected points must belong to one orbit. -/
theorem exists_arc_of_unique_exit
    (hcycle : ∀ x ∈ A, ∀ y ∈ A, p.SameCycle x y)
    {b : D} (hb : b ∈ A) (hbout : p b ∉ A)
    (hexit : ∀ x ∈ A, p x ∉ A → x = b) : Nonempty (Arc p A) := by
  classical
  let dist (x : A) : ℕ := Nat.find (hcycle x.val x.property b hb).exists_nat_pow_eq
  have hit (x : A) : (p ^ dist x) x.val = b :=
    Nat.find_spec (hcycle x.val x.property b hb).exists_nat_pow_eq
  have minimal (x : A) {i : ℕ} (hi : i < dist x) : (p ^ i) x.val ≠ b :=
    Nat.find_min (hcycle x.val x.property b hb).exists_nat_pow_eq hi
  obtain ⟨a, _, hmax⟩ := (Finset.univ : Finset A).exists_max_image dist
    ⟨⟨b, hb⟩, Finset.mem_univ _⟩
  have hmax' (x : A) : dist x ≤ dist a := hmax x (Finset.mem_univ _)
  have hinside : ∀ i ≤ dist a, (p ^ i) a.val ∈ A := by
    intro i
    induction i with
    | zero => intro _; exact a.property
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      by_contra hn
      have heq := hexit ((p ^ i) a.val) hprev (by
        simpa only [pow_succ', Perm.mul_apply] using hn)
      exact minimal a (by omega) heq
  have heq : A = (Finset.range (dist a + 1)).image (fun i => (p ^ i) a.val) := by
    ext x
    constructor
    · intro hx
      let x' : A := ⟨x, hx⟩
      refine Finset.mem_image.mpr ⟨dist a - dist x', Finset.mem_range.mpr (by omega), ?_⟩
      apply (p ^ dist x').injective
      calc
        (p ^ dist x') ((p ^ (dist a - dist x')) a.val) = (p ^ dist a) a.val := by
          rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_of_le (hmax' x')]
        _ = b := hit a
        _ = (p ^ dist x') x := (hit x').symm
    · rintro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hinside i (by have := Finset.mem_range.mp hi; omega)
  have hneq {i j : ℕ} (hij : i < j) (hj : j ≤ dist a) :
      (p ^ i) a.val ≠ (p ^ j) a.val := by
    intro h
    have hh : (p ^ (dist a - j + i)) a.val = b := by
      calc
        _ = (p ^ (dist a - j)) ((p ^ i) a.val) := by rw [pow_add, Perm.mul_apply]
        _ = (p ^ (dist a - j)) ((p ^ j) a.val) := congrArg _ h
        _ = (p ^ dist a) a.val := by
          rw [← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hj]
        _ = b := hit a
    exact minimal a (by omega) hh
  refine ⟨⟨a.val, dist a + 1, by omega, heq, ?_, ?_⟩⟩
  · intro i j hij
    apply Fin.ext
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hlt
    · exact hneq hlt (by omega) hij
    · exact hneq hlt (by omega) hij.symm
  · rw [pow_succ', Perm.mul_apply, hit a]
    exact hbout

/-- A single extra successor point detects an ordered arc in one orbit. -/
theorem exists_arc_of_union_card
    (hcycle : ∀ x ∈ A, ∀ y ∈ A, p.SameCycle x y)
    (hcard : (A ∪ A.image p).card = A.card + 1) : Nonempty (Arc p A) := by
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (exits_card_of_union_card p A hcard)
  have hbe : b ∈ exits p A := by rw [hb]; simp
  obtain ⟨hba, hbo⟩ := Finset.mem_filter.mp hbe
  apply exists_arc_of_unique_exit p A hcycle hba hbo
  intro x hx hpx
  have hxe : x ∈ exits p A := Finset.mem_filter.mpr ⟨hx, hpx⟩
  simpa only [hb, Finset.mem_singleton] using hxe

end
end Mettapedia.GraphTheory.FourColor.PermutationSingleExitArc
