import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mettapedia.GraphTheory.FourColor.GoertzelV24PermutationOrbitSurgery

/-!
# Computable cycle counting for permutations of a finite type

`orbitList σ x` lists the iterates of `x` under `σ` up to the carrier size; it contains
exactly the points on the cycle of `x` (`mem_orbitList_iff`).  With an injective index,
`cycleCount idx σ` counts the points that are least on their cycle, which is the number of
cycles (`cycleCount_eq_orbitCount`).  Both are plain list and finset computations, so the
kernel can decide statements about the cycles of a concrete permutation.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace PermCycleCount

open Equiv
open GoertzelV24PermutationOrbitSurgery

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- `n`-fold application, by recursion. -/
def iter (σ : Perm D) : Nat → D → D
  | 0, x => x
  | n + 1, x => σ (iter σ n x)

omit [Fintype D] [DecidableEq D] in
theorem iter_eq_pow (σ : Perm D) (n : Nat) (x : D) : iter σ n x = (σ ^ n) x := by
  induction n with
  | zero => simp [iter]
  | succ n ih => rw [iter, ih, pow_succ', Perm.mul_apply]

omit [DecidableEq D] in
/-- Every point has a positive period at most the carrier size. -/
theorem exists_period (σ : Perm D) (x : D) :
    ∃ p, 0 < p ∧ p ≤ Fintype.card D ∧ (σ ^ p) x = x := by
  obtain ⟨a, b, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun n : Fin (Fintype.card D + 1) => (σ ^ (n : Nat)) x) (by simp)
  have hval : (a : Nat) ≠ b := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hval with h | h
  · refine ⟨b - a, by omega, by omega, ?_⟩
    have hb : (b : Nat) = a + (b - a) := by omega
    have : (σ ^ (a : Nat)) ((σ ^ ((b : Nat) - a)) x) = (σ ^ (a : Nat)) x := by
      rw [← Perm.mul_apply, ← pow_add, ← hb]
      exact heq.symm
    exact (σ ^ (a : Nat)).injective this
  · refine ⟨a - b, by omega, by omega, ?_⟩
    have ha : (a : Nat) = b + (a - b) := by omega
    have : (σ ^ (b : Nat)) ((σ ^ ((a : Nat) - b)) x) = (σ ^ (b : Nat)) x := by
      rw [← Perm.mul_apply, ← pow_add, ← ha]
      exact heq
    exact (σ ^ (b : Nat)).injective this

omit [Fintype D] [DecidableEq D] in
theorem pow_mul_period (σ : Perm D) (x : D) {p : Nat} (hp : (σ ^ p) x = x) (q : Nat) :
    (σ ^ (p * q)) x = x := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, pow_add, Perm.mul_apply, hp, ih]

omit [Fintype D] [DecidableEq D] in
theorem pow_mod_period (σ : Perm D) (x : D) {p : Nat} (hp : (σ ^ p) x = x) (n : Nat) :
    (σ ^ n) x = (σ ^ (n % p)) x := by
  conv_lhs => rw [← Nat.mod_add_div n p, pow_add, Perm.mul_apply, pow_mul_period σ x hp]

/-- The iterates of `x`, up to the carrier size. -/
def orbitList (σ : Perm D) (x : D) : List D :=
  (List.range (Fintype.card D)).map fun n => iter σ n x

omit [DecidableEq D] in
theorem mem_orbitList_iff (σ : Perm D) (x y : D) : y ∈ orbitList σ x ↔ σ.SameCycle x y := by
  constructor
  · intro h
    simp only [orbitList, List.mem_map, List.mem_range] at h
    obtain ⟨n, -, rfl⟩ := h
    rw [iter_eq_pow]
    exact ⟨n, by simp⟩
  · intro h
    obtain ⟨i, -, rfl⟩ := h.exists_pow_eq'
    obtain ⟨p, hp0, hpcard, hp⟩ := exists_period σ x
    simp only [orbitList, List.mem_map, List.mem_range]
    refine ⟨i % p, lt_of_lt_of_le (Nat.mod_lt _ hp0) hpcard, ?_⟩
    rw [iter_eq_pow, ← pow_mod_period σ x hp]

omit [DecidableEq D] in
theorem self_mem_orbitList (σ : Perm D) (x : D) : x ∈ orbitList σ x :=
  (mem_orbitList_iff σ x x).2 (Perm.SameCycle.refl σ x)

/-- `x` is least on its cycle for the index `idx`. -/
def isMin (idx : D → Nat) (σ : Perm D) (x : D) : Bool :=
  (orbitList σ x).all fun y => decide (idx x ≤ idx y)

omit [DecidableEq D] in
theorem isMin_iff (idx : D → Nat) (σ : Perm D) (x : D) :
    isMin idx σ x = true ↔ ∀ y, σ.SameCycle x y → idx x ≤ idx y := by
  simp [isMin, List.all_eq_true, mem_orbitList_iff]

/-- The number of cycle minima. -/
def cycleCount (idx : D → Nat) (σ : Perm D) : Nat :=
  (Finset.univ.filter fun x => isMin idx σ x = true).card

/-- **Cycle minima count the cycles.** -/
theorem cycleCount_eq_orbitCount (idx : D → Nat) (hidx : Function.Injective idx)
    (σ : Perm D) : cycleCount idx σ = orbitCount σ := by
  have h1 : cycleCount idx σ = Fintype.card {x // isMin idx σ x = true} :=
    (Fintype.card_subtype _).symm
  rw [h1]
  unfold orbitCount
  refine Fintype.card_eq.mpr ⟨Equiv.ofBijective
    (fun x => (Quotient.mk (Perm.SameCycle.setoid σ) x.1)) ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx⟩ ⟨x', hx'⟩ h
    have hsc : σ.SameCycle x x' := Quotient.exact h
    have h1 := (isMin_iff idx σ x).1 hx x' hsc
    have h2 := (isMin_iff idx σ x').1 hx' x hsc.symm
    exact Subtype.ext (hidx (le_antisymm h1 h2))
  · intro q
    induction q using Quotient.inductionOn with
    | h z =>
      obtain ⟨x, hxmem, hxmin⟩ := (orbitList σ z).toFinset.exists_min_image idx
        ⟨z, by simpa using self_mem_orbitList σ z⟩
      rw [List.mem_toFinset, mem_orbitList_iff] at hxmem
      refine ⟨⟨x, ?_⟩, Quotient.sound hxmem.symm⟩
      rw [isMin_iff]
      intro y hy
      apply hxmin
      rw [List.mem_toFinset, mem_orbitList_iff]
      exact hxmem.trans hy

end PermCycleCount
end Mettapedia.GraphTheory.FourColor
