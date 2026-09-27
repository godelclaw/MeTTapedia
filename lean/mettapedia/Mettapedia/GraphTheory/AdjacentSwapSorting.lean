import Mettapedia.GSLT.Core.Ultrainfinite
import Mathlib.GroupTheory.Perm.Fin

/-!
# Quadratic adjacent-swap programs for finite words

Every permutation of a word of length `n` has a program of at most
`n * (n - 1)` adjacent swaps. The program retains its individual swaps
as a GSLT route and works over any alphabet. The bound comes from
placing the first position and recursively permuting the tail.
-/

namespace Mettapedia.GraphTheory.AdjacentSwapSorting

open Mettapedia.GSLT.Ultrainfinite

variable {α : Type*} {n : Nat}

/-- One swap of consecutive positions in the linear order. -/
structure Step (x y : Fin n → α) where
  left : Fin n
  right : Fin n
  adjacent : left.val + 1 = right.val
  result : y = x ∘ Equiv.swap left right

private def single (x : Fin n → α) (i j : Fin n) (h : i.val + 1 = j.val) :
    Route Step x (x ∘ Equiv.swap i j) := .cons ⟨i, j, h, rfl⟩ (.refl _)

private def Step.prepend (a : α) {x y : Fin n → α} (step : Step x y) :
    Step (Fin.cons a x) (Fin.cons a y) := by
    rcases step with ⟨i, j, hij, rfl⟩
    refine ⟨i.succ, j.succ, by simpa using congrArg Nat.succ hij, ?_⟩
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [Function.comp_def, Equiv.swap_apply_def, (Fin.succ_ne_zero i).symm,
        (Fin.succ_ne_zero j).symm]
    · by_cases hi : k = i <;> by_cases hj : k = j <;>
        simp_all [Function.comp_def, Equiv.swap_apply_def, Fin.succ_inj]

/-- Fixing a new first symbol preserves every authored tail swap. -/
def prepend (a : α) {x y : Fin n → α} :
    Route Step x y → Route Step (Fin.cons a x) (Fin.cons a y)
  | .refl _ => .refl _
  | .cons step rest => .cons (step.prepend a) (prepend a rest)

@[simp] theorem prepend_length (a : α) {x y : Fin n → α} (r : Route Step x y) :
    (prepend a r).length = r.length := by
  induction r with
  | refl => rfl
  | cons step rest ih => simp [prepend, Route.length, ih]

/-- Moving a selected position to the front and restoring the intervening
positions costs at most twice its index. -/
theorem swap_zero_route (j : Fin (n + 1)) (x : Fin (n + 1) → α) :
    ∃ r : Route Step x (x ∘ Equiv.swap 0 j), r.length ≤ 2 * j.val := by
  induction j using Fin.induction generalizing x with
  | zero =>
    have heq : x ∘ Equiv.swap 0 0 = x := by simp
    rw [heq]
    exact ⟨.refl _, by simp [Route.length]⟩
  | succ j ih =>
    by_cases hj : j.val = 0
    · exact ⟨single x 0 j.succ (by simp [hj]), by simp [single, Route.length, hj]⟩
    · let s := Equiv.swap j.castSucc j.succ
      obtain ⟨middle, hmiddle⟩ := ih (x ∘ s)
      have hzero : (0 : Fin (n + 1)) ≠ j.castSucc := by
        intro h
        exact hj (congrArg Fin.val h).symm
      have heq : (x ∘ s ∘ Equiv.swap 0 j.castSucc) ∘ s = x ∘ Equiv.swap 0 j.succ := by
        have hp : s * Equiv.swap 0 j.castSucc * s = Equiv.swap 0 j.succ := by
          simpa only [s, Equiv.swap_comm j.succ 0] using
            Equiv.swap_mul_swap_mul_swap hzero (Fin.succ_ne_zero j).symm
        exact funext (fun k => congrArg (fun p : Equiv.Perm (Fin (n + 1)) => x (p k)) hp)
      rw [← heq]
      refine ⟨((single x j.castSucc j.succ rfl).append middle).append
        (single _ j.castSucc j.succ rfl), ?_⟩
      simp only [Route.length_append, single, Route.length]
      have := j.isLt
      simp only [Fin.val_castSucc, Fin.val_succ] at hmiddle ⊢
      omega

/-- A uniform quadratic program for every permutation and every alphabet.
No finiteness or equality decision procedure for the alphabet is needed. -/
theorem permutation_route (n : Nat) (p : Equiv.Perm (Fin n)) (x : Fin n → α) :
    ∃ r : Route Step x (x ∘ p), r.length ≤ n * (n - 1) := by
  induction n with
  | zero =>
    have heq : x ∘ p = x := by funext i; exact Fin.elim0 i
    rw [heq]
    exact ⟨.refl _, by simp [Route.length]⟩
  | succ n ih =>
    obtain ⟨⟨j, q⟩, rfl⟩ := Equiv.Perm.decomposeFin.symm.surjective p
    let w := x ∘ Equiv.swap 0 j
    have hstart := swap_zero_route j x
    change (∃ r : Route Step x w, r.length ≤ 2 * j.val) at hstart
    rw [← Fin.cons_self_tail w] at hstart
    obtain ⟨first, hfirst⟩ := hstart
    obtain ⟨tail, htail⟩ := ih q (Fin.tail w)
    have heq : Fin.cons (w 0) (Fin.tail w ∘ q) =
        x ∘ Equiv.Perm.decomposeFin.symm (j, q) := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [w, Function.comp_def]
      · simp [w, Function.comp_def, Fin.tail]
    rw [← heq]
    refine ⟨first.append (prepend (w 0) tail), ?_⟩
    rw [Route.length_append, prepend_length]
    have hj := j.isLt
    have hrec : n * (n - 1) + 2 * n = (n + 1) * n := by
      cases n with
      | zero => simp
      | succ n => simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm]; omega
    simp only [Nat.add_sub_cancel]
    omega

end Mettapedia.GraphTheory.AdjacentSwapSorting
