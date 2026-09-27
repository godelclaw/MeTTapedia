import Mettapedia.GraphTheory.AdjacentSwapSorting
import Mettapedia.GraphTheory.FourColor.ZigzagRingErgodicity

/-!
# Quadratic mixing time for full-colour zigzag tubes

An explicit adjacent-swap program replaces the bound obtained from the
number of word states. Every full three-colour count class mixes after
`2 * (k * (k - 1))` physical rings, for every circumference at least three.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagRing

open GoertzelV24CorridorPumping Mettapedia.GSLT.Ultrainfinite

variable (k : Nat) [NeZero k]

/-- Linear adjacent swaps are among the allowed cyclic word moves. -/
theorem sorting_route_transfer {x y : Fin k → Color}
    (route : Route AdjacentSwapSorting.Step x y) :
    ExactRelationalTransfer (Move k) route.length x y := by
  induction route with
  | refl => exact .zero _
  | cons step rest ih =>
    have hs : step.left + 1 = step.right := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_one']
      have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by
        have := step.adjacent
        have := step.right.isLt
        omega)
      rw [h1, step.adjacent, Nat.mod_eq_of_lt step.right.isLt]
    apply ExactRelationalTransfer.succ ?_ ih
    refine Or.inr ⟨step.left, ?_⟩
    rw [swapAt_eq_comp_swap, hs]
    exact step.result

private theorem idle_sorting (n : Nat) (x : Fin k → Color) :
    ExactRelationalTransfer (Move k) n x x := by
  induction n with
  | zero => exact .zero _
  | succ n ih => exact .succ (Or.inl rfl) ih

/-- The finite word state space is unnecessary: at most `k * (k - 1)`
adjacent swaps suffice, followed by idle moves to the requested length. -/
theorem moves_after_quadratic_bound (x y : Fin k → Color)
    (hc : ∀ c, colourCount k x c = colourCount k y c)
    (n : Nat) (hn : k * (k - 1) ≤ n) :
    ExactRelationalTransfer (Move k) n x y := by
  obtain ⟨p, rfl⟩ := exists_perm_of_counts k x y hc
  obtain ⟨route, hroute⟩ := AdjacentSwapSorting.permutation_route k p x
  have h := (sorting_route_transfer k route).comp
    (idle_sorting k (n - route.length) (x ∘ p))
  simpa only [Nat.add_sub_of_le (hroute.trans hn)] using h

/-- Every sufficiently long physical tube mixes a full three-colour
count class, with a quadratic bound independent of its multiplicities. -/
theorem full_transfer_after_quadratic_bound (hk : 3 ≤ k) (x y : Fin k → Color)
    (hx : Full k x) (hc : ∀ c, colourCount k x c = colourCount k y c)
    (r : Nat) (hr : 2 * (k * (k - 1)) ≤ r) :
    ExactRelationalTransfer (Step k) r x y := by
  have heven : ∀ x y : Fin k → Color, Full k x →
      (∀ c, colourCount k x c = colourCount k y c) →
      ∀ n, k * (k - 1) ≤ n → ExactRelationalTransfer (Step k) (2 * n) x y := by
    intro x y hx hc n hn
    let z := (shiftEquiv k ^ n).symm y
    have hcz : ∀ c, colourCount k x c = colourCount k z c := by
      intro c
      have hs := colourCount_shiftEquiv_pow k n z c
      have hcancel : (shiftEquiv k ^ n) z = y := Equiv.apply_symm_apply _ _
      rw [hcancel] at hs
      exact (hc c).trans hs
    have hm := moves_after_quadratic_bound k x z hcz n hn
    simpa only [z, Equiv.apply_symm_apply] using transfer_of_movePath k hk hm hx
  by_cases hpar : r % 2 = 0
  · have hlen : 2 * (r / 2) = r := by omega
    simpa only [hlen] using heven x y hx hc (r / 2) (by omega)
  · have hlen : 1 + 2 * (r / 2) = r := by omega
    obtain ⟨z, hz⟩ := hx.exists_step k hk
    have hzcount : ∀ c, colourCount k z c = colourCount k y c :=
      fun c => (hz.colourCount k c).trans (hc c)
    have ht := heven z y (hz.full_target k hx) hzcount (r / 2) (by omega)
    have hs : ExactRelationalTransfer (Step k) 1 x z := .succ hz (.zero _)
    simpa only [hlen] using hs.comp ht

end Mettapedia.GraphTheory.FourColor.ZigzagRing
