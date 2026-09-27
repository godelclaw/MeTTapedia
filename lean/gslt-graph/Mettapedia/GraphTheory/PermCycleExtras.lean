import Mathlib.GroupTheory.Perm.Cycle.Basic

open scoped BigOperators

namespace Mettapedia.GraphTheory

namespace EquivPermSameCycle

open Equiv

theorem step_right {α : Type*} (σ : Perm α) (x : α) :
    σ.SameCycle x (σ x) := by
  refine ⟨(1 : ℤ), ?_⟩
  simp [zpow_one]

theorem step_right_inv {α : Type*} (σ : Perm α) (x : α) :
    σ.SameCycle x (σ.symm x) := by
  refine ⟨(-1 : ℤ), ?_⟩
  simp [Equiv.Perm.inv_def]

/-- Mathlib's `Equiv.Perm.sameCycle_apply_right`, re-exported under the name
this development uses. -/
theorem sameCycle_apply_right {α : Type*} (σ : Perm α) {a b : α} :
    σ.SameCycle a (σ b) ↔ σ.SameCycle a b :=
  Equiv.Perm.sameCycle_apply_right

/-- Mathlib's `Equiv.Perm.sameCycle_symm_apply_right`, re-exported.  Mathlib
also keeps `sameCycle_inv_apply_right` as a *deprecated* alias of that lemma,
so prefer the `symm` name in new code. -/
theorem sameCycle_inv_apply_right {α : Type*} (σ : Perm α) {a b : α} :
    σ.SameCycle a (σ.symm b) ↔ σ.SameCycle a b :=
  Equiv.Perm.sameCycle_symm_apply_right

/-- The finite set of points in the same cycle as `x`.

This is deliberately **not** `(σ.cycleOf x).support`: the two differ at a fixed
point, where the cycle support is empty but the same-cycle set is `{x}`.  Do
not "simplify" one into the other. -/
noncomputable def sameCycleFinset {α : Type*} [Fintype α] (σ : Perm α) (x : α) :
    Finset α := by
  classical
  exact Finset.univ.filter fun y => σ.SameCycle x y

theorem apply_mem_sameCycleFinset {α : Type*} [Fintype α] {σ : Perm α} {x y : α}
    (hy : y ∈ sameCycleFinset σ x) :
    σ y ∈ sameCycleFinset σ x := by
  classical
  simp only [sameCycleFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  exact (sameCycle_apply_right σ).2 hy

theorem symm_apply_mem_sameCycleFinset {α : Type*} [Fintype α] {σ : Perm α} {x y : α}
    (hy : y ∈ sameCycleFinset σ x) :
    σ.symm y ∈ sameCycleFinset σ x := by
  classical
  simp only [sameCycleFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  exact (sameCycle_inv_apply_right σ).2 hy

theorem sum_comp_apply_sameCycleFinset {α β : Type*} [Fintype α] [AddCommMonoid β]
    (σ : Perm α) (x : α) (g : α → β) :
    ∑ y ∈ sameCycleFinset σ x, g (σ y) = ∑ y ∈ sameCycleFinset σ x, g y := by
  classical
  refine Finset.sum_bij
    (fun y _hy => σ y)
    (fun _y hy => apply_mem_sameCycleFinset hy)
    (fun _a _ha _b _hb h => σ.injective h)
    ?surj
    (fun _y _hy => rfl)
  intro y hy
  refine ⟨σ.symm y, symm_apply_mem_sameCycleFinset hy, by simp⟩

end EquivPermSameCycle

end Mettapedia.GraphTheory
