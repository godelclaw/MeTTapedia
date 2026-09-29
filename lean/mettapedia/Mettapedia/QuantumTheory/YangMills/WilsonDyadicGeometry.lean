import Mettapedia.QuantumTheory.YangMills.StrongCouplingCrossing

/-!
# Nested separators of a four-dimensional Wilson assembly

At mesh `s`, retain links lying in a coordinate face of the mesh: a transverse
coordinate is divisible by `s`. All other links are internal. Any internal
links in one plaquette have the same cell index. Thus distinct cells share
only retained links, and a plaquette cannot directly couple their interiors.
-/
set_option autoImplicit false
noncomputable section
open Finset
open scoped Classical
namespace Mettapedia.QuantumTheory.YangMills.WilsonDyadicGeometry
open StrongCouplingCrossing
variable {d n : ℕ}

/-- A positive link is retained precisely when it lies in a transverse mesh
face; the full link, including both endpoints, then lies in that face. -/
def Retained (s : ℕ) (l : Link d n) : Prop :=
  ∃ i : Fin d, i ≠ l.2 ∧ s ∣ (l.1 i).val

/-- Index of the cell containing the origin, in ordinary integer coordinates. -/
def cell (s : ℕ) (x : Site d n) : Fin d → ℕ := fun i => (x i).val / s

theorem retained_of_dvd {s t : ℕ} (hst : s ∣ t) (l : Link d n)
    (h : Retained t l) : Retained s l := by
  obtain ⟨i, hi, hd⟩ := h
  exact ⟨i, hi, hst.trans hd⟩

theorem coarse_retained_fine (l : Link d n) (h : Retained 4 l) : Retained 2 l :=
  retained_of_dvd (by decide : 2 ∣ 4) l h

/-- An internal shifted link cannot have crossed a mesh face or the periodic
seam, since the shifted transverse coordinate would then be divisible by `s`. -/
theorem div_val_add_one {s : ℕ} (x : ZMod (n + 3))
    (h : ¬s ∣ (x + 1).val) : (x + 1).val / s = x.val / s := by
  have hval : (x + 1).val = (x.val + 1) % (n + 3) := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod,
      Nat.mod_eq_of_lt (by omega : 1 < n + 3)]
  have hx := x.val_lt
  have hlt : x.val + 1 < n + 3 := by
    by_contra hnot
    have heq : x.val + 1 = n + 3 := by omega
    rw [hval, heq, Nat.mod_self] at h
    exact h (dvd_zero _)
  rw [hval, Nat.mod_eq_of_lt hlt] at h ⊢
  exact Nat.succ_div_of_not_dvd h

theorem cell_step_eq {s : ℕ} (x : Site d n) (μ : Fin d)
    (h : ¬s ∣ (x μ + 1).val) : cell s (x + step μ) = cell s x := by
  funext i
  by_cases hi : i = μ
  · subst i
    simpa [cell, step] using div_val_add_one (n := n) (s := s) (x μ) h
  · simp [cell, step, hi]

/-- Every internal boundary link of a plaquette belongs to its base cell.
This is the geometric separation needed for exact conditional factorization. -/
theorem internal_link_cell (s : ℕ) (p : Plaquette d n) (i : Fin 4)
    (h : ¬Retained s (linkAt p i)) : cell s (linkAt p i).1 = cell s p.1 := by
  fin_cases i
  · rfl
  · apply cell_step_eq
    intro hd
    apply h
    refine ⟨p.2.1.1, ne_of_lt p.2.2, ?_⟩
    simpa [linkAt, step] using hd
  · apply cell_step_eq
    intro hd
    apply h
    refine ⟨p.2.1.2, ne_of_gt p.2.2, ?_⟩
    simpa [linkAt, step] using hd
  · rfl

/-- Distinct cell interiors never meet the same elementary plaquette. -/
theorem internal_support_same_cell (s : ℕ) (p : Plaquette d n)
    {l k : Link d n} (hl : l ∈ support p) (hk : k ∈ support p)
    (hil : ¬Retained s l) (hik : ¬Retained s k) : cell s l.1 = cell s k.1 := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hl
  obtain ⟨j, _, rfl⟩ := mem_image.mp hk
  exact (internal_link_cell s p i hil).trans (internal_link_cell s p j hik).symm

#print axioms coarse_retained_fine
#print axioms internal_link_cell
#print axioms internal_support_same_cell
end Mettapedia.QuantumTheory.YangMills.WilsonDyadicGeometry
