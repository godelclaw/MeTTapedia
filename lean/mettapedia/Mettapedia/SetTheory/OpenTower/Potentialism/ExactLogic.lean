import Mettapedia.SetTheory.OpenTower.Potentialism.Filtration
import Mettapedia.SetTheory.OpenTower.Potentialism.Transfer
import Mathlib.Data.Fin.Basic

/-!
# The formulas valid on the closed sets

Under cofinally many inaccessibles, a formula is valid on the closed sets of one
level exactly when it is valid on every nonempty finite reflexive transitive total
preorder. If the only closed sets are the empty set and the level at ω, the same
statement is the validity theorem of the two-point chain.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.Potentialism

open Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
open Mettapedia.SetTheory.CarveOuts
open Mettapedia.SetTheory.OpenTower.InternalTower
open Mettapedia.SetTheory.OpenTower.Strength.StageFamilies
open scoped ZFSet
open Classical

universe u

theorem fin2_one_ne_zero : (1 : Fin 2) ≠ 0 := by
  intro h
  exact absurd (congrArg Fin.val h) Nat.zero_ne_one.symm

theorem fin2_not_one_le_zero : ¬ (1 : Fin 2) ≤ 0 := by
  intro h
  have : (1 : ℕ) ≤ 0 := (Fin.le_iff_val_le_val).mp h
  omega

/-- **Under cofinal inaccessibles, validity on the closed sets is validity on the finite total
preorders.** -/
theorem valid_closed_iff_valid_finite_total (h : CofinalInaccessibles.{u}) (φ : Formula) :
    Valid (fun (A B : {U : ZFSet.{u} // Closed U}) => A.1 ⊆ B.1) φ ↔
      ∀ (W : Type) (R : W → W → Prop),
        Finite W → Nonempty W → (∀ w, R w w) →
          (∀ a b c, R a b → R b c → R a c) → (∀ a b, R a b ∨ R b a) → Valid R φ := by
  constructor
  · intro hvalid W R hfin hinhab hrefl htrans htotal
    exact valid_finite_total_of_valid_closed h hvalid R hfin hinhab hrefl htrans htotal
  · intro hall
    by_contra hfail
    obtain ⟨W, R, hfin, hinhab, hrefl, htrans, htotal, hnot⟩ :=
      not_valid_finite_total_of_not_valid_closed hfail
    exact hnot (hall W R hfin hinhab hrefl htrans htotal)

/-! ## The two-point chain, with no cofinality hypothesis -/

/-- The empty closed set is sent to the bottom of the two-point chain, and every other closed set
to the top. -/
noncomputable def toTwo (A : {U : ZFSet.{u} // Closed U}) : Fin 2 :=
  if A.1 = (∅ : ZFSet.{u}) then 0 else 1

/-- The bottom of the two-point chain is the empty set, and the top is the level at ω. -/
noncomputable def fromTwo (i : Fin 2) : {U : ZFSet.{u} // Closed U} :=
  if i = 0 then ⟨∅, closed_empty⟩ else ⟨V_ Ordinal.omega0, vonNeumann_omega_closed⟩

theorem vonNeumann_omega_ne_empty : (V_ Ordinal.omega0 : ZFSet.{u}) ≠ ∅ := by
  intro h
  have hmem : (∅ : ZFSet.{u}) ∈ V_ Ordinal.omega0 := empty_mem_vonNeumann_omega
  rw [h] at hmem
  exact ZFSet.notMem_empty (∅ : ZFSet.{u}) hmem

theorem toTwo_eq_zero_iff (A : {U : ZFSet.{u} // Closed U}) : toTwo A = 0 ↔ A.1 = ∅ := by
  by_cases h : A.1 = (∅ : ZFSet.{u})
  · rw [toTwo, if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [toTwo, if_neg h]
    exact ⟨fun h1 => absurd h1 fin2_one_ne_zero, fun he => absurd he h⟩

theorem toTwo_eq_one_of_ne {A : {U : ZFSet.{u} // Closed U}} (h : A.1 ≠ ∅) : toTwo A = 1 := by
  rw [toTwo, if_neg h]

theorem fromTwo_zero : fromTwo (0 : Fin 2) = ⟨∅, closed_empty⟩ := by
  rw [fromTwo, if_pos rfl]

theorem fromTwo_one : fromTwo (1 : Fin 2) = ⟨V_ Ordinal.omega0, vonNeumann_omega_closed⟩ := by
  rw [fromTwo, if_neg fin2_one_ne_zero]

/-- The empty set is the bottom of the two-point chain. -/
example : toTwo ⟨∅, closed_empty⟩ = 0 := (toTwo_eq_zero_iff _).mpr rfl

/-- The level at ω is not the bottom of the two-point chain. -/
example : toTwo ⟨V_ Ordinal.omega0, vonNeumann_omega_closed⟩ ≠ 0 := by
  rw [toTwo_eq_one_of_ne vonNeumann_omega_ne_empty]
  exact fin2_one_ne_zero

/-- The bottom of the chain is the empty set. -/
example : (fromTwo (0 : Fin 2)).1 = (∅ : ZFSet.{u}) := by
  rw [fromTwo_zero]

/-- The top of the chain is not the empty set. -/
example : (fromTwo (1 : Fin 2)).1 ≠ (∅ : ZFSet.{u}) := by
  rw [fromTwo_one]
  exact vonNeumann_omega_ne_empty

theorem fin2_eq_one_of_ne_zero {i : Fin 2} (hi : i ≠ 0) : i = 1 := by
  have hlt : i.1 < 2 := i.isLt
  have hne : i.1 ≠ 0 := by
    intro h
    exact hi (Fin.ext h)
  have hv : i.1 = 1 := by omega
  exact Fin.ext hv

theorem toTwo_surj (w : Fin 2) : ∃ A : {U : ZFSet.{u} // Closed U}, toTwo A = w := by
  by_cases hw : w = 0
  · exact ⟨⟨∅, closed_empty⟩, by rw [hw, (toTwo_eq_zero_iff _).mpr rfl]⟩
  · have hw1 : w = 1 := fin2_eq_one_of_ne_zero hw
    exact ⟨⟨V_ Ordinal.omega0, vonNeumann_omega_closed⟩,
      by rw [hw1, toTwo_eq_one_of_ne vonNeumann_omega_ne_empty]⟩

theorem toTwo_forth {A B : {U : ZFSet.{u} // Closed U}} (hAB : A.1 ⊆ B.1) : toTwo A ≤ toTwo B := by
  by_cases hA : A.1 = ∅
  · rw [(toTwo_eq_zero_iff A).mpr hA]
    exact Fin.zero_le _
  · have hB : B.1 ≠ ∅ := by
      intro hB
      apply hA
      rw [ZFSet.eq_empty]
      intro y hy
      have hyB : y ∈ B.1 := hAB hy
      rw [hB] at hyB
      exact ZFSet.notMem_empty y hyB
    rw [toTwo_eq_one_of_ne hA, toTwo_eq_one_of_ne hB]

theorem toTwo_back {A : {U : ZFSet.{u} // Closed U}} {w : Fin 2} (hw : toTwo A ≤ w) :
    ∃ B : {U : ZFSet.{u} // Closed U}, A.1 ⊆ B.1 ∧ toTwo B = w := by
  by_cases hw0 : w = 0
  · subst hw0
    exact ⟨A, fun _ hx => hx, le_antisymm hw (Fin.zero_le _)⟩
  · have hw1 : w = 1 := fin2_eq_one_of_ne_zero hw0
    by_cases hA : A.1 = ∅
    · refine ⟨⟨V_ Ordinal.omega0, vonNeumann_omega_closed⟩, ?_, ?_⟩
      · rw [hA]
        exact ZFSet.empty_subset _
      · rw [hw1, toTwo_eq_one_of_ne vonNeumann_omega_ne_empty]
    · refine ⟨A, fun _ hx => hx, by rw [hw1, toTwo_eq_one_of_ne hA]⟩

theorem fromTwo_forth {i j : Fin 2} (hij : i ≤ j) : (fromTwo i).1 ⊆ (fromTwo j).1 := by
  by_cases hi : i = 0
  · rw [hi, fromTwo_zero]
    exact ZFSet.empty_subset _
  · have hi1 : i = 1 := fin2_eq_one_of_ne_zero hi
    by_cases hj : j = 0
    · rw [hi1, hj] at hij
      exact absurd hij fin2_not_one_le_zero
    · rw [fin2_eq_one_of_ne_zero hj, fromTwo_one, hi1, fromTwo_one]

theorem fromTwo_back (honly : ∀ U : ZFSet.{u}, Closed U → U = ∅ ∨ U = V_ Ordinal.omega0)
    (i : Fin 2) (A : {U : ZFSet.{u} // Closed U}) (hsub : (fromTwo i).1 ⊆ A.1) :
    ∃ j, i ≤ j ∧ fromTwo j = A := by
  rcases honly A.1 A.2 with hA | hA
  · have hi : i = 0 := by
      by_cases hi0 : i = 0
      · exact hi0
      · exfalso
        rw [fin2_eq_one_of_ne_zero hi0, fromTwo_one] at hsub
        have hmem : (∅ : ZFSet.{u}) ∈ A.1 := hsub empty_mem_vonNeumann_omega
        rw [hA] at hmem
        exact ZFSet.notMem_empty _ hmem
    refine ⟨0, ?_, ?_⟩
    · rw [hi]
    · exact Subtype.ext (by rw [fromTwo_zero]; exact hA.symm)
  · refine ⟨1, ?_, ?_⟩
    · rw [Fin.le_iff_val_le_val]
      have := i.isLt
      omega
    · exact Subtype.ext (by rw [fromTwo_one]; exact hA.symm)

theorem fromTwo_surj (honly : ∀ U : ZFSet.{u}, Closed U → U = ∅ ∨ U = V_ Ordinal.omega0)
    (A : {U : ZFSet.{u} // Closed U}) : ∃ i, fromTwo i = A := by
  rcases honly A.1 A.2 with hA | hA
  · exact ⟨0, Subtype.ext (by rw [fromTwo_zero]; exact hA.symm)⟩
  · exact ⟨1, Subtype.ext (by rw [fromTwo_one]; exact hA.symm)⟩

theorem valid_fin2_of_valid_closed {φ : Formula}
    (hvalid : Valid (fun (A B : {U : ZFSet.{u} // Closed U}) => A.1 ⊆ B.1) φ) :
    Valid (fun (i j : Fin 2) => i ≤ j) φ :=
  valid_of_surjective_bounded toTwo toTwo_surj (fun _ _ h => toTwo_forth h)
    (fun _ _ h => toTwo_back h) hvalid

theorem valid_closed_of_valid_fin2
    (honly : ∀ U : ZFSet.{u}, Closed U → U = ∅ ∨ U = V_ Ordinal.omega0) {φ : Formula}
    (hvalid : Valid (fun (i j : Fin 2) => i ≤ j) φ) :
    Valid (fun (A B : {U : ZFSet.{u} // Closed U}) => A.1 ⊆ B.1) φ :=
  valid_of_surjective_bounded fromTwo (fromTwo_surj honly) (fun _ _ h => fromTwo_forth h)
    (fun i A h => fromTwo_back honly i A h) hvalid

/-- **If the only closed sets are `∅` and the level at ω, their logic is the two-point chain.** -/
theorem valid_closed_iff_valid_fin2
    (honly : ∀ U : ZFSet.{u}, Closed U → U = ∅ ∨ U = V_ Ordinal.omega0) (φ : Formula) :
    Valid (fun (A B : {U : ZFSet.{u} // Closed U}) => A.1 ⊆ B.1) φ ↔
      Valid (fun (i j : Fin 2) => i ≤ j) φ :=
  ⟨fun h => valid_fin2_of_valid_closed h, fun h => valid_closed_of_valid_fin2 honly h⟩

end Mettapedia.SetTheory.OpenTower.Potentialism
