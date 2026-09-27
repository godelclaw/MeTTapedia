import Mettapedia.GraphTheory.FourColor.OddCycleCapConstruction
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Logic.Equiv.Fintype

/-!
# Boundary words for single-vertex frontier changes

The invariant needed for width changes is coverage of all nonconstant,
nonzero, zero-sum words. On an odd boundary the nonconstancy condition is
automatic. Contracting two unequal neighbours is the colour operation at
a merging cubic vertex; expansion is its inverse.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundaryWordFrontier

open ZigzagRing
open scoped BigOperators

def Admissible {k : Nat} (w : Fin k → Color) : Prop :=
  (∀ i, w i ≠ 0) ∧ (∑ i, w i) = 0

def Nonconstant {k : Nat} (w : Fin k → Color) : Prop :=
  ∃ i j, w i ≠ w j

def Required {k : Nat} (w : Fin k → Color) : Prop := Admissible w ∧ Nonconstant w

theorem Admissible.comp_perm {k : Nat} {w : Fin k → Color}
    (hw : Admissible w) (p : Equiv.Perm (Fin k)) : Admissible (w ∘ p) := by
  refine ⟨fun i => hw.1 _, ?_⟩
  exact (Equiv.sum_comp p w).trans hw.2

theorem Required.comp_perm {k : Nat} {w : Fin k → Color}
    (hw : Required w) (p : Equiv.Perm (Fin k)) : Required (w ∘ p) := by
  obtain ⟨i, j, hij⟩ := hw.2
  exact ⟨hw.1.comp_perm p, p.symm i, p.symm j, by simpa using hij⟩

theorem colourCount_comp_perm (k : Nat) (w : Fin k → Color)
    (p : Equiv.Perm (Fin k)) (c : Color) :
    colourCount k (w ∘ p) c = colourCount k w c :=
  Equiv.sum_comp p (fun i => if w i = c then 1 else 0)

theorem nonconstant_of_full {k : Nat} {w : Fin k → Color} (hw : Full k w) :
    Nonconstant w := by
  obtain ⟨i, hi⟩ := hw.2 red red_ne_zero
  obtain ⟨j, hj⟩ := hw.2 blue blue_ne_zero
  exact ⟨i, j, by rw [hi, hj]; exact red_ne_blue⟩

theorem required_of_odd {k : Nat} (hk : Odd k) {w : Fin k → Color}
    (hw : Admissible w) : Required w :=
  ⟨hw, nonconstant_of_full (CycleCap.full_of_oddCounts k w hw.1
    (CycleCap.oddCounts_of_sum_eq_zero k hk w hw.1 hw.2))⟩

/-- Collapse the first two ports, preserving every remaining port in order. -/
def contract (n : Nat) (y : Fin (n + 2) → Color) : Fin (n + 1) → Color :=
  Fin.cons (y 0 + y 1) (fun i => y i.succ.succ)

/-- Replace the first port by the ordered pair `a,b`. -/
def expand (n : Nat) (x : Fin (n + 1) → Color) (a b : Color) : Fin (n + 2) → Color :=
  Fin.cons a (Fin.cons b (fun i => x i.succ))

theorem contract_expand (n : Nat) (x : Fin (n + 1) → Color)
    (a b : Color) (hab : a + b = x 0) : contract n (expand n x a b) = x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [contract, expand, hab]

theorem expand_contract (n : Nat) (y : Fin (n + 2) → Color) :
    expand n (contract n y) (y 0) (y 1) = y := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [expand]
  · refine Fin.cases ?_ (fun j => ?_) j <;> simp [contract, expand]

theorem contract_admissible {n : Nat} {y : Fin (n + 2) → Color}
    (hy : Admissible y) (hne : y 0 ≠ y 1) : Admissible (contract n y) := by
  refine ⟨?_, ?_⟩
  · intro i
    refine Fin.cases (add_ne_zero_of_ne hne) (fun j => hy.1 j.succ.succ) i
  · have hsum := hy.2
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hsum
    simpa [contract, Fin.sum_univ_succ, add_assoc] using hsum

theorem expand_required {n : Nat} {x : Fin (n + 1) → Color}
    (hx : Admissible x) {a b : Color} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) (hsum : a + b = x 0) : Required (expand n x a b) := by
  refine ⟨⟨?_, ?_⟩, ⟨0, 1, ?_⟩⟩
  · intro i
    refine Fin.cases ha (fun j => ?_) i
    exact Fin.cases hb (fun j => hx.1 j.succ) j
  · have h := hx.2
    rw [Fin.sum_univ_succ] at h
    simpa [expand, Fin.sum_univ_succ, ← add_assoc, hsum] using h
  · simpa [expand] using hab

/-- Every admissible smaller word has a nonconstant admissible expansion. -/
theorem exists_required_expansion {n : Nat} (x : Fin (n + 1) → Color)
    (hx : Admissible x) :
    ∃ y : Fin (n + 2) → Color, Required y ∧ y 0 ≠ y 1 ∧ contract n y = x := by
  have hpair : ∀ c : Color, c ≠ 0 →
      ∃ a b : Color, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ a + b = c := by
    decide +kernel
  obtain ⟨a, b, ha, hb, hab, hs⟩ := hpair (x 0) (hx.1 0)
  exact ⟨expand n x a b, expand_required hx ha hb hab hs,
    by simpa [expand] using hab, contract_expand n x a b hs⟩

private theorem nonzero_colour_card : Fintype.card {c : Color // c ≠ 0} = 3 := by
  decide +kernel

/-- A full word of length at least four can be rearranged so that its first
two letters differ and contracting them still leaves two distinct colours.
The repeated colour is kept at the third port. -/
theorem full_contract_seed {n : Nat} (hn : 2 ≤ n) (w : Fin (n + 2) → Color)
    (hw : Admissible w) (hfull : Full (n + 2) w) :
    ∃ p : Equiv.Perm (Fin (n + 2)),
      (w ∘ p) 0 ≠ (w ∘ p) 1 ∧ Required (contract n (w ∘ p)) := by
  let : NeZero n := ⟨by omega⟩
  let f : Fin (n + 2) → {c : Color // c ≠ 0} := fun i => ⟨w i, hw.1 i⟩
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f
    (by rw [nonzero_colour_card, Fintype.card_fin]; omega)
  have hwj : w j = w i := (congrArg Subtype.val heq).symm
  obtain ⟨s, t, hst⟩ := nonconstant_of_full hfull
  have hother : ∃ l, w l ≠ w i := by
    by_cases hs : w s = w i
    · exact ⟨t, fun ht => hst (hs.trans ht.symm)⟩
    · exact ⟨s, hs⟩
  obtain ⟨l, hl⟩ := hother
  have hil : i ≠ l := fun h => hl (congrArg w h.symm)
  have hlj : l ≠ j := fun h => hl ((congrArg w h).trans hwj)
  let source : Fin 3 → Fin (n + 2) := fun t => ⟨t.val, by have := t.isLt; omega⟩
  let target : Fin 3 → Fin (n + 2) := ![i, l, j]
  have hs : Function.Injective source := by
    intro a b h
    exact Fin.ext (congrArg (fun t : Fin (n + 2) => t.val) h)
  have ht : Function.Injective target := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [target]
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair source target hs ht
  have hp0 : p 0 = i := hp 0
  have hp1 : p 1 = l := hp 1
  have hp2 : p (0 : Fin n).succ.succ = j := hp 2
  have hne : (w ∘ p) 0 ≠ (w ∘ p) 1 := by simpa [hp0, hp1] using hl.symm
  refine ⟨p, hne, contract_admissible (hw.comp_perm p) hne, ?_⟩
  refine ⟨0, (0 : Fin n).succ, ?_⟩
  change w (p 0) + w (p 1) ≠ w (p (0 : Fin n).succ.succ)
  rw [hp0, hp1, hp2, hwj]
  exact add_ne_left_of_ne_zero (hw.1 l)

end Mettapedia.GraphTheory.FourColor.BoundaryWordFrontier
