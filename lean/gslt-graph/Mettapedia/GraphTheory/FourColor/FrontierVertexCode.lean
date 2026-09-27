import Mettapedia.GraphTheory.FourColor.BoundaryWordFrontier
import Mettapedia.GraphTheory.FourColor.VertexCodeRealization

/-!
# Literal cubic vertices that split and merge frontier ports

The first boundary coordinate is the chosen split port. A merge consumes
the first two coordinates. Every remaining port persists in its old cyclic
order. The finite codes construct real vertices through `attach`.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundaryWordFrontier

open TubeSlab.VertexTransfer VertexCodePartition VertexCodeRealization

def splitCode (n : Nat) : Code (n + 1) (n + 2) :=
  (![Sum.inr 0, Sum.inr 1, Sum.inl 0],
    Fin.cons none (Fin.cons none (fun i => some i.succ)))

def mergeCode (n : Nat) : Code (n + 2) (n + 1) :=
  (![Sum.inl 0, Sum.inl 1, Sum.inr 0],
    Fin.cons none (fun i => some i.succ.succ))

theorem splitCode_valid (n : Nat) : VertexCodePartition.Valid (splitCode n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [splitCode]
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [splitCode, Fin.exists_fin_succ]
    · refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [splitCode, Fin.exists_fin_succ, Fin.succ_succ_ne_one, eq_comm]
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [splitCode, Fin.exists_fin_succ, Fin.forall_fin_succ]
    · simp [splitCode, Fin.exists_fin_succ, Fin.forall_fin_succ, eq_comm]
  · intro j l i hj hl
    cases j using Fin.cases with
    | zero => simp [splitCode] at hj
    | succ j =>
      cases j using Fin.cases with
      | zero => simp [splitCode] at hj
      | succ j =>
        cases l using Fin.cases with
        | zero => simp [splitCode] at hl
        | succ l =>
          cases l using Fin.cases with
          | zero => simp [splitCode] at hl
          | succ l =>
            simp only [splitCode, Fin.cons_succ, Option.some.injEq] at hj hl
            exact congrArg Fin.succ (hj.trans hl.symm)

theorem mergeCode_valid (n : Nat) : VertexCodePartition.Valid (mergeCode n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [mergeCode]
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [mergeCode, Fin.exists_fin_succ, eq_comm]
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [mergeCode, Fin.exists_fin_succ, Fin.forall_fin_succ]
    · refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [mergeCode, Fin.exists_fin_succ, Fin.forall_fin_succ,
          Fin.succ_succ_ne_one, eq_comm]
  · intro j l i hj hl
    cases j using Fin.cases with
    | zero => simp [mergeCode] at hj
    | succ j =>
      cases l using Fin.cases with
      | zero => simp [mergeCode] at hl
      | succ l =>
        simp only [mergeCode, Fin.cons_succ, Option.some.injEq] at hj hl
        exact Fin.succ_inj.mp (hj.trans hl.symm)

theorem colour_triple_injective_iff {a b c : Color} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Function.Injective (![a, b, c] : Fin 3 → Color) ↔ a ≠ b ∧ c = a + b := by
  constructor
  · intro h
    have hab : a ≠ b := h.ne (by decide : (0 : Fin 3) ≠ 1)
    have hac : a ≠ c := h.ne (by decide : (0 : Fin 3) ≠ 2)
    have hbc : b ≠ c := h.ne (by decide : (1 : Fin 3) ≠ 2)
    exact ⟨hab, ZigzagRing.third_eq_add ha hb hc hab hac hbc⟩
  · rintro ⟨hab, rfl⟩ i j hij
    have hac : a ≠ a + b := (add_ne_left_of_ne_zero hb).symm
    have hbc : b ≠ a + b := (add_ne_right_of_ne_zero ha).symm
    fin_cases i <;> fin_cases j <;> simp_all

private theorem split_star (n : Nat) (x : Fin (n + 1) → Color) (y : Fin (n + 2) → Color) :
    (fun t => Sum.elim x y ((splitCode n).1 t)) = ![y 0, y 1, x 0] := by
  funext t
  fin_cases t <;> rfl

private theorem merge_star (n : Nat) (y : Fin (n + 2) → Color) (x : Fin (n + 1) → Color) :
    (fun t => Sum.elim y x ((mergeCode n).1 t)) = ![y 0, y 1, x 0] := by
  funext t
  fin_cases t <;> rfl

private theorem contract_nonzero {n : Nat} {y : Fin (n + 2) → Color}
    (hy : ∀ i, y i ≠ 0) (hne : y 0 ≠ y 1) : ∀ i, contract n y i ≠ 0 :=
  Fin.cases (add_ne_zero_of_ne hne) (fun j => hy j.succ.succ)

/-- Exact split relation: the fresh colours differ, sum to the consumed
colour, and every retained boundary colour agrees. -/
theorem split_accepts_iff (n : Nat) (x : Fin (n + 1) → Color) (y : Fin (n + 2) → Color)
    (hy : ∀ i, y i ≠ 0) :
    CodeAccepts (splitCode n) x y ↔ y 0 ≠ y 1 ∧ contract n y = x := by
  constructor
  · intro h
    have ht := h.2.2.1
    rw [split_star] at ht
    obtain ⟨hne, hsum⟩ := (colour_triple_injective_iff (hy 0) (hy 1) (h.1 0)).mp ht
    refine ⟨hne, ?_⟩
    funext i
    refine Fin.cases hsum.symm (fun j => ?_) i
    exact (h.2.2.2 j.succ.succ j.succ rfl).symm
  · rintro ⟨hne, heq⟩
    have hx : ∀ i, x i ≠ 0 := heq ▸ contract_nonzero hy hne
    refine ⟨hx, hy, ?_, ?_⟩
    · rw [split_star]
      exact (colour_triple_injective_iff (hy 0) (hy 1) (hx 0)).mpr
        ⟨hne, (congrFun heq 0).symm⟩
    · intro j i hj
      cases j using Fin.cases with
      | zero => simp [splitCode] at hj
      | succ j =>
        cases j using Fin.cases with
        | zero => simp [splitCode] at hj
        | succ j =>
          simp only [splitCode, Fin.cons_succ, Option.some.injEq] at hj
          subst i
          exact (congrFun heq j.succ).symm

/-- The merge is the converse relation on nonzero words. -/
theorem merge_accepts_iff (n : Nat) (y : Fin (n + 2) → Color) (x : Fin (n + 1) → Color)
    (hy : ∀ i, y i ≠ 0) :
    CodeAccepts (mergeCode n) y x ↔ y 0 ≠ y 1 ∧ contract n y = x := by
  constructor
  · intro h
    have ht := h.2.2.1
    rw [merge_star] at ht
    obtain ⟨hne, hsum⟩ := (colour_triple_injective_iff (hy 0) (hy 1) (h.2.1 0)).mp ht
    refine ⟨hne, ?_⟩
    funext i
    refine Fin.cases hsum.symm (fun j => ?_) i
    exact h.2.2.2 j.succ j.succ.succ rfl
  · rintro ⟨hne, heq⟩
    have hx : ∀ i, x i ≠ 0 := heq ▸ contract_nonzero hy hne
    refine ⟨hy, hx, ?_, ?_⟩
    · rw [merge_star]
      exact (colour_triple_injective_iff (hy 0) (hy 1) (hx 0)).mpr
        ⟨hne, (congrFun heq 0).symm⟩
    · intro j i hj
      cases j using Fin.cases with
      | zero => simp [mergeCode] at hj
      | succ j =>
        simp only [mergeCode, Fin.cons_succ, Option.some.injEq] at hj
        subst i
        exact congrFun heq j.succ

end Mettapedia.GraphTheory.FourColor.BoundaryWordFrontier
