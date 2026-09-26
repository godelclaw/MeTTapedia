import Mettapedia.GraphTheory.FourColor.FrontierVertexCode

/-!
# A split followed by a neighbouring merge

Splitting the first port and merging the second fresh port with its old
neighbour restores every admissible boundary word from the nonconstant
admissible words. This holds at every width at least three, without rings.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundaryWordFrontier

open TubeSlab.VertexTransfer

/-- Merge input ports one and two; retain port zero and all later ports. -/
def neighbourMergeCode (n : Nat) : Code (n + 3) (n + 2) :=
  (![Sum.inl 1, Sum.inl 2, Sum.inr 1],
    Fin.cons (some 0) (Fin.cons none (fun i => some i.succ.succ.succ)))

theorem neighbourMergeCode_valid (n : Nat) :
    VertexCodePartition.Valid (neighbourMergeCode n) := by
  have h12 : (1 : Fin (n + 3)) ≠ 2 := by
    intro h
    have hv := congrArg Fin.val h
    change (1 : Nat) = 2 at hv
    omega
  have h20 : (2 : Fin (n + 3)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    change (2 : Nat) = 0 at hv
    omega
  have htail (j : Fin n) : j.succ.succ.succ ≠ (2 : Fin (n + 3)) := by
    intro h
    have hv := congrArg Fin.val h
    change j.val + 1 + 1 + 1 = 2 at hv
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [neighbourMergeCode]
  · intro j
    cases j using Fin.cases with
    | zero => simp [neighbourMergeCode, Fin.exists_fin_succ]
    | succ j =>
      cases j using Fin.cases with
      | zero => simp [neighbourMergeCode, Fin.exists_fin_succ]
      | succ j => simp [neighbourMergeCode, Fin.exists_fin_succ, Fin.succ_succ_ne_one, eq_comm]
  · intro i
    cases i using Fin.cases with
    | zero => simp [neighbourMergeCode, Fin.exists_fin_succ, Fin.forall_fin_succ, h20]
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        simp [neighbourMergeCode, Fin.exists_fin_succ, Fin.forall_fin_succ,
          Fin.succ_succ_ne_one]
      | succ i =>
        cases i using Fin.cases with
        | zero =>
          simp [neighbourMergeCode, Fin.exists_fin_succ, Fin.forall_fin_succ,
            h20, htail, eq_comm]
        | succ i =>
          simp [neighbourMergeCode, Fin.exists_fin_succ, Fin.forall_fin_succ,
            Fin.succ_succ_ne_one, htail, eq_comm]
  · intro j k i hj hk
    cases j using Fin.cases with
    | zero =>
      cases k using Fin.cases with
      | zero => rfl
      | succ k =>
        cases k using Fin.cases with
        | zero => simp [neighbourMergeCode] at hk
        | succ k =>
          simp only [neighbourMergeCode, Fin.cons_zero, Option.some.injEq] at hj
          simp only [neighbourMergeCode, Fin.cons_succ, Option.some.injEq] at hk
          have := hj.trans hk.symm
          exact False.elim ((Fin.succ_ne_zero _).symm this)
    | succ j =>
      cases j using Fin.cases with
      | zero => simp [neighbourMergeCode] at hj
      | succ j =>
        cases k using Fin.cases with
        | zero =>
          simp only [neighbourMergeCode, Fin.cons_zero, Option.some.injEq] at hk
          simp only [neighbourMergeCode, Fin.cons_succ, Option.some.injEq] at hj
          exact False.elim (Fin.succ_ne_zero _ (hj.trans hk.symm))
        | succ k =>
          cases k using Fin.cases with
          | zero => simp [neighbourMergeCode] at hk
          | succ k =>
            simp only [neighbourMergeCode, Fin.cons_succ, Option.some.injEq] at hj hk
            exact Fin.succ_inj.mp (hj.trans hk.symm)

def cellSource (n : Nat) (y : Fin (n + 2) → Color) (b : Color) : Fin (n + 2) → Color :=
  Fin.cons (y 0 + b) (Fin.cons (y 1 + b) (fun i => y i.succ.succ))

def cellMiddle (n : Nat) (y : Fin (n + 2) → Color) (b : Color) : Fin (n + 3) → Color :=
  Fin.cons (y 0) (Fin.cons b (Fin.cons (y 1 + b) (fun i => y i.succ.succ)))

/-- A local colour choice ensures that the predecessor is not constant,
including when the desired output is constant. -/
private theorem cell_colour_choice (a e t : Color) (ha : a ≠ 0)
    (he : e ≠ 0) (ht : t ≠ 0) :
    ∃ b : Color, b ≠ 0 ∧ a ≠ b ∧ e ≠ b ∧ (a + b ≠ e + b ∨ a + b ≠ t) := by
  revert ha he ht
  fin_cases a <;> fin_cases e <;> fin_cases t <;> decide +kernel

/-- Exact witnesses for both literal vertices of the cell. -/
theorem cell_covers_admissible (n : Nat) (hn : 1 ≤ n) (y : Fin (n + 2) → Color)
    (hy : Admissible y) :
    ∃ x z, Required x ∧ CodeAccepts (splitCode (n + 1)) x z ∧
      CodeAccepts (neighbourMergeCode n) z y := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨b, hb, hab, heb, hnc⟩ := cell_colour_choice (y 0) (y 1)
    (y (0 : Fin n).succ.succ) (hy.1 0) (hy.1 1) (hy.1 _)
  let x := cellSource n y b
  let z := cellMiddle n y b
  have hx0 : ∀ i, x i ≠ 0 :=
    Fin.cases (add_ne_zero_of_ne hab)
      (Fin.cases (add_ne_zero_of_ne heb) (fun i => hy.1 i.succ.succ))
  have hz0 : ∀ i, z i ≠ 0 := Fin.cases (hy.1 0)
    (Fin.cases hb (Fin.cases (add_ne_zero_of_ne heb) (fun i => hy.1 i.succ.succ)))
  have hx : Required x := by
    refine ⟨⟨hx0, ?_⟩, ?_⟩
    · have hp : (y 0 + b) + (y 1 + b) = y 0 + y 1 := by
        calc
          _ = (y 0 + y 1) + (b + b) := by abel
          _ = y 0 + y 1 := by rw [color_add_self, add_zero]
      have h := hy.2
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h
      simpa [x, cellSource, Fin.sum_univ_succ, ← add_assoc, hp] using h
    · rcases hnc with h | h
      · exact ⟨0, 1, h⟩
      · exact ⟨0, (0 : Fin n).succ.succ, h⟩
  refine ⟨x, z, hx, ?_, ?_⟩
  · exact (split_accepts_iff (n + 1) x z hz0).mpr ⟨hab, rfl⟩
  · refine ⟨hz0, hy.1, ?_, ?_⟩
    · have hs : (fun t => Sum.elim z y ((neighbourMergeCode n).1 t)) =
          (![b, y 1 + b, y 1] : Fin 3 → Color) := by
        funext t
        fin_cases t <;> rfl
      rw [hs]
      apply (colour_triple_injective_iff hb (add_ne_zero_of_ne heb) (hy.1 1)).mpr
      refine ⟨(add_ne_right_of_ne_zero (hy.1 1)).symm, ?_⟩
      have hbb := color_add_self b
      calc
        y 1 = y 1 + (b + b) := by rw [hbb, add_zero]
        _ = b + (y 1 + b) := by abel
    · intro j i hji
      cases j using Fin.cases with
      | zero =>
        simp only [neighbourMergeCode, Fin.cons_zero, Option.some.injEq] at hji
        subst i
        rfl
      | succ j =>
        cases j using Fin.cases with
        | zero => simp [neighbourMergeCode] at hji
        | succ j =>
          simp only [neighbourMergeCode, Fin.cons_succ, Option.some.injEq] at hji
          subst i
          rfl

end Mettapedia.GraphTheory.FourColor.BoundaryWordFrontier
